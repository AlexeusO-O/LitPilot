
# -*- coding: utf-8 -*-
import csv, json, os, re, threading, time, tkinter as tk, webbrowser
from collections import Counter
from io import StringIO
from tkinter import ttk, filedialog, messagebox
import tkinter.simpledialog as simpledialog

import requests
from Bio import Entrez, Medline

APP_NAME = "LitPilot"
APP_VERSION = "v0.1"
APP_TITLE = f"{APP_NAME} {APP_VERSION}｜PubMed 文献筛选与分析工具"
SETTINGS_FILE = "litpilot_settings.json"
TEMPLATES_FILE = "litpilot_templates.json"

PUBMED_SORT_MAP = {
    "最佳匹配 Best Match": "relevance",
    "发布时间（新到旧）": "pub date",
    "发表时间（旧到新）": "pub+date+asc",
}
ARTICLE_TYPE_OPTIONS = [
    "Review","Meta-Analysis","Systematic Review","RCT","Cohort Study",
    "Case Report","Guideline","Animal/In Vitro","Basic Research",
]
ARTICLE_TYPE_PATTERNS = {
    "Systematic Review": [r"systematic review"],
    "Meta-Analysis": [r"meta-analysis", r"meta analysis"],
    "Review": [r"review"],
    "RCT": [r"randomized controlled trial", r"randomised controlled trial", r"clinical trial"],
    "Case Report": [r"case reports?", r"case series"],
    "Guideline": [r"guideline", r"consensus", r"recommendation"],
    "Cohort Study": [r"cohort"],
    "Animal/In Vitro": [r"animal", r"mice", r"mouse", r"rat", r"in vitro", r"cell line", r"organoid"],
    "Basic Research": [r"mechanism", r"pathway", r"signaling", r"transcript", r"molecular", r"epigenetic"],
}
BUILTIN_TEMPLATES = {
    "默认": {"builtin": True,"retmax": 50,"title_kw":"","abstract_kw":"","year_min":"","year_max":"","decision":"全部","highlight":"","core_keywords":"","target_types":[],"q_filter":"全部","nondup_only":False},
    "陌生领域快速入门": {"builtin": True,"retmax": 50,"title_kw":"","abstract_kw":"review OR systematic review OR meta-analysis OR guideline","year_min":"","year_max":"","decision":"全部","highlight":"review;systematic review;meta-analysis;guideline","core_keywords":"review, systematic review, meta-analysis, guideline","target_types":["Review","Meta-Analysis","Systematic Review","Guideline"],"q_filter":"全部","nondup_only":True},
    "综述优先": {"builtin": True,"retmax": 80,"title_kw":"","abstract_kw":"review OR systematic review OR meta-analysis","year_min":"","year_max":"","decision":"全部","highlight":"review;systematic review;meta-analysis","core_keywords":"review, systematic review, meta-analysis","target_types":["Review","Meta-Analysis","Systematic Review"],"q_filter":"全部","nondup_only":True},
    "近5年热点": {"builtin": True,"retmax": 100,"title_kw":"","abstract_kw":"","year_min":str(time.localtime().tm_year-5),"year_max":str(time.localtime().tm_year),"decision":"全部","highlight":"","core_keywords":"","target_types":[],"q_filter":"全部","nondup_only":True},
}
EXCLUSION_REASONS = ["非目标人群","非目标疾病","非目标干预","非原始研究","无摘要","动物/体外研究","与主题相关性低","重复文献"]
COLUMNS = ["PMID","Title","Authors","Journal","Year","DOI","Abstract","PublicationType","ArticleType","Language","PubMedURL","Decision","Reason","Notes","Tags","相关性评分","是否重复","Q区","影响因子","中科院分区"]
TREE_COLUMNS = ("筛选结果","PMID","发表时间","期刊","Q区","影响因子","中科院分区","文章类型","相关性评分","是否重复","标签","标题","排除理由")
COLUMN_TO_FIELD = {"筛选结果":"Decision","PMID":"PMID","发表时间":"Year","期刊":"Journal","Q区":"Q区","影响因子":"影响因子","中科院分区":"中科院分区","文章类型":"ArticleType","相关性评分":"相关性评分","是否重复":"是否重复","标签":"Tags","标题":"Title","排除理由":"Reason"}
DEFAULT_SHORTCUTS = {"保留":"r","排除":"e","待定":"t","循环切换":"space","打开PubMed":"Return"}
DEFAULT_GPT_TASK = """请帮我完成以下任务：
1. 按研究主题对这些文献分组
2. 区分综述、临床研究、基础研究
3. 指出每组最值得优先阅读的文献
4. 总结该领域目前的主要研究方向
5. 如果存在争议，请指出争议点"""

def normalize_query(q): return re.sub(r"\s+"," ",q.strip())
def split_pmids(text): return [x for x in re.split(r"[\s,;]+", text.strip()) if x]
def parse_doi(aid_list):
    if not aid_list: return ""
    for item in aid_list:
        s = str(item)
        if "[doi]" in s.lower(): return s.replace(" [doi]","").strip()
    return ""
def norm_text(s):
    s = (s or "").strip().lower()
    s = re.sub(r"\s+"," ",s)
    s = re.sub(r"[^a-z0-9\u4e00-\u9fff ]+","",s)
    return s
def normalize_journal(s): return re.sub(r"\s+"," ",(s or "").strip().lower())
def extract_year_num(text):
    m = re.search(r"(19|20)\d{2}", str(text or ""))
    return int(m.group(0)) if m else None
def to_float(v):
    try: return float(str(v).strip())
    except: return -1.0
def q_rank(v): return {"Q1":1,"Q2":2,"Q3":3,"Q4":4}.get(str(v or "").strip().upper(),99)
def cas_rank(v):
    m = re.search(r"([1-4])区", str(v or ""))
    return int(m.group(1)) if m else 99

def article_type_from_row(row):
    pt = (row.get("PublicationType","") or "").lower()
    title = (row.get("Title","") or "").lower()
    abstract = (row.get("Abstract","") or "").lower()
    text = " ".join([pt,title,abstract])
    hits = []
    for label, patterns in ARTICLE_TYPE_PATTERNS.items():
        for p in patterns:
            if re.search(p,text):
                hits.append(label); break
    if not hits and pt and "journal article" in pt: hits.append("Journal Article")
    return "; ".join(hits)

def score_row(row, core_keywords, target_types, recent_bonus_year=None):
    score = 0
    title = (row.get("Title","") or "").lower()
    abstract = (row.get("Abstract","") or "").lower()
    article_type = (row.get("ArticleType","") or "").lower()
    year = extract_year_num(row.get("Year",""))

    for kw in core_keywords:
        kw = kw.strip().lower()
        if not kw:
            continue
        if kw in title:
            score += 3
        if kw in abstract:
            score += 1

    for t in target_types:
        t = t.strip().lower()
        if t and t in article_type:
            score += 2

    if recent_bonus_year and year and year >= recent_bonus_year:
        score += 1

    if row.get("Q区","") == "Q1":
        score += 1

    if row.get("是否重复","") == "是":
        score -= 10

    return score

def search_pubmed(query, email, retmax, sort_ui):
    Entrez.email = email
    handle = Entrez.esearch(db="pubmed", term=query, retmax=retmax, sort=PUBMED_SORT_MAP.get(sort_ui,"relevance"))
    result = Entrez.read(handle); handle.close()
    return result.get("IdList",[])

def medline_batch_fetch(pmids, email, batch_size=200):
    Entrez.email = email
    rows = []
    for start in range(0, len(pmids), batch_size):
        batch = pmids[start:start+batch_size]
        handle = Entrez.efetch(db="pubmed", id=",".join(batch), rettype="medline", retmode="text")
        raw = handle.read(); handle.close()
        for r in Medline.parse(StringIO(raw)):
            row = {
                "PMID": r.get("PMID",""), "Title": r.get("TI",""), "Authors": "; ".join(r.get("AU",[])),
                "Journal": r.get("JT",""), "Year": r.get("DP",""), "DOI": parse_doi(r.get("AID",[])),
                "Abstract": " ".join(str(r.get("AB","")).splitlines()),
                "PublicationType": "; ".join(r.get("PT",[])), "ArticleType": "", "Language": "; ".join(r.get("LA",[])),
                "PubMedURL": f"https://pubmed.ncbi.nlm.nih.gov/{r.get('PMID','')}/", "Decision":"待定","Reason":"","Notes":"","Tags":"",
                "相关性评分":0,"是否重复":"","Q区":"","影响因子":"","中科院分区":""
            }
            row["ArticleType"] = article_type_from_row(row)
            rows.append(row)
        time.sleep(0.34)
    return rows

def rows_to_ris(rows):
    lines = []
    for row in rows:
        lines += ["TY  - JOUR"]
        if row.get("Title"): lines += [f"TI  - {row['Title']}"]
        for author in [a.strip() for a in str(row.get("Authors","")).split(";") if a.strip()]:
            lines += [f"AU  - {author}"]
        if row.get("Journal"): lines += [f"JO  - {row['Journal']}"]
        if row.get("Year"): lines += [f"PY  - {row['Year']}"]
        if row.get("DOI"): lines += [f"DO  - {row['DOI']}"]
        if row.get("Abstract"): lines += [f"AB  - {row['Abstract']}"]
        if row.get("PMID"): lines += [f"ID  - PMID:{row['PMID']}"]
        if row.get("PubMedURL"): lines += [f"UR  - {row['PubMedURL']}"]
        lines += ["ER  - ",""]
    return "\n".join(lines)

def write_csv(path, rows):
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.DictWriter(f, fieldnames=COLUMNS, extrasaction="ignore"); w.writeheader()
        for row in rows: w.writerow(row)

def keyword_expr_match(text, expr):
    if not expr.strip(): return True
    text = (text or "").lower()
    parts = [p.strip() for p in re.split(r"\s+OR\s+", expr, flags=re.I)]
    return any(p.lower() in text for p in parts if p)

def truncate_abstract(text, mode):
    text = (text or "").strip()
    if mode == "完整摘要": return text
    if mode == "前300字": return text[:300]
    if mode == "前500字": return text[:500]
    if mode == "不包含摘要": return ""
    return text

class SettingsWindow(tk.Toplevel):
    def __init__(self, master, settings, save_callback, test_callback):
        super().__init__(master)
        self.title(f"{APP_NAME} 设置"); self.geometry("860x700"); self.resizable(False, False)
        self.save_callback = save_callback; self.test_callback = test_callback
        frm = ttk.Frame(self, padding=14); frm.pack(fill="both", expand=True)
        ttk.Label(frm,text="NCBI / PubMed",font=("",10,"bold")).grid(row=0,column=0,sticky="w",columnspan=4)
        ttk.Label(frm,text="NCBI 邮箱").grid(row=1,column=0,sticky="w",pady=(8,0))
        self.email_var = tk.StringVar(value=settings.get("email",""))
        ttk.Entry(frm,textvariable=self.email_var,width=36).grid(row=1,column=1,sticky="w",padx=6,pady=(8,0))
        ttk.Label(frm,text="EasyScholar",font=("",10,"bold")).grid(row=2,column=0,sticky="w",columnspan=4,pady=(18,0))
        ttk.Label(frm,text="URL").grid(row=3,column=0,sticky="w",pady=(8,0))
        self.url_var = tk.StringVar(value=settings.get("easy_url","https://www.easyscholar.cc/open/getPublicationRank"))
        ttk.Entry(frm,textvariable=self.url_var,width=72).grid(row=3,column=1,columnspan=3,sticky="ew",padx=6,pady=(8,0))
        ttk.Label(frm,text="SecretKey").grid(row=4,column=0,sticky="w",pady=(8,0))
        self.key_var = tk.StringVar(value=settings.get("easy_key",""))
        ttk.Entry(frm,textvariable=self.key_var,width=36,show="*").grid(row=4,column=1,sticky="w",padx=6,pady=(8,0))
        self.easy_enable_var = tk.BooleanVar(value=settings.get("easy_enable",False))
        ttk.Checkbutton(frm,text="自动查询期刊信息",variable=self.easy_enable_var).grid(row=4,column=2,sticky="w",pady=(8,0))
        ttk.Button(frm,text="测试接口",command=self.test).grid(row=4,column=3,sticky="e",pady=(8,0))
        ttk.Label(frm,text="默认行为",font=("",10,"bold")).grid(row=5,column=0,sticky="w",columnspan=4,pady=(18,0))
        ttk.Label(frm,text="默认抓取条数").grid(row=6,column=0,sticky="w",pady=(8,0))
        self.retmax_var = tk.StringVar(value=str(settings.get("retmax",50)))
        ttk.Entry(frm,textvariable=self.retmax_var,width=12).grid(row=6,column=1,sticky="w",padx=6,pady=(8,0))
        self.auto_dedupe_var = tk.BooleanVar(value=settings.get("auto_dedupe",True))
        self.auto_type_var = tk.BooleanVar(value=settings.get("auto_type",True))
        self.auto_score_var = tk.BooleanVar(value=settings.get("auto_score",True))
        self.template_apply_count_var = tk.BooleanVar(value=settings.get("apply_template_count",True))
        ttk.Checkbutton(frm,text="自动去重",variable=self.auto_dedupe_var).grid(row=7,column=0,sticky="w",pady=(8,0))
        ttk.Checkbutton(frm,text="自动识别文章类型",variable=self.auto_type_var).grid(row=7,column=1,sticky="w",pady=(8,0))
        ttk.Checkbutton(frm,text="自动相关性评分",variable=self.auto_score_var).grid(row=7,column=2,sticky="w",pady=(8,0))
        ttk.Checkbutton(frm,text="应用模板时覆盖抓取条数",variable=self.template_apply_count_var).grid(row=8,column=0,columnspan=2,sticky="w",pady=(8,0))
        ttk.Label(frm,text="快捷键",font=("",10,"bold")).grid(row=9,column=0,sticky="w",columnspan=4,pady=(18,0))
        self.shortcut_vars = {}
        keys = settings.get("shortcuts",DEFAULT_SHORTCUTS)
        row = 10
        for name in ["保留","排除","待定","循环切换","打开PubMed"]:
            ttk.Label(frm,text=name).grid(row=row,column=0,sticky="w",pady=(6,0))
            var = tk.StringVar(value=keys.get(name,DEFAULT_SHORTCUTS[name])); self.shortcut_vars[name]=var
            ttk.Entry(frm,textvariable=var,width=14).grid(row=row,column=1,sticky="w",padx=6,pady=(6,0))
            row += 1
        ttk.Label(frm,text="GPT 分析设置",font=("",10,"bold")).grid(row=row,column=0,sticky="w",columnspan=4,pady=(18,0)); row += 1
        ttk.Label(frm,text="摘要长度").grid(row=row,column=0,sticky="w",pady=(8,0))
        self.abstract_len_var = tk.StringVar(value=settings.get("gpt_abstract_mode","前300字"))
        ttk.Combobox(frm,textvariable=self.abstract_len_var,values=["完整摘要","前300字","前500字","不包含摘要"],state="readonly",width=16).grid(row=row,column=1,sticky="w",padx=6,pady=(8,0))
        btns = ttk.Frame(frm); btns.grid(row=row+2,column=0,columnspan=4,sticky="e",pady=(24,0))
        ttk.Button(btns,text="保存",command=self.save).pack(side="right")
        ttk.Button(btns,text="取消",command=self.destroy).pack(side="right",padx=8)
        for i in range(4): frm.columnconfigure(i, weight=1)
    def test(self): self.test_callback(self.url_var.get().strip(), self.key_var.get().strip())
    def save(self):
        try: retmax = int(self.retmax_var.get().strip())
        except: messagebox.showerror("提示","默认抓取条数必须是整数。"); return
        self.save_callback({
            "email": self.email_var.get().strip(),
            "easy_url": self.url_var.get().strip(),
            "easy_key": self.key_var.get().strip(),
            "easy_enable": self.easy_enable_var.get(),
            "retmax": retmax,
            "auto_dedupe": self.auto_dedupe_var.get(),
            "auto_type": self.auto_type_var.get(),
            "auto_score": self.auto_score_var.get(),
            "apply_template_count": self.template_apply_count_var.get(),
            "shortcuts": {k:v.get().strip() for k,v in self.shortcut_vars.items()},
            "gpt_abstract_mode": self.abstract_len_var.get().strip(),
        }); self.destroy()

class GPTAnalysisWindow(tk.Toplevel):
    def __init__(self, master, selected_rows, query_text, settings):
        super().__init__(master)
        self.title(f"{APP_NAME} - 文献分析"); self.geometry("1100x780")
        self.selected_rows = selected_rows; self.query_text = query_text.strip(); self.settings = settings
        frm = ttk.Frame(self,padding=12); frm.pack(fill="both", expand=True)
        ttk.Label(frm,text="自定义任务（可编辑）",font=("",10,"bold")).pack(anchor="w")
        self.task_text = tk.Text(frm,height=8,wrap="word"); self.task_text.pack(fill="x",pady=(6,0))
        self.task_text.insert("1.0", settings.get("gpt_custom_task", DEFAULT_GPT_TASK))
        self.remember_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(frm,text="记住本次任务（下次自动填充）",variable=self.remember_var).pack(anchor="w",pady=(6,10))
        ttk.Label(frm,text="自动生成的文献数据（预览）",font=("",10,"bold")).pack(anchor="w")
        self.preview_text = tk.Text(frm,wrap="word"); self.preview_text.pack(fill="both",expand=True,pady=(6,0))
        self.preview_text.insert("1.0", self.build_preview()); self.preview_text.config(state="disabled")
        btns = ttk.Frame(frm); btns.pack(fill="x",pady=(10,0))
        ttk.Button(btns,text="复制到剪贴板",command=self.copy_all).pack(side="right")
        ttk.Button(btns,text="导出 TXT",command=self.export_txt).pack(side="right",padx=6)
    def build_preview(self):
        total = len(self.selected_rows); type_counter = Counter(); q_counter = Counter(); nondup = 0
        for row in self.selected_rows:
            if row.get("是否重复","") != "是": nondup += 1
            for part in [x.strip() for x in str(row.get("ArticleType","")).split(";") if x.strip()]:
                type_counter[part] += 1
            if row.get("Q区",""): q_counter[row.get("Q区")] += 1
        lines = [f"主题：{self.query_text or '用户选中文献分析'}","","当前文献概况：",f"- 总数：{total}"]
        for k,v in type_counter.most_common(): lines.append(f"- {k}：{v}")
        for q in ["Q1","Q2","Q3","Q4"]:
            if q_counter.get(q): lines.append(f"- {q}：{q_counter[q]}")
        lines.append(f"- 非重复：{nondup}"); lines += ["","以下是文献列表："]
        abs_mode = self.settings.get("gpt_abstract_mode","前300字")
        for i,row in enumerate(self.selected_rows,1):
            lines.append(f"{i}. PMID={row.get('PMID','')}")
            lines.append(f"   标题={row.get('Title','')}")
            lines.append(f"   期刊={row.get('Journal','')}")
            lines.append(f"   年份={row.get('Year','')}")
            lines.append(f"   文章类型={row.get('ArticleType','')}")
            abs_text = truncate_abstract(row.get("Abstract",""), abs_mode)
            if abs_text: lines.append(f"   摘要={abs_text}")
            lines.append("")
        return "\n".join(lines).strip()
    def final_text(self):
        task = self.task_text.get("1.0","end").strip(); preview = self.build_preview()
        if self.remember_var.get():
            self.settings["gpt_custom_task"] = task
            with open(SETTINGS_FILE,"w",encoding="utf-8") as f: json.dump(self.settings,f,ensure_ascii=False,indent=2)
        return task + "\n\n" + preview
    def copy_all(self):
        text = self.final_text(); self.clipboard_clear(); self.clipboard_append(text); self.update()
        messagebox.showinfo("完成","已复制到剪贴板。")
    def export_txt(self):
        path = filedialog.asksaveasfilename(defaultextension=".txt",filetypes=[("TXT 文件","*.txt")],initialfile="selected_analysis.txt")
        if path:
            with open(path,"w",encoding="utf-8") as f: f.write(self.final_text())
            messagebox.showinfo("完成","已导出 TXT。")

class StatsWindow(tk.Toplevel):
    def __init__(self, master, rows, apply_type_filter, apply_q_filter):
        super().__init__(master)
        self.title(f"{APP_NAME} - 分类统计"); self.geometry("760x560")
        frm = ttk.Frame(self,padding=12); frm.pack(fill="both",expand=True)
        left = ttk.LabelFrame(frm,text="文章类型分布（点击筛选）",padding=10); left.pack(side="left",fill="both",expand=True,padx=(0,8))
        right = ttk.LabelFrame(frm,text="Q区分布（点击筛选）",padding=10); right.pack(side="left",fill="both",expand=True,padx=(8,0))
        type_counter = Counter(); q_counter = Counter()
        for row in rows:
            for part in [x.strip() for x in str(row.get("ArticleType","")).split(";") if x.strip()]: type_counter[part] += 1
            if row.get("Q区",""): q_counter[row.get("Q区")] += 1
        ttk.Button(left,text="清除文章类型筛选",command=lambda: apply_type_filter("")).pack(fill="x",pady=(0,8))
        for name,count in type_counter.most_common():
            ttk.Button(left,text=f"{name} ({count})",command=lambda n=name: apply_type_filter(n)).pack(fill="x",pady=2)
        ttk.Button(right,text="清除Q区筛选",command=lambda: apply_q_filter("全部")).pack(fill="x",pady=(0,8))
        for q in ["Q1","Q2","Q3","Q4"]:
            if q_counter.get(q):
                ttk.Button(right,text=f"{q} ({q_counter[q]})",command=lambda x=q: apply_q_filter(x)).pack(fill="x",pady=2)

class DetailWindow(tk.Toplevel):
    def __init__(self, master, row_data, save_callback):
        super().__init__(master)
        self.title(f"{APP_NAME} - 文献详情"); self.geometry("1120x760"); self.row_data = row_data; self.save_callback = save_callback
        top = ttk.Frame(self,padding=10); top.pack(fill="both",expand=True)
        meta = ttk.Frame(top); meta.pack(fill="x")
        meta_items = [("PMID",row_data.get("PMID","")),("发表时间",row_data.get("Year","")),("期刊",row_data.get("Journal","")),("DOI",row_data.get("DOI","")),("文章类型",row_data.get("ArticleType","")),("相关性评分",str(row_data.get("相关性评分",""))),("Q区",row_data.get("Q区","")),("影响因子",str(row_data.get("影响因子",""))),("中科院分区",row_data.get("中科院分区","")),("是否重复",row_data.get("是否重复",""))]
        for i,(k,v) in enumerate(meta_items):
            ttk.Label(meta,text=f"{k}:").grid(row=i//2,column=(i%2)*2,sticky="w",pady=2)
            ttk.Label(meta,text=v,wraplength=430).grid(row=i//2,column=(i%2)*2+1,sticky="w",padx=(4,18),pady=2)
        ttk.Label(top,text="标题").pack(anchor="w",pady=(10,0))
        self.title_text = tk.Text(top,height=4,wrap="word"); self.title_text.pack(fill="x"); self.title_text.insert("1.0",row_data.get("Title",""))
        ttk.Label(top,text="作者").pack(anchor="w",pady=(10,0))
        self.authors_text = tk.Text(top,height=2,wrap="word"); self.authors_text.pack(fill="x"); self.authors_text.insert("1.0",row_data.get("Authors",""))
        ttk.Label(top,text="摘要").pack(anchor="w",pady=(10,0))
        self.abstract_text = tk.Text(top,height=16,wrap="word"); self.abstract_text.pack(fill="both",expand=True); self.abstract_text.insert("1.0",row_data.get("Abstract",""))
        form = ttk.Frame(top); form.pack(fill="x",pady=10)
        ttk.Label(form,text="筛选结果").grid(row=0,column=0,sticky="w")
        self.decision_var = tk.StringVar(value=row_data.get("Decision","待定"))
        ttk.Combobox(form,textvariable=self.decision_var,values=["待定","保留","排除"],state="readonly",width=16).grid(row=0,column=1,sticky="w",padx=6)
        ttk.Label(form,text="排除理由").grid(row=0,column=2,sticky="w",padx=(12,0))
        self.reason_entry = ttk.Entry(form,width=40); self.reason_entry.grid(row=0,column=3,sticky="ew",padx=6); self.reason_entry.insert(0,row_data.get("Reason",""))
        ttk.Label(form,text="标签").grid(row=1,column=0,sticky="w",pady=(8,0))
        self.tags_entry = ttk.Entry(form,width=40); self.tags_entry.grid(row=1,column=1,sticky="ew",padx=6,pady=(8,0)); self.tags_entry.insert(0,row_data.get("Tags",""))
        ttk.Label(form,text="备注").grid(row=2,column=0,sticky="nw",pady=(8,0))
        self.notes_text = tk.Text(form,height=5,wrap="word"); self.notes_text.grid(row=2,column=1,columnspan=3,sticky="ew",pady=(8,0)); self.notes_text.insert("1.0",row_data.get("Notes",""))
        form.columnconfigure(3, weight=1)
        btns = ttk.Frame(top); btns.pack(fill="x")
        ttk.Button(btns,text="保存",command=self.save).pack(side="right")
        ttk.Button(btns,text="关闭",command=self.destroy).pack(side="right",padx=8)
    def save(self):
        self.row_data["Title"] = self.title_text.get("1.0","end").strip()
        self.row_data["Authors"] = self.authors_text.get("1.0","end").strip()
        self.row_data["Abstract"] = self.abstract_text.get("1.0","end").strip()
        self.row_data["Decision"] = self.decision_var.get().strip()
        self.row_data["Reason"] = self.reason_entry.get().strip()
        self.row_data["Tags"] = self.tags_entry.get().strip()
        self.row_data["Notes"] = self.notes_text.get("1.0","end").strip()
        self.row_data["ArticleType"] = article_type_from_row(self.row_data)
        self.save_callback(self.row_data); self.destroy()

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE); self.geometry("1760x980")
        self.rows = []; self.filtered_indices = []; self.settings = self.load_json(SETTINGS_FILE,{})
        self.templates = self.load_templates(); self.current_sort_column = "相关性评分"; self.current_sort_desc = True
        self.tree_tags_configured = False; self.advanced_visible = False
        self._build_ui(); self.apply_loaded_settings(); self.refresh_template_dropdown(); self.bind_shortcuts()

    def load_json(self, path, default):
        if os.path.exists(path):
            try:
                with open(path,"r",encoding="utf-8") as f: return json.load(f)
            except: return default
        return default

    def save_json(self, path, data):
        with open(path,"w",encoding="utf-8") as f: json.dump(data,f,ensure_ascii=False,indent=2)

    def load_templates(self):
        data = self.load_json(TEMPLATES_FILE,{})
        merged = dict(BUILTIN_TEMPLATES); merged.update(data); return merged

    def save_custom_templates(self):
        custom = {k:v for k,v in self.templates.items() if not v.get("builtin")}
        self.save_json(TEMPLATES_FILE, custom)

    def get_shortcuts(self):
        sc = dict(DEFAULT_SHORTCUTS); sc.update(self.settings.get("shortcuts",{})); return sc

    def bind_shortcuts(self):
        shortcuts = self.get_shortcuts()
        for action,key in shortcuts.items():
            if not key: continue
            sequence = f"<{key}>"
            if action == "保留": self.bind_all(sequence, lambda e: self.quick_set_decision("保留"))
            elif action == "排除": self.bind_all(sequence, lambda e: self.quick_set_decision("排除"))
            elif action == "待定": self.bind_all(sequence, lambda e: self.quick_set_decision("待定"))
            elif action == "循环切换": self.bind_all(sequence, lambda e: self.cycle_decision())
            elif action == "打开PubMed": self.bind_all(sequence, lambda e: self.open_selected_pubmed())

    def get_selected_target_types(self):
        return [name for name,var in self.target_type_vars.items() if var.get()]

    def set_selected_target_types(self, values):
        values = set(values or [])
        for name,var in self.target_type_vars.items(): var.set(name in values)

    def apply_loaded_settings(self):
        self.retmax_var.set(str(self.settings.get("retmax",50)))
        self.pubmed_sort_var.set(self.settings.get("pubmed_sort","最佳匹配 Best Match"))
        self.highlight_var.set(self.settings.get("highlight",""))
        self.core_kw_var.set(self.settings.get("core_keywords",""))
        self.title_kw_var.set(self.settings.get("title_kw",""))
        self.abstract_kw_var.set(self.settings.get("abstract_kw",""))
        self.year_min_var.set(self.settings.get("year_min",""))
        self.year_max_var.set(self.settings.get("year_max",""))
        self.decision_filter_var.set(self.settings.get("decision","全部"))
        self.type_filter_var.set(self.settings.get("type_filter",""))
        self.q_filter_var.set(self.settings.get("q_filter","全部"))
        self.nondup_only_var.set(self.settings.get("nondup_only",False))
        self.current_template_var.set(self.settings.get("template","默认"))
        self.set_selected_target_types(self.settings.get("target_types",[]))

    def persist_settings(self):
        try: retmax = int(self.retmax_var.get().strip() or 50)
        except: retmax = 50
        data = {
            "retmax": retmax, "pubmed_sort": self.pubmed_sort_var.get().strip(), "highlight": self.highlight_var.get().strip(),
            "core_keywords": self.core_kw_var.get().strip(), "title_kw": self.title_kw_var.get().strip(),
            "abstract_kw": self.abstract_kw_var.get().strip(), "year_min": self.year_min_var.get().strip(),
            "year_max": self.year_max_var.get().strip(), "decision": self.decision_filter_var.get().strip(),
            "type_filter": self.type_filter_var.get().strip(), "q_filter": self.q_filter_var.get().strip(),
            "nondup_only": self.nondup_only_var.get(), "template": self.current_template_var.get().strip(),
            "target_types": self.get_selected_target_types(),
        }
        self.settings.update(data); self.save_json(SETTINGS_FILE,self.settings)

    def _build_ui(self):
        top = ttk.Frame(self,padding=10); top.pack(fill="x")
        ttk.Label(top,text="抓取条数").grid(row=0,column=0,sticky="w")
        self.retmax_var = tk.StringVar(value="50")
        ttk.Entry(top,textvariable=self.retmax_var,width=10).grid(row=0,column=1,sticky="w",padx=6)
        ttk.Label(top,text="PubMed 排序").grid(row=0,column=2,sticky="w",padx=(12,0))
        self.pubmed_sort_var = tk.StringVar(value="最佳匹配 Best Match")
        ttk.Combobox(top,textvariable=self.pubmed_sort_var,values=list(PUBMED_SORT_MAP.keys()),state="readonly",width=24).grid(row=0,column=3,sticky="w",padx=6)
        self.mode_var = tk.StringVar(value="search")
        ttk.Radiobutton(top,text="PubMed 检索",variable=self.mode_var,value="search").grid(row=0,column=4,padx=(18,4))
        ttk.Radiobutton(top,text="PMID 列表导入",variable=self.mode_var,value="pmid").grid(row=0,column=5)
        ttk.Button(top,text="开始抓取",command=self.fetch_records).grid(row=0,column=6,padx=(18,6))
        ttk.Button(top,text="设置",command=self.open_settings).grid(row=0,column=7)
        self.append_mode_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(top, text="追加到当前结果", variable=self.append_mode_var).grid(row=0, column=8, padx=(8, 0))
        ttk.Button(top, text="清空结果", command=self.clear_all_rows).grid(row=0, column=9, padx=6)
        ttk.Label(top,text="检索式 / PMID").grid(row=1,column=0,sticky="nw",pady=(10,0))
        self.query_text = tk.Text(top,height=4,wrap="word"); self.query_text.grid(row=1,column=1,columnspan=7,sticky="ew",pady=(10,0),padx=6)
        top.columnconfigure(7, weight=1)

        tools = ttk.LabelFrame(self,text="模板与分析参数",padding=10); tools.pack(fill="x",padx=10,pady=(0,10))
        ttk.Label(tools,text="筛选策略").grid(row=0,column=0,sticky="w")
        self.current_template_var = tk.StringVar(value="默认")
        self.template_combo = ttk.Combobox(tools,textvariable=self.current_template_var,state="readonly",width=20)
        self.template_combo.grid(row=0,column=1,sticky="w",padx=6)
        ttk.Button(tools,text="应用策略",command=self.apply_template).grid(row=0,column=2,sticky="w",padx=6)
        ttk.Button(tools,text="保存当前为策略",command=self.save_template_prompt).grid(row=0,column=3,sticky="w",padx=6)
        ttk.Button(tools,text="重新查询期刊信息",command=self.enrich_journals).grid(row=0,column=4,sticky="w",padx=6)
        ttk.Button(tools,text="分类统计",command=self.show_stats).grid(row=0,column=5,sticky="w",padx=6)
        ttk.Button(tools,text="生成选中文献分析文本",command=self.open_gpt_analysis).grid(row=0,column=6,sticky="w",padx=6)
        self.advanced_toggle_btn = ttk.Button(tools,text="▼ 高级筛选",command=self.toggle_advanced)
        self.advanced_toggle_btn.grid(row=1,column=0,sticky="w",pady=(10,0))
        self.advanced_frame = ttk.Frame(tools); self.advanced_frame.grid(row=2,column=0,columnspan=7,sticky="ew",pady=(10,0)); self.advanced_frame.grid_remove()
        columns_frame = ttk.Frame(self.advanced_frame); columns_frame.pack(fill="x")
        columns_frame.columnconfigure(0,weight=1); columns_frame.columnconfigure(1,weight=1); columns_frame.columnconfigure(2,weight=1)
        col1 = ttk.Frame(columns_frame); col1.grid(row=0,column=0,sticky="nsew",padx=(0,8))
        ttk.Label(col1,text="核心关键词").pack(anchor="w")
        self.core_kw_var = tk.StringVar(); ttk.Entry(col1,textvariable=self.core_kw_var).pack(fill="x",pady=(4,0))
        col2 = ttk.Frame(columns_frame); col2.grid(row=0,column=1,sticky="nsew",padx=8)
        ttk.Label(col2,text="高亮关键词").pack(anchor="w")
        self.highlight_var = tk.StringVar(); ttk.Entry(col2,textvariable=self.highlight_var).pack(fill="x",pady=(4,0))
        col3 = ttk.LabelFrame(columns_frame,text="目标文章类型（多选）",padding=6); col3.grid(row=0,column=2,sticky="nsew",padx=(8,0))
        self.target_type_vars = {}
        for i,name in enumerate(ARTICLE_TYPE_OPTIONS):
            var = tk.BooleanVar(value=False); self.target_type_vars[name] = var
            ttk.Checkbutton(col3,text=name,variable=var).grid(row=i//2,column=i%2,sticky="w",padx=4,pady=2)

        btns = ttk.Frame(self,padding=(10,0)); btns.pack(fill="x")
        ttk.Button(btns,text="应用过滤",command=self.apply_filters).pack(side="left")
        ttk.Button(btns,text="清空过滤",command=self.clear_filters).pack(side="left",padx=6)
        ttk.Button(btns,text="最近1年",command=lambda: self.quick_year_range(1)).pack(side="left",padx=(12,0))
        ttk.Button(btns,text="最近3年",command=lambda: self.quick_year_range(3)).pack(side="left",padx=6)
        ttk.Button(btns,text="最近5年",command=lambda: self.quick_year_range(5)).pack(side="left",padx=6)
        ttk.Button(btns,text="清空年份",command=self.clear_year_range).pack(side="left",padx=6)
        ttk.Button(btns,text="查看/编辑选中文献",command=self.open_selected_detail).pack(side="left",padx=18)
        ttk.Button(btns,text="批量打标签",command=self.batch_tag).pack(side="left",padx=6)
        ttk.Button(btns,text="一键生成纳排理由",command=self.auto_reason_selected).pack(side="left",padx=6)
        ttk.Button(btns,text="标记保留",command=lambda: self.quick_set_decision("保留")).pack(side="left",padx=12)
        ttk.Button(btns,text="标记排除",command=lambda: self.quick_set_decision("排除")).pack(side="left",padx=6)
        ttk.Button(btns,text="标记待定",command=lambda: self.quick_set_decision("待定")).pack(side="left",padx=6)
        ttk.Button(btns,text="导出核心文献包",command=self.export_core_bundle).pack(side="right")
        ttk.Button(btns,text="导出全部 CSV",command=self.export_all_csv).pack(side="right",padx=6)
        ttk.Button(btns,text="导出保留 RIS",command=self.export_kept_ris).pack(side="right",padx=6)
        ttk.Button(btns,text="导出保留 CSV",command=self.export_kept_csv).pack(side="right",padx=6)

        filters = ttk.LabelFrame(self,text="过滤",padding=10); filters.pack(fill="x",padx=10,pady=10)
        ttk.Label(filters,text="标题关键词").grid(row=0,column=0,sticky="w")
        self.title_kw_var = tk.StringVar(); ttk.Entry(filters,textvariable=self.title_kw_var,width=18).grid(row=0,column=1,padx=6)
        ttk.Label(filters,text="摘要关键词").grid(row=0,column=2,sticky="w",padx=(10,0))
        self.abstract_kw_var = tk.StringVar(); ttk.Entry(filters,textvariable=self.abstract_kw_var,width=22).grid(row=0,column=3,padx=6)
        ttk.Label(filters,text="最早年份").grid(row=0,column=4,sticky="w",padx=(10,0))
        self.year_min_var = tk.StringVar(); ttk.Entry(filters,textvariable=self.year_min_var,width=8).grid(row=0,column=5,padx=6)
        ttk.Label(filters,text="最晚年份").grid(row=0,column=6,sticky="w",padx=(10,0))
        self.year_max_var = tk.StringVar(); ttk.Entry(filters,textvariable=self.year_max_var,width=8).grid(row=0,column=7,padx=6)
        ttk.Label(filters,text="筛选结果").grid(row=0,column=8,sticky="w",padx=(10,0))
        self.decision_filter_var = tk.StringVar(value="全部")
        ttk.Combobox(filters,textvariable=self.decision_filter_var,values=["全部","待定","保留","排除"],state="readonly",width=10).grid(row=0,column=9,padx=6)
        ttk.Label(filters,text="文章类型").grid(row=0,column=10,sticky="w",padx=(10,0))
        self.type_filter_var = tk.StringVar(value=""); ttk.Entry(filters,textvariable=self.type_filter_var,width=16).grid(row=0,column=11,padx=6)
        ttk.Label(filters,text="Q区").grid(row=0,column=12,sticky="w",padx=(10,0))
        self.q_filter_var = tk.StringVar(value="全部")
        ttk.Combobox(filters,textvariable=self.q_filter_var,values=["全部","Q1","Q2","Q3","Q4"],state="readonly",width=8).grid(row=0,column=13,padx=6)
        self.nondup_only_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(filters,text="仅看非重复",variable=self.nondup_only_var).grid(row=0,column=14,padx=(12,0))

        stats = ttk.Frame(self,padding=(10,0)); stats.pack(fill="x")
        self.status_var = tk.StringVar(value="准备就绪"); ttk.Label(stats,textvariable=self.status_var).pack(side="left")
        self.counts_var = tk.StringVar(value="保留 0 | 排除 0 | 待定 0 | 重复 0"); ttk.Label(stats,textvariable=self.counts_var).pack(side="right")

        table_frame = ttk.Frame(self,padding=10); table_frame.pack(fill="both",expand=True)
        self.tree = ttk.Treeview(table_frame,columns=TREE_COLUMNS,show="headings",selectmode="extended")
        widths = {"筛选结果":90,"PMID":95,"发表时间":100,"期刊":220,"Q区":55,"影响因子":75,"中科院分区":120,"文章类型":180,"相关性评分":100,"是否重复":85,"标签":140,"标题":620,"排除理由":180}
        for c in TREE_COLUMNS:
            self.tree.heading(c,text=c,command=lambda col=c: self.sort_by_column_click(col))
            self.tree.column(c,width=widths[c],anchor="w")
        self.tree.pack(side="left",fill="both",expand=True)
        self.tree.bind("<Double-1>", lambda e: self.open_selected_detail())
        self.tree.bind("<Button-3>", self.show_context_menu)
        yscroll = ttk.Scrollbar(table_frame,orient="vertical",command=self.tree.yview); yscroll.pack(side="right",fill="y")
        self.tree.configure(yscrollcommand=yscroll.set)

        self.context_menu = tk.Menu(self,tearoff=0)
        self.context_menu.add_command(label="标记保留",command=lambda: self.quick_set_decision("保留"))
        self.context_menu.add_command(label="标记排除",command=lambda: self.quick_set_decision("排除"))
        self.context_menu.add_command(label="标记待定",command=lambda: self.quick_set_decision("待定"))
        self.context_menu.add_separator()
        self.context_menu.add_command(label="打开 PubMed",command=self.open_selected_pubmed)
        self.context_menu.add_command(label="复制 PMID",command=lambda: self.copy_selected_field("PMID"))
        self.context_menu.add_command(label="复制 DOI",command=lambda: self.copy_selected_field("DOI"))
        self.context_menu.add_command(label="复制标题",command=lambda: self.copy_selected_field("Title"))

    def toggle_advanced(self):
        self.advanced_visible = not self.advanced_visible
        if self.advanced_visible:
            self.advanced_frame.grid(); self.advanced_toggle_btn.config(text="▲ 高级筛选")
        else:
            self.advanced_frame.grid_remove(); self.advanced_toggle_btn.config(text="▼ 高级筛选")

    def quick_year_range(self, years):
        current = time.localtime().tm_year
        self.year_min_var.set(str(current - years)); self.year_max_var.set(str(current)); self.apply_filters()

    def clear_year_range(self):
        self.year_min_var.set(""); self.year_max_var.set(""); self.apply_filters()

    def refresh_template_dropdown(self):
        self.template_combo["values"] = list(self.templates.keys())
        if self.current_template_var.get() not in self.templates: self.current_template_var.set("默认")

    def set_status(self, text):
        self.status_var.set(text); self.update_idletasks()

    def show_stats(self):
        if not self.rows:
            messagebox.showinfo("提示","请先抓取文献。"); return
        StatsWindow(self, self.rows, lambda name:(self.type_filter_var.set(name), self.apply_filters()),
                         lambda q:(self.q_filter_var.set(q), self.apply_filters()))

    def open_gpt_analysis(self):
        indices = self.get_selected_indices()
        if not indices:
            messagebox.showinfo("提示","请先选中文献。"); return
        GPTAnalysisWindow(self, [self.rows[i] for i in indices], self.query_text.get("1.0","end"), self.settings)

    def open_settings(self):
        def save_callback(data):
            self.settings.update(data); self.retmax_var.set(str(data.get("retmax",50))); self.persist_settings(); self.bind_shortcuts()
        def test_callback(url, key):
            try:
                if not url or not key:
                    messagebox.showerror("提示","请先填写 URL 和 SecretKey。"); return
                resp = requests.get(url, params={"secretKey": key, "publicationName": "Journal of Urology"}, timeout=15)
                meta = self.parse_easy_result(resp.json())
                messagebox.showinfo("测试结果", f"Q区: {meta.get('Q区','')}\n影响因子: {meta.get('影响因子','')}\n中科院分区: {meta.get('中科院分区','')}")
            except Exception as e:
                messagebox.showerror("测试失败", str(e))
        SettingsWindow(self, self.settings, save_callback, test_callback)

    def save_template_prompt(self):
        name = simpledialog.askstring("保存策略","请输入策略名称：")
        if not name: return
        self.templates[name] = {
            "builtin": False, "retmax": int(self.retmax_var.get().strip() or 50),
            "title_kw": self.title_kw_var.get().strip(), "abstract_kw": self.abstract_kw_var.get().strip(),
            "year_min": self.year_min_var.get().strip(), "year_max": self.year_max_var.get().strip(),
            "decision": self.decision_filter_var.get().strip(), "highlight": self.highlight_var.get().strip(),
            "core_keywords": self.core_kw_var.get().strip(), "target_types": self.get_selected_target_types(),
            "q_filter": self.q_filter_var.get().strip(), "nondup_only": self.nondup_only_var.get(),
        }
        self.save_custom_templates(); self.refresh_template_dropdown(); self.current_template_var.set(name); self.persist_settings()
        messagebox.showinfo("完成","策略已保存。")

    def apply_template(self):
        conf = self.templates.get(self.current_template_var.get().strip(), self.templates["默认"])
        self.title_kw_var.set(conf.get("title_kw","")); self.abstract_kw_var.set(conf.get("abstract_kw",""))
        self.year_min_var.set(conf.get("year_min","")); self.year_max_var.set(conf.get("year_max",""))
        self.decision_filter_var.set(conf.get("decision","全部")); self.highlight_var.set(conf.get("highlight",""))
        self.core_kw_var.set(conf.get("core_keywords","")); self.q_filter_var.set(conf.get("q_filter","全部"))
        self.nondup_only_var.set(conf.get("nondup_only",False)); self.set_selected_target_types(conf.get("target_types",[]))
        if self.settings.get("apply_template_count",True): self.retmax_var.set(str(conf.get("retmax",50)))
        if self.settings.get("auto_score",True): self.run_scoring()
        self.apply_filters()

    def clear_all_rows(self):
        self.rows = []
        self.filtered_indices = []
        self.refresh_tree()
        self.set_status("已清空当前结果。")

    def fetch_records(self):
        email = self.settings.get("email","").strip()
        if not email:
            messagebox.showerror("提示","请先在设置里填写 NCBI 邮箱。"); return
        try: retmax = int(self.retmax_var.get().strip())
        except: messagebox.showerror("提示","抓取条数必须是整数。"); return
        raw = self.query_text.get("1.0","end").strip()
        if not raw:
            messagebox.showerror("提示","请输入检索式或 PMID 列表。"); return
        self.persist_settings()
        try:
            if self.mode_var.get() == "search":
                self.set_status("正在搜索 PubMed..."); pmids = search_pubmed(normalize_query(raw), email, retmax, self.pubmed_sort_var.get())
            else:
                pmids = split_pmids(raw)
            if not pmids:
                messagebox.showinfo("结果","没有抓到文献。"); return
            self.set_status(f"正在抓取 {len(pmids)} 条记录...")
            new_rows = medline_batch_fetch(pmids, email)
            if self.settings.get("auto_type",True):
                for row in new_rows:
                    row["ArticleType"] = article_type_from_row(row)

            append_mode = self.append_mode_var.get() if hasattr(self, "append_mode_var") else True
            if append_mode:
                self.rows.extend(new_rows)
            else:
                self.rows = new_rows

            if self.settings.get("auto_dedupe",True):
                self.run_dedup()
            if self.settings.get("easy_enable",False):
                self.enrich_journals(auto=True)
            else:
                if self.settings.get("auto_score",True): self.run_scoring()
                self.apply_filters(); self.set_status(f"已抓取 {len(self.rows)} 条记录。")
        except Exception as e:
            messagebox.showerror("错误", str(e)); self.set_status("抓取失败")

    def run_dedup(self):
        seen_pmid, seen_doi, seen_title = set(), set(), set()
        for row in self.rows:
            row["是否重复"] = ""; dup = False
            pmid = row.get("PMID",""); doi = row.get("DOI","").lower().strip(); title_n = norm_text(row.get("Title",""))
            if pmid and pmid in seen_pmid: dup = True
            if doi and doi in seen_doi: dup = True
            if title_n and title_n in seen_title: dup = True
            if pmid: seen_pmid.add(pmid)
            if doi: seen_doi.add(doi)
            if title_n: seen_title.add(title_n)
            if dup:
                row["是否重复"] = "是"
                if not row.get("Reason"): row["Reason"] = "重复文献"

    def run_scoring(self):
        core_keywords = [x.strip() for x in re.split(r"[,;，；]+", self.core_kw_var.get().strip()) if x.strip()]
        target_types = self.get_selected_target_types()
        recent_bonus_year = time.localtime().tm_year - 5
        for row in self.rows: row["相关性评分"] = score_row(row, core_keywords, target_types, recent_bonus_year)

    def parse_easy_result(self, data):
        meta = {"Q区":"","影响因子":"","中科院分区":""}
        try:
            block = data.get("data",{}).get("officialRank",{}).get("all",{})
            meta["Q区"] = str(block.get("sci","") or "")
            meta["影响因子"] = str(block.get("sciif","") or "")
            meta["中科院分区"] = str(block.get("sciBase","") or "")
        except: pass
        return meta

    def enrich_journals(self, auto=False):
        if not self.rows:
            if not auto: messagebox.showinfo("提示","请先抓取文献。")
            return
        if not self.settings.get("easy_enable",False):
            if not auto: messagebox.showinfo("提示","请先在设置中启用 EasyScholar。")
            return
        key = self.settings.get("easy_key","").strip(); url = self.settings.get("easy_url","").strip()
        if not key or not url:
            if not auto: messagebox.showerror("提示","请先在设置中填写 EasyScholar URL 和 SecretKey。")
            return
        def work():
            try:
                self.set_status("正在补充期刊信息...")
                journals = sorted({normalize_journal(r.get("Journal","")) for r in self.rows if r.get("Journal","").strip()})
                cache = {}
                for i,jn in enumerate(journals,1):
                    original_name = next((r["Journal"] for r in self.rows if normalize_journal(r.get("Journal","")) == jn), "")
                    resp = requests.get(url, params={"secretKey": key, "publicationName": original_name}, timeout=15)
                    cache[jn] = self.parse_easy_result(resp.json())
                    self.set_status(f"期刊信息查询中 {i}/{len(journals)} ..."); time.sleep(0.7)
                for row in self.rows:
                    meta = cache.get(normalize_journal(row.get("Journal","")), {})
                    row["Q区"] = meta.get("Q区",""); row["影响因子"] = meta.get("影响因子",""); row["中科院分区"] = meta.get("中科院分区","")
                if self.settings.get("auto_score",True): self.run_scoring()
                self.apply_filters(); self.set_status(f"已抓取 {len(self.rows)} 条记录。")
            except Exception as e:
                if not auto: messagebox.showerror("EasyScholar 错误", str(e))
                self.set_status("期刊信息查询失败")
        threading.Thread(target=work, daemon=True).start()

    def apply_filters(self):
        title_kw = self.title_kw_var.get().strip().lower()
        abstract_kw = self.abstract_kw_var.get().strip()
        decision_filter = self.decision_filter_var.get().strip()
        type_filter = self.type_filter_var.get().strip().lower()
        q_filter = self.q_filter_var.get().strip()
        year_min = extract_year_num(self.year_min_var.get().strip())
        year_max = extract_year_num(self.year_max_var.get().strip())
        self.filtered_indices = []
        for idx,row in enumerate(self.rows):
            if title_kw and title_kw not in row.get("Title","").lower(): continue
            if abstract_kw and not keyword_expr_match(row.get("Abstract",""), abstract_kw): continue
            row_year = extract_year_num(row.get("Year",""))
            if year_min and (not row_year or row_year < year_min): continue
            if year_max and (not row_year or row_year > year_max): continue
            if decision_filter != "全部" and row.get("Decision","待定") != decision_filter: continue
            if type_filter and type_filter not in row.get("ArticleType","").lower(): continue
            if q_filter != "全部" and row.get("Q区","") != q_filter: continue
            if self.nondup_only_var.get() and row.get("是否重复","") == "是": continue
            self.filtered_indices.append(idx)
        self.sort_filtered_indices(); self.refresh_tree(); self.persist_settings()

    def sort_value(self, row, column):
        field = COLUMN_TO_FIELD.get(column,"")
        if field == "Decision": return str(row.get("Decision",""))
        if field == "PMID": return str(row.get("PMID",""))
        if field == "Year": return extract_year_num(row.get("Year","")) or -1
        if field == "Journal": return str(row.get("Journal","")).lower()
        if field == "Q区": return q_rank(row.get("Q区",""))
        if field == "影响因子": return to_float(row.get("影响因子",""))
        if field == "中科院分区": return cas_rank(row.get("中科院分区",""))
        if field == "ArticleType": return str(row.get("ArticleType","")).lower()
        if field == "相关性评分": return row.get("相关性评分",0) or 0
        if field == "是否重复": return 1 if row.get("是否重复","") == "是" else 0
        if field == "Tags": return str(row.get("Tags","")).lower()
        if field == "Title": return str(row.get("Title","")).lower()
        if field == "Reason": return str(row.get("Reason","")).lower()
        return 0

    def sort_filtered_indices(self):
        self.filtered_indices = sorted(self.filtered_indices, key=lambda i: self.sort_value(self.rows[i], self.current_sort_column), reverse=self.current_sort_desc)
        self.update_sort_headers()

    def sort_by_column_click(self, column):
        if self.current_sort_column == column: self.current_sort_desc = not self.current_sort_desc
        else:
            self.current_sort_column = column; self.current_sort_desc = True
        self.sort_filtered_indices(); self.refresh_tree()

    def update_sort_headers(self):
        for c in TREE_COLUMNS:
            label = c + (" ↓" if c == self.current_sort_column and self.current_sort_desc else " ↑" if c == self.current_sort_column else "")
            self.tree.heading(c, text=label, command=lambda col=c: self.sort_by_column_click(col))

    def clear_filters(self):
        self.title_kw_var.set(""); self.abstract_kw_var.set(""); self.year_min_var.set(""); self.year_max_var.set("")
        self.decision_filter_var.set("全部"); self.type_filter_var.set(""); self.q_filter_var.set("全部"); self.nondup_only_var.set(False)
        self.apply_filters()

    def refresh_tree(self):
        for item in self.tree.get_children(): self.tree.delete(item)
        if not self.tree_tags_configured:
            self.tree.tag_configure("keep", background="#e8f6e8")
            self.tree.tag_configure("exclude", background="#fdeaea")
            self.tree.tag_configure("pending", background="#f0f0f0")
            self.tree_tags_configured = True
        for idx in self.filtered_indices:
            row = self.rows[idx]
            tag = "keep" if row.get("Decision") == "保留" else "exclude" if row.get("Decision") == "排除" else "pending"
            self.tree.insert("", "end", iid=str(idx), values=(
                row.get("Decision",""), row.get("PMID",""), row.get("Year",""), row.get("Journal",""),
                row.get("Q区",""), row.get("影响因子",""), row.get("中科院分区",""), row.get("ArticleType",""),
                row.get("相关性评分",0), row.get("是否重复",""), row.get("Tags",""), row.get("Title",""), row.get("Reason","")
            ), tags=(tag,))
        self.update_counts()

    def update_counts(self):
        kept = sum(1 for r in self.rows if r.get("Decision") == "保留")
        excluded = sum(1 for r in self.rows if r.get("Decision") == "排除")
        undecided = sum(1 for r in self.rows if r.get("Decision","待定") == "待定")
        dup = sum(1 for r in self.rows if r.get("是否重复") == "是")
        self.counts_var.set(f"保留 {kept} | 排除 {excluded} | 待定 {undecided} | 重复 {dup}")

    def get_selected_indices(self):
        selection = self.tree.selection()
        return [int(x) for x in selection] if selection else []

    def quick_set_decision(self, value):
        indices = self.get_selected_indices()
        if not indices: return
        for idx in indices: self.rows[idx]["Decision"] = value
        self.refresh_tree()

    def cycle_decision(self):
        indices = self.get_selected_indices()
        if not indices: return
        order = {"待定":"保留","保留":"排除","排除":"待定"}
        for idx in indices:
            cur = self.rows[idx].get("Decision","待定"); self.rows[idx]["Decision"] = order.get(cur,"待定")
        self.refresh_tree()

    def open_selected_detail(self):
        indices = self.get_selected_indices()
        if not indices:
            messagebox.showinfo("提示","请先选中一条文献。"); return
        idx = indices[0]
        row_data = dict(self.rows[idx])
        def save_callback(updated):
            self.rows[idx] = updated
            if self.settings.get("auto_type",True): self.rows[idx]["ArticleType"] = article_type_from_row(self.rows[idx])
            if self.settings.get("auto_score",True): self.run_scoring()
            self.apply_filters()
        DetailWindow(self, row_data, save_callback)

    def show_context_menu(self, event):
        row_id = self.tree.identify_row(event.y)
        if row_id:
            self.tree.selection_set(row_id)
            self.context_menu.post(event.x_root, event.y_root)

    def open_selected_pubmed(self):
        indices = self.get_selected_indices()
        if not indices: return
        url = self.rows[indices[0]].get("PubMedURL","")
        if url: webbrowser.open(url)

    def copy_selected_field(self, field):
        indices = self.get_selected_indices()
        if not indices: return
        value = str(self.rows[indices[0]].get(field,""))
        self.clipboard_clear(); self.clipboard_append(value); self.update()

    def batch_tag(self):
        indices = self.get_selected_indices()
        if not indices:
            messagebox.showinfo("提示","请先选中文献。"); return
        raw = simpledialog.askstring("批量打标签","请输入标签（逗号或分号分隔）")
        if raw is None: return
        tags = [x.strip() for x in re.split(r"[,;，；]+", raw) if x.strip()]
        for idx in indices:
            old = [x.strip() for x in re.split(r"[,;，；]+", self.rows[idx].get("Tags","")) if x.strip()]
            self.rows[idx]["Tags"] = "; ".join(list(dict.fromkeys(old + tags)))
        self.refresh_tree()

    def auto_reason_selected(self):
        indices = self.get_selected_indices()
        if not indices:
            messagebox.showinfo("提示","请先选中文献。"); return
        menu = tk.Toplevel(self); menu.title(f"{APP_NAME} - 选择纳排理由"); menu.geometry("380x320")
        vars_ = []; frm = ttk.Frame(menu,padding=12); frm.pack(fill="both",expand=True)
        for reason in EXCLUSION_REASONS:
            v = tk.BooleanVar(value=False); vars_.append((reason,v)); ttk.Checkbutton(frm,text=reason,variable=v).pack(anchor="w")
        def apply():
            selected = [r for r,v in vars_ if v.get()]
            if not selected:
                messagebox.showinfo("提示","请至少选择一个理由。"); return
            text = "；".join(selected)
            for idx in indices:
                self.rows[idx]["Reason"] = text
                if self.rows[idx].get("Decision","待定") == "待定": self.rows[idx]["Decision"] = "排除"
            self.refresh_tree(); menu.destroy()
        ttk.Button(frm,text="应用",command=apply).pack(anchor="e",pady=10)

    def export_all_csv(self):
        if not self.rows:
            messagebox.showinfo("提示","当前没有数据可导出。"); return
        path = filedialog.asksaveasfilename(defaultextension=".csv",filetypes=[("CSV 文件","*.csv")],initialfile="litpilot_all.csv")
        if path: write_csv(path,self.rows); messagebox.showinfo("完成","已导出全部 CSV。")

    def export_kept_csv(self):
        kept = [r for r in self.rows if r.get("Decision") == "保留"]
        if not kept:
            messagebox.showinfo("提示","当前没有“保留”文献。"); return
        path = filedialog.asksaveasfilename(defaultextension=".csv",filetypes=[("CSV 文件","*.csv")],initialfile="litpilot_kept.csv")
        if path: write_csv(path,kept); messagebox.showinfo("完成","已导出保留项 CSV。")

    def export_kept_ris(self):
        kept = [r for r in self.rows if r.get("Decision") == "保留"]
        if not kept:
            messagebox.showinfo("提示","当前没有“保留”文献。"); return
        path = filedialog.asksaveasfilename(defaultextension=".ris",filetypes=[("RIS 文件","*.ris")],initialfile="litpilot_kept.ris")
        if path:
            with open(path,"w",encoding="utf-8") as f: f.write(rows_to_ris(kept))
            messagebox.showinfo("完成","已导出保留项 RIS。")

    def export_core_bundle(self):
        kept = [r for r in self.rows if r.get("Decision") == "保留"]
        if not kept:
            messagebox.showinfo("提示","当前没有“保留”文献。"); return
        folder = filedialog.askdirectory()
        if not folder: return
        csv_path = os.path.join(folder,"core_kept.csv"); ris_path = os.path.join(folder,"core_kept.ris"); txt_path = os.path.join(folder,"core_for_chatgpt.txt")
        write_csv(csv_path,kept)
        with open(ris_path,"w",encoding="utf-8") as f: f.write(rows_to_ris(kept))
        lines = ["请帮我分析以下保留文献，输出主题分类、核心研究问题、值得优先精读的文献。",""]
        for i,r in enumerate(kept[:50],1):
            lines.append(f"{i}. PMID={r.get('PMID','')} | Year={r.get('Year','')} | Journal={r.get('Journal','')}")
            lines.append(f"Title: {r.get('Title','')}")
            lines.append(f"Abstract: {r.get('Abstract','')}")
            lines.append("")
        with open(txt_path,"w",encoding="utf-8") as f: f.write("\n".join(lines))
        messagebox.showinfo("完成", f"已导出核心文献包到：\n{folder}")

if __name__ == "__main__":
    app = App()
    app.mainloop()

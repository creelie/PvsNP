"""Build the arXiv catalogue of literature on P versus NP and circuit lower bounds.

Queries the public arXiv API (export.arxiv.org) for each search phrase below,
merges the results by arXiv identifier and writes arxiv_catalogue.csv with
one row per paper: id, first version date, primary category, title, authors,
the search phrases that matched, and the DOI when arXiv records one.

Usage: python3 fetch_arxiv.py [output.csv]
"""
import csv
import sys
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET

QUERIES = {
    "P vs NP": 'ti:"P versus NP" OR abs:"P versus NP" OR ti:"P vs NP" OR abs:"P vs NP" OR ti:"P vs. NP" OR abs:"P vs. NP" OR abs:"P != NP" OR abs:"P = NP"',
    "circuit lower bound": 'abs:circuit AND abs:lower AND abs:bound AND (cat:cs.CC OR cat:cs.DS OR cat:cs.DM)',
    "natural proofs": 'abs:natural AND abs:proofs AND cat:cs.CC',
    "relativization": '(abs:relativization OR abs:relativizing OR abs:relativize) AND cat:cs.CC',
    "algebrization": 'abs:algebrization OR abs:algebrizing OR abs:algebrize',
    "geometric complexity theory": 'abs:geometric AND abs:complexity AND abs:theory AND (abs:permanent OR abs:determinant OR abs:orbit OR abs:obstructions)',
    "hardness magnification": 'abs:hardness AND abs:magnification',
    "MCSP": 'abs:minimum AND abs:circuit AND abs:size AND abs:problem',
    "proof complexity": 'abs:proof AND abs:complexity AND abs:lower AND abs:bound AND (cat:cs.CC OR cat:cs.LO OR cat:math.LO)',
    "ETH/SETH": '(abs:exponential AND abs:time AND abs:hypothesis) OR abs:SETH',
    "threshold circuits": 'abs:threshold AND abs:circuits AND (cat:cs.CC OR cat:cs.DM)',
    "circuit satisfiability algorithm": 'abs:satisfiability AND abs:circuits AND abs:algorithm AND cat:cs.CC',
    "formula lower bound": 'abs:formula AND abs:lower AND abs:bound AND cat:cs.CC',
    "ACC": 'abs:ACC AND cat:cs.CC',
    "VP vs VNP": 'abs:VNP',
    "meta-complexity": 'abs:meta-complexity OR abs:metacomplexity OR (abs:Kolmogorov AND abs:complexity AND cat:cs.CC)',
    "range avoidance": 'abs:range AND abs:avoidance AND cat:cs.CC',
    "PCP": '(abs:PCP OR (abs:probabilistically AND abs:checkable)) AND cat:cs.CC',
    "tensor network contraction": 'abs:tensor AND abs:network AND abs:contraction AND (cat:cs.CC OR cat:cs.DS)',
}
API = "https://export.arxiv.org/api/query"
NS = {"a": "http://www.w3.org/2005/Atom", "arxiv": "http://arxiv.org/schemas/atom"}


def fetch(query, start, size):
    params = urllib.parse.urlencode({"search_query": query, "start": start,
                                     "max_results": size, "sortBy": "submittedDate",
                                     "sortOrder": "ascending"})
    for attempt in range(5):
        try:
            with urllib.request.urlopen(API + "?" + params, timeout=120) as r:
                return ET.fromstring(r.read())
        except Exception as exc:  # network hiccup: wait and retry
            print("retry", attempt, exc, file=sys.stderr)
            time.sleep(5 * (attempt + 1))
    raise RuntimeError("arXiv API unreachable")


def main(out):
    papers = {}
    for tag, query in QUERIES.items():
        start, size = 0, 500
        while True:
            root = fetch(query, start, size)
            entries = root.findall("a:entry", NS)
            for e in entries:
                ident = e.find("a:id", NS).text.rsplit("/abs/", 1)[-1]
                ident = ident.rsplit("v", 1)[0] if ident[-1].isdigit() and "v" in ident else ident
                rec = papers.setdefault(ident, {
                    "id": ident,
                    "published": e.find("a:published", NS).text[:10],
                    "category": e.find("arxiv:primary_category", NS).attrib.get("term", ""),
                    "title": " ".join(e.find("a:title", NS).text.split()),
                    "authors": "; ".join(" ".join(a.find("a:name", NS).text.split())
                                         for a in e.findall("a:author", NS)),
                    "doi": (e.find("arxiv:doi", NS).text if e.find("arxiv:doi", NS) is not None else ""),
                    "queries": set(),
                })
                rec["queries"].add(tag)
            print(tag, start, len(entries), file=sys.stderr)
            if len(entries) < size:
                break
            start += size
            time.sleep(3)
        time.sleep(3)
    rows = sorted(papers.values(), key=lambda r: (r["published"], r["id"]))
    with open(out, "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["arxiv_id", "first_version", "primary_category", "title", "authors", "doi", "matched"])
        for r in rows:
            w.writerow([r["id"], r["published"], r["category"], r["title"], r["authors"], r["doi"],
                        "; ".join(sorted(r["queries"]))])
    print(len(rows), "papers", file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "arxiv_catalogue.csv")

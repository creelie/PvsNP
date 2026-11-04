"""Check every DOI of the bibliography against Crossref.

Reads lines 'KEY DOI' from dois.txt and prints, for each, the Crossref title,
container, year and first author, or 'NOT FOUND'.  Writes crossref_records.json.
Usage: python3 check_dois.py dois.txt
"""
import json
import sys
import time
import urllib.parse
import urllib.request


def get(doi):
    url = "https://api.crossref.org/works/" + urllib.parse.quote(doi)
    req = urllib.request.Request(url, headers={"User-Agent": "pvsnp-bibliography-check/1.0"})
    for attempt in range(4):
        try:
            with urllib.request.urlopen(req, timeout=60) as r:
                return json.load(r)["message"]
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return None
            time.sleep(3)
        except Exception:
            time.sleep(3)
    return None


out = {}
for line in open(sys.argv[1]):
    if not line.strip():
        continue
    key, doi = line.split()
    m = get(doi)
    if m is None:
        print(f"{key}\t{doi}\tNOT FOUND")
        out[key] = None
        continue
    year = (m.get("issued", {}).get("date-parts") or [[None]])[0][0]
    au = m.get("author", [])
    first = (au[0].get("family", "") if au else "")
    rec = {"doi": doi, "title": (m.get("title") or [""])[0],
           "container": (m.get("container-title") or [""])[0], "year": year,
           "authors": [a.get("given", "") + " " + a.get("family", "") for a in au],
           "volume": m.get("volume"), "issue": m.get("issue"), "page": m.get("page")}
    out[key] = rec
    print(f"{key}\t{doi}\t{year}\t{first}\t{rec['title'][:80]}\t{rec['container'][:50]}\t{rec['volume']}\t{rec['page']}")
    time.sleep(0.3)
json.dump(out, open("crossref_records.json", "w"), indent=1, ensure_ascii=False)

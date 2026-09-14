import json, sys
d = json.load(open(sys.argv[1], encoding='utf-8'))
for p in d['papers']:
    if sys.argv[2] in (p.get('title') or ''):
        print(json.dumps({k: p.get(k) for k in ('title', 'year', 'authors', 'url', 'doi', 'abstract')}, ensure_ascii=False)[:2500])

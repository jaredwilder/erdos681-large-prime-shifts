import json, sys
d = json.load(open(sys.argv[1], encoding='utf-8'))
for p in d['papers']: print('-', p.get('year') or '', '|', (p.get('title') or '')[:100])

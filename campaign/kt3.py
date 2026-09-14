import json
d = json.load(open("ob_killtable2.json", encoding="utf-8"))
d["id"] = "erdos681_bigbad_kill_table_999997304513_v3"
d["imports"] = "Mathlib"
json.dump(d, open("ob_killtable3.json", "w", encoding="utf-8"), ensure_ascii=False)

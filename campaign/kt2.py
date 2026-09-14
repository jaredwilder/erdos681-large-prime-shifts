import json
d = json.load(open("ob_killtable.json"))
d["id"] = "erdos681_bigbad_kill_table_999997304513_v2"
d["set_options"] = ["set_option maxRecDepth 200000", "set_option maxHeartbeats 0"]
d["proof"] = "⟨by decide +kernel, by decide +kernel, by decide +kernel⟩"
json.dump(d, open("ob_killtable2.json", "w", encoding="utf-8"), ensure_ascii=False)

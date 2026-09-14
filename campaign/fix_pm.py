import json
d = json.load(open('ob_powmod.json', encoding='utf-8'))
old = d['proof'].split('      · have he : e + 1 = 2 * ((e + 1) / 2) + 1')[0]
d['proof'] = old + "      · have he : e + 1 = 2 * ((e + 1) / 2) + 1 := by omega\n        conv_rhs => rw [he, pow_succ, pow_mul']\n        simp [Nat.mul_mod, Nat.pow_mod]"
d['id'] = 'erdos681_powMod_correct_v2'
json.dump(d, open('ob_powmod2.json', 'w', encoding='utf-8'), ensure_ascii=False)

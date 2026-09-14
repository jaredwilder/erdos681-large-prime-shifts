import json
d = json.load(open('ob_bad2999903.json', encoding='utf-8'))
d['id'] = 'erdos681_bad_prime_burst_2999897_2999903'
d['conclusion'] = 'badB 2999897 = true ∧ badB 2999903 = true'
d['proof'] = '⟨by decide, by decide⟩'
json.dump(d, open('ob_burst_pair.json', 'w', encoding='utf-8'), ensure_ascii=False)

src = open("pratt_tree_gen.py").read()
old_start = src.index('    lemmas.append(')
old_end = src.index('header = open')
new = '''    terms = [pf(q) for q in F]
    ex = terms[0] if len(terms) == 1 else "⟨" + ", ".join(terms) + "⟩"
    lemmas.append(
        f"theorem P_{n} : Nat.Prime {n} :=\n"
        f"  lucas_of {n} {a} {F} (by norm_num) (by norm_num)\n"
        f"    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact {ex})\n"
        f"    (by norm_num) (by decide) (by decide)\n")
'''
src = src[:old_start] + new + src[old_end:]
open("pratt_tree_gen2.py", "w").write(src)

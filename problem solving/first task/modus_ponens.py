def modus_ponens(a: Expression, b: Expression) -> Expression:
    if a.empty() or b.empty():
        return Expression()
    if b[0].op != Operation.IMPLICATION:
        return Expression()
    substitution = {}
    if not unification(a, b.subtree_copy(b.subtree(0).left()), substitution):
        return Expression()
    result = b.subtree_copy(0)
    result.change_variables(a.max_value() + 1)
    vars = result.variables()
    for var in vars:
        if var not in substitution:
            continue
        change = substitution[var]
        while change[0].type == 'Variable' and change[0].value in substitution:
            should_negate = change[0].op == Operation.NEGATION
            change = substitution[change[0].value]
            if should_negate:
                change.negation()
        result.replace(var, change)
    result = result.subtree_copy(result.subtree(0).right())
    result.normalize()
    return result
def add_constraint(term: Term, substitution: Expression, sub: Dict[int, Expression]) -> bool:
    if substitution[0].type == 'Function' and substitution.contains(term):
        return False
    sub[term.value] = substitution
    return True

def unification(left: Expression, right: Expression, substitution: Dict[int, Expression]) -> bool:
    sub = {}
    right.change_variables(left.max_value() + 1)
    v = right.max_value() + 1
    from collections import deque
    expression = deque()
    expression.append((left.subtree(0).self(), right.subtree(0).self()))
    while expression:
        left_idx, right_idx = expression.popleft()
        left_term = left[left_idx]
        right_term = right[right_idx]
        if left_term.type == 'Function' and right_term.type == 'Function':
            if left_term.op != right_term.op:
                return False
            expression.append((left.subtree(left_idx).left(), right.subtree(right_idx).left()))
            expression.append((left.subtree(left_idx).right(), right.subtree(right_idx).right()))
            continue
        lhs = left.subtree_copy(left_idx)
        rhs = right.subtree_copy(right_idx)
        while lhs[0].type == 'Variable' and lhs[0].value in sub:
            should_negate = lhs[0].op == Operation.NEGATION
            lhs = sub[lhs[0].value]
            if should_negate:
                lhs.negation()
        while rhs[0].type == 'Variable' and rhs[0].value in sub:
            should_negate = rhs[0].op == Operation.NEGATION
            rhs = sub[rhs[0].value]
            if should_negate:
                rhs.negation()
        if lhs[0].type == 'Constant' and rhs[0].type == 'Constant':
            if lhs[0] != rhs[0]:
                return False
            continue
        if lhs[0].type == 'Constant' and rhs[0].type == 'Variable':
            if rhs[0].op == Operation.NEGATION:
                lhs[0].op = Operation.NEGATION if lhs[0].op != Operation.NEGATION else Operation.NOP
            if not add_constraint(rhs[0], lhs, sub):
                return False
            continue
        if lhs[0].type == 'Variable' and rhs[0].type == 'Constant':
            if lhs[0].op == Operation.NEGATION:
                rhs[0].op = Operation.NEGATION if rhs[0].op != Operation.NEGATION else Operation.NOP
            if not add_constraint(lhs[0], rhs, sub):
                return False
            continue
        if lhs[0].type == 'Variable' and rhs[0].type == 'Variable':
            if lhs[0].value == rhs[0].value:
                if lhs[0].op != rhs[0].op:
                    return False
                continue
            expr = Expression(Term('Variable', Operation.NEGATION if lhs[0].op == Operation.NEGATION or rhs[0].op == Operation.NEGATION else Operation.NOP, v))
            v += 1
            neg_expr = expr.subtree_copy(0)
            neg_expr.negation()
            if lhs[0].op == Operation.NEGATION:
                add_constraint(lhs[0], neg_expr, sub)
            else:
                add_constraint(lhs[0], expr, sub)
            if rhs[0].op == Operation.NEGATION:
                add_constraint(rhs[0], neg_expr, sub)
            else:
                add_constraint(rhs[0], expr, sub)
            continue
        if lhs[0].type == 'Function':
            if rhs[0].type != 'Variable':
                return False
            if rhs[0].op == Operation.NEGATION:
                lhs.negation()
            if not add_constraint(rhs[0], lhs, sub):
                return False
            continue
        if rhs[0].type == 'Function':
            if lhs[0].type != 'Variable':
                return False
            if lhs[0].op == Operation.NEGATION:
                rhs.negation()
            if not add_constraint(lhs[0], rhs, sub):
                return False
            continue
        return False
    for v, expr in sub.items():
        if expr[0].type != 'Function':
            continue
        for var in expr.variables():
            if var in sub:
                replacement = sub[var]
                while replacement[0].type == 'Variable' and replacement[0].value in sub:
                    should_negate = replacement[0].op == Operation.NEGATION
                    replacement = sub[replacement[0].value]
                    if should_negate:
                        replacement.negation()
                if replacement.contains(Term('Variable', Operation.NOP, var)):
                    return False
                expr.replace(var, replacement)
    substitution.update(sub)
    return True

def is_equal(left: Expression, right: Expression) -> bool:
    if len(left) != len(right):
        return False
    if left[0].op != right[0].op:
        return False
    left.normalize()
    right.normalize()
    return left.equals(right)

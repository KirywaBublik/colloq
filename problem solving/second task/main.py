from functools import lru_cache

# Data structures
Variable = str
Expression = str

# Axioms
AXIOMS = [
    "(A → (B → A))",
    "((A → (B → C)) → ((A → B) → (A → C)))",
    "(((¬B) → (¬A)) → (((¬B) → A) → B))"
]


# Rules
def modus_ponens(expr1, expr2):
    if expr1.startswith("(") and expr1.endswith(")"):
        antecedent = expr1[1:expr1.index("→")]
        consequent = expr1[expr1.index("→") + 2:-1]
        if antecedent == expr2:
            return consequent
    return None


def modus_tollens(expr1, expr2):
    if expr1.startswith("(") and expr1.endswith(")") and expr2.startswith("¬"):
        consequent = expr1[expr1.index("→") + 2:-1]
        negated_expr = expr2[1:]
        if consequent == negated_expr:
            return "¬" + expr1[1:expr1.index("→")]
    return None


def disjunctive_syllogism(expr1, expr2):
    if expr1.startswith("¬") and expr2.startswith("(") and expr2.endswith(")"):
        negated_expr = expr1[1:]
        antecedent = expr2[1:expr2.index("→")]
        consequent = expr2[expr2.index("→") + 2:-1]
        if antecedent == negated_expr:
            return consequent
    return None


def hypothetical_syllogism(expr1, expr2):
    if expr1.startswith("(") and expr1.endswith(")") and expr2.startswith("(") and expr2.endswith(")"):
        antecedent1 = expr1[1:expr1.index("→")]
        consequent1 = expr1[expr1.index("→") + 2:-1]
        antecedent2 = expr2[1:expr2.index("→")]
        consequent2 = expr2[expr2.index("→") + 2:-1]
        if consequent1 == antecedent2:
            return f"({antecedent1} → {consequent2})"
    return None


@lru_cache(maxsize=None)
def prove(target):
    proved = AXIOMS.copy()

    while target not in proved:
        new_proofs = []

        for expr1 in proved:
            for expr2 in proved:
                new_proof = (
                        modus_ponens(expr1, expr2) or
                        modus_tollens(expr1, expr2) or
                        disjunctive_syllogism(expr1, expr2) or
                        hypothetical_syllogism(expr1, expr2)
                )

                if new_proof and new_proof not in proved:
                    new_proofs.append(new_proof)

        if not new_proofs:
            return False

        proved.update(new_proofs)

    return True


# Example usage
A = "A"
B = "B"
target = f"({A} → {B})"
result = prove(target)

print(f"Target: {target}")
print(f"Proved: {'Yes' if result else 'No'}")

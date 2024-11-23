import sys
from constructor import Expression
from algorithm import Solver

def main():
    expression_str = input()
    target = Expression(expression_str)
    target.standardize()
    target.make_permanent()

    axioms = [
        Expression("a>(b>a)"),
        Expression("(a>(b>c))>((a>b)>(a>c))"),
        Expression("(!a>!b)>((!a>b)>a)"),
        Expression("a>(!a>b)"),
        Expression("a*b>a"),
        Expression("a*b>b"),
        Expression("a>(b>(a*b))"),
        Expression("a>a")
    ]

    print(f"your input: {target}", file=sys.stderr)

    solve = Solver(axioms, target, 10000)
    solve.solve()

    print(solve.thought_chain())
    return 0

if __name__ == "__main__":
    import sys
    sys.exit(main())

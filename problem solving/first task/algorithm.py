import time
import re
import sys
from collections import deque
from typing import Set
from enum import Enum, auto
from constructor import Expression
INVALID_INDEX = -1
from typing import List, Dict, Tuple, Union

class Operation(Enum):
    NOP = auto()
    NEGATION = auto()
    IMPLICATION = auto()
    DISJUNCTION = auto()
    CONJUNCTION = auto()
    XOR = auto()
    EQUIVALENT = auto()


def is_equal(left: Expression, right: Expression) -> bool:
    # O(1) checks
    if len(left) != len(right):
        return False

    if left[0].op != right[0].op:
        return False

    left.normalize()
    right.normalize()

    return left.equals(right)


def priority(op: Operation) -> int:
    priorities = {
        Operation.NOP: 0,
        Operation.NEGATION: 5,
        Operation.IMPLICATION: 1,
        Operation.DISJUNCTION: 3,
        Operation.CONJUNCTION: 4,
        Operation.XOR: 2,
        Operation.EQUIVALENT: 2
    }
    return priorities[op]

def is_commutative(op: Operation) -> bool:
    return op in {Operation.DISJUNCTION, Operation.CONJUNCTION, Operation.XOR, Operation.EQUIVALENT}

def opposite(op: Operation) -> Operation:
    opposite_map = {
        Operation.NOP: Operation.NOP,
        Operation.NEGATION: Operation.NEGATION,
        Operation.DISJUNCTION: Operation.CONJUNCTION,
        Operation.CONJUNCTION: Operation.IMPLICATION,
        Operation.IMPLICATION: Operation.CONJUNCTION,
        Operation.XOR: Operation.EQUIVALENT,
        Operation.EQUIVALENT: Operation.XOR
    }
    return opposite_map[op]

class Relation:
    def __init__(self, self_idx=INVALID_INDEX, left=INVALID_INDEX,
                 right=INVALID_INDEX, parent=INVALID_INDEX):
        self.refs = [self_idx, left, right, parent]

    def self(self):
        return self.refs[0]

    def left(self):
        return self.refs[1]

    def right(self):
        return self.refs[2]

    def parent(self):
        return self.refs[3]

def increase_index(index: int, offset: int) -> int:
    return INVALID_INDEX if index == INVALID_INDEX else index + offset

def decrease_index(index: int, offset: int) -> int:
    return INVALID_INDEX if index == INVALID_INDEX or offset > index else index - offset


class Term:
    def __init__(self, term_type, op=Operation.NOP, value=0):
        self.type = term_type
        self.op = op
        self.value = value

    def to_string(self) -> str:
        if self.type == 'None':
            return 'None'
        if self.type == 'Function':
            operation_dict = {
                Operation.NOP: "NOP",
                Operation.NEGATION: "!",
                Operation.DISJUNCTION: "|",
                Operation.CONJUNCTION: "*",
                Operation.IMPLICATION: ">",
                Operation.XOR: "+",
                Operation.EQUIVALENT: "="
            }
            return operation_dict[self.op]
        else:
            result = '!' if self.op == Operation.NEGATION else ''
            if self.type == 'Constant':
                suitable_constant = chr(abs(self.value) - 1 + ord('a'))
                result += suitable_constant
            else:
                suitable_constant = chr(abs(self.value) - 1 + ord('A'))
                result += suitable_constant
            return result

    def __eq__(self, other):
        return (self.type == other.type and
                self.op == other.op and
                self.value == other.value)

class Node:
    def __init__(self, term: Term, rel: Relation):
        self.term = term
        self.rel = rel



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

class Solver:
    def __init__(self, axioms: list[Expression], target: Expression, time_limit_ms: int):
        self.known_axioms_: Set[str] = set()
        self.axioms_: List[Expression] = axioms.copy()
        self.produced_ = deque()
        self.targets_ = [target]
        self.time_limit_ = time_limit_ms
        self.ss = ''
        self.dump_ = open("conclusions.txt", "w")

        if len(self.axioms_) < 3:
            raise ValueError("At least 3 axioms are required")

        self.add_expression(modus_ponens(self.axioms_[0], self.axioms_[0]), 100)
        self.add_expression(modus_ponens(self.axioms_[1], self.axioms_[0]), 100)
        self.add_expression(modus_ponens(self.axioms_[3], self.axioms_[1]), 100)
        self.add_expression(modus_ponens(self.axioms_[4], self.axioms_[1]), 100)
        self.add_expression(modus_ponens(self.axioms_[2], self.axioms_[5]), 100)
        self.add_expression(modus_ponens(self.axioms_[6], self.axioms_[6]), 100)
        self.add_expression(modus_ponens(self.axioms_[7], self.axioms_[8]), 100)
        self.add_expression(modus_ponens(self.axioms_[3], self.axioms_[9]), 100)

        self.dump_.write(f"{self.axioms_[3]} mp {self.axioms_[0]} {self.axioms_[0]}\n")
        self.dump_.write(f"{self.axioms_[4]} mp {self.axioms_[1]} {self.axioms_[0]}\n")
        self.dump_.write(f"{self.axioms_[5]} mp {self.axioms_[3]} {self.axioms_[1]}\n")
        self.dump_.write(f"{self.axioms_[6]} mp {self.axioms_[4]} {self.axioms_[1]}\n")
        self.dump_.write(f"{self.axioms_[7]} mp {self.axioms_[2]} {self.axioms_[5]}\n")
        self.dump_.write(f"{self.axioms_[8]} mp {self.axioms_[6]} {self.axioms_[5]}\n")
        self.dump_.write(f"{self.axioms_[9]} mp {self.axioms_[7]} {self.axioms_[8]}\n")
        self.dump_.write(f"{self.axioms_[10]} mp {self.axioms_[3]} {self.axioms_[9]}\n")

        self.axioms_ = self.axioms_[:3]

    def is_target_proved_by(self, expression: Expression) -> bool:
        if expression.empty():
            return False
        for target in self.targets_:
            if is_equal(target, expression):
                return True
        return False

    def deduction_theorem_decomposition(self, expression: Expression) -> bool:
        if expression.empty():
            return False
        if expression[0].op != Operation.IMPLICATION:
            return False
        self.axioms_.append(expression.subtree_copy(expression.subtree(0).left()))
        self.targets_.append(expression.subtree_copy(expression.subtree(0).right()))
        return True

    def add_expression(self, expression: Expression, max_len: int) -> bool:
        if 2 * max_len < len(expression):
            return False
        self.axioms_.append(expression)
        self.known_axioms_.add(expression.to_string())
        return True

    def add_produced(self, expression: Expression, max_len: int) -> bool:
        if expression.empty():
            return False
        if 2 * max_len < len(expression):
            return False
        self.produced_.append(expression)
        return True

    def produce(self, max_len: int):
        if not self.produced_:
            return
        iteration_size = len(self.produced_)
        print(f"iter: {iteration_size}", file=sys.stderr)
        for _ in range(iteration_size):
            if time.time() * 1000 > self.time_limit_:
                break
            expression = self.produced_.popleft()
            if 2 * max_len < len(expression):
                continue
            expression.normalize()
            representation = expression.to_string()
            if representation in self.known_axioms_:
                continue
            self.add_expression(expression, max_len)
            if self.is_target_proved_by(expression):
                return
            for j in range(len(self.axioms_)):
                expr = modus_ponens(self.axioms_[j], self.axioms_[-1])
                if self.add_produced(expr, max_len):
                    self.dump_.write(f"{expr} mp {self.axioms_[j]} {self.axioms_[-1]}\n")
                if self.is_target_proved_by(expr):
                    self.add_expression(expr, max_len)
                    return
                if j + 1 == len(self.axioms_):
                    break
                expr = modus_ponens(self.axioms_[-1], self.axioms_[j])
                if self.add_produced(expr, max_len):
                    self.dump_.write(f"{expr} mp {self.axioms_[-1]} {self.axioms_[j]}\n")
                if self.is_target_proved_by(expr):
                    self.add_expression(expr, max_len)
                    return
        if time.time() * 1000 > self.time_limit_:
            return
        print(f"newly produced: {len(self.produced_)}", file=sys.stderr)

    def solve(self):
        self.ss = ''
        len_target = len(self.targets_[-1])
        while self.deduction_theorem_decomposition(self.targets_[-1]):
            prev = self.targets_[-2]
            curr = self.targets_[-1]
            axiom = self.axioms_[-1]
            self.ss += f"deduction theorem: Γ ⊢ {prev} <=> Γ U {{{axiom}}} ⊢ {curr}\n"
        for axiom in self.axioms_:
            axiom.normalize()
            self.produced_.append(axiom)
            self.dump_.write(f"{axiom}  axiom\n")
        self.produced_.append(Expression("(!a>!b)>(b>a)"))
        self.axioms_.clear()
        self.known_axioms_.clear()
        time_start = time.time() * 1000
        self.time_limit_ = time_start + self.time_limit_
        while time.time() * 1000 < self.time_limit_:
            self.produce(len_target)
            if self.is_target_proved_by(self.axioms_[-1]):
                break
        if not any(self.is_target_proved_by(axiom) for axiom in self.axioms_):
            self.ss += "No proof was found in the time allotted\n"
            return
        proof = None
        target_proved = None
        for axiom in self.axioms_:
            if proof:
                break
            for target in self.targets_:
                if is_equal(target, axiom):
                    proof = axiom
                    target_proved = target
                    break
        self.dump_.flush()
        conclusions_ = {}
        with open("conclusions.txt") as conclusions:
            for line in conclusions:
                parts = line.strip().split()
                expr = parts[0]
                conclusions_[expr] = parts[1:]
        ts = TopoSort(conclusions_, proof.to_string())
        self.ss += ts.to_string()
        substitution = {}
        unification(target_proved, proof, substitution)
        if substitution:
            self.ss += f"change variables: {proof}\n"
            for v, s in substitution.items():
                self.ss += f"{chr(v + ord('A') - 1)} -> {s}\n"
            self.ss += f"proved: {target_proved}\n"

    def thought_chain(self) -> str:
        return self.ss

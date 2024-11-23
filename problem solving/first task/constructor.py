from enum import Enum, auto
import sys
import re
from typing import List, Dict, Tuple, Union
from parser import ExpressionParser

INVALID_INDEX = -1

class Operation(Enum):
    NOP = auto()
    NEGATION = auto()
    IMPLICATION = auto()
    DISJUNCTION = auto()
    CONJUNCTION = auto()
    XOR = auto()
    EQUIVALENT = auto()

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

class Node:
    def __init__(self, term: Term, rel: Relation):
        self.term = term
        self.rel = rel

class Expression:
    def __init__(self, expression=None):
        self.nodes: List[Node] = []
        if expression is None:
            pass
        elif isinstance(expression, str):
            parser = ExpressionParser(expression)
            self.nodes = parser.parse().nodes
        elif isinstance(expression, Term):
            self.nodes.append(Node(expression, Relation(0)))
        elif isinstance(expression, list):
            self.nodes = expression
        elif isinstance(expression, Expression):
            self.nodes = expression.nodes.copy()
        else:
            raise TypeError("Invalid type for Expression initialization")

    def __len__(self):
        return len(self.nodes)

    def __getitem__(self, idx):
        return self.nodes[idx].term

    def empty(self) -> bool:
        return len(self.nodes) == 0

    def equal_to(self, other) -> bool:
        return self.to_string() == other.to_string()

    def variables(self) -> List[int]:
        vars = []
        for node in self.nodes:
            if node.term.type == 'Variable':
                vars.append(node.term.value)
        return vars

    def to_string(self) -> str:
        if self.empty():
            return 'empty'

        def f(out, root, expression):
            if root.self() == INVALID_INDEX:
                return

            brackets = root.parent() != INVALID_INDEX and \
                expression[root.self()].type == 'Function'
            if brackets:
                out.append("(")

            f(out, self.subtree(root.left()), expression)
            out.append(expression[root.self()].to_string())
            f(out, self.subtree(root.right()), expression)

            if brackets:
                out.append(")")

        out = []
        f(out, self.subtree(0), self)
        return ''.join(out)

    def max_value(self) -> int:
        value = 0
        for node in self.nodes:
            if node.term.type == 'Variable':
                value = max(value, node.term.value)
        return value

    def min_value(self) -> int:
        min_value = sys.maxsize
        for node in self.nodes:
            if node.term.type == 'Variable':
                min_value = min(min_value, node.term.value)
        return min_value

    def normalize(self):
        order = []
        remapping = {}

        def traverse(node):
            if node.self() == INVALID_INDEX:
                return
            traverse(self.subtree(node.left()))
            if self.nodes[node.self()].term.type == 'Variable':
                order.append(self.nodes[node.self()].term.value)
            traverse(self.subtree(node.right()))

        traverse(self.subtree(0))

        new_value = 1
        for entry in order:
            if entry in remapping:
                continue
            remapping[entry] = new_value
            new_value += 1

        for node in self.nodes:
            if node.term.type != 'Variable':
                continue
            node.term.value = remapping[node.term.value]

    def standardize(self):
        from collections import deque
        q = deque()
        q.append(0)

        while q:
            node_idx = q.popleft()
            if node_idx == INVALID_INDEX:
                continue
            if self.nodes[node_idx].term.type != 'Function':
                continue
            if self.nodes[node_idx].term.op == Operation.DISJUNCTION:
                self.nodes[node_idx].term.op = Operation.IMPLICATION
                self.negation(self.subtree(node_idx).left())
            if self.has_left(node_idx):
                q.append(self.subtree(node_idx).left())
            if self.has_right(node_idx):
                q.append(self.subtree(node_idx).right())

    def make_permanent(self):
        for node in self.nodes:
            if node.term.type == 'Variable':
                node.term.type = 'Constant'

    def subtree(self, idx) -> Relation:
        return self.nodes[idx].rel if idx >= 0 and idx < len(self.nodes) else Relation()

    def subtree_copy(self, idx) -> 'Expression':
        new_root_index = self.subtree(idx).self()
        nodes = []
        remapping = {}
        i = 0

        def traverse(node):
            nonlocal i
            if node.self() == INVALID_INDEX:
                return
            nodes.append(self.nodes[node.self()])
            remapping[node.self()] = i
            i += 1
            traverse(self.subtree(node.left()))
            traverse(self.subtree(node.right()))

        traverse(self.subtree(new_root_index))

        nodes[0].rel.refs[3] = INVALID_INDEX

        for node in nodes:
            node.rel.refs = [remapping.get(ref, ref) for ref in node.rel.refs]

        return Expression(nodes)

    def contains(self, term: Term) -> bool:
        if term.type not in {'Variable', 'Constant'}:
            return False
        for node in self.nodes:
            if node.term.type in {'Variable', 'Constant'} and node.term.value == term.value:
                return True
        return False

    def has_left(self, idx) -> bool:
        return idx >= 0 and idx < len(self.nodes) and self.nodes[idx].rel.left() != INVALID_INDEX

    def has_right(self, idx) -> bool:
        return idx >= 0 and idx < len(self.nodes) and self.nodes[idx].rel.right() != INVALID_INDEX

    def negation(self, idx=0):
        from collections import deque
        q = deque()
        q.append(idx)

        while q:
            node_idx = q.popleft()
            if node_idx == INVALID_INDEX:
                continue
            if self.nodes[node_idx].term.type != 'Function':
                self.nodes[node_idx].term.op = (
                    Operation.NOP if self.nodes[node_idx].term.op == Operation.NEGATION else Operation.NEGATION
                )
                continue
            self.nodes[node_idx].term.op = opposite(self.nodes[node_idx].term.op)
            if self.nodes[node_idx].term.op in {Operation.IMPLICATION, Operation.CONJUNCTION}:
                q.append(self.subtree(node_idx).right())
            elif self.nodes[node_idx].term.op == Operation.DISJUNCTION:
                q.append(self.subtree(node_idx).left())
                q.append(self.subtree(node_idx).right())

    def change_variables(self, bound):
        bound -= self.min_value()
        for node in self.nodes:
            if node.term.type == 'Variable':
                node.term.value += bound

    def replace(self, value, expression: 'Expression') -> 'Expression':
        if expression.empty():
            return self
        indices = []
        new_expr = expression
        new_expr_neg = new_expr.subtree_copy(0)
        new_expr_neg.negation()
        appropriate_value = 0

        for idx, node in enumerate(self.nodes):
            if node.term.type == 'Variable' and node.term.value == value:
                indices.append(idx)
                appropriate_value = max(abs(appropriate_value), node.term.value)

        if not indices:
            return self

        offset = len(self.nodes)
        appropriate_value += 1
        for entry in indices:
            replacement = new_expr_neg if self.nodes[entry].term.op == Operation.NEGATION else new_expr
            self.nodes[entry] = Node(
                replacement.nodes[0].term,
                Relation(
                    self.nodes[entry].rel.refs[0],
                    increase_index(replacement.subtree(0).left(), offset - 1),
                    increase_index(replacement.subtree(0).right(), offset - 1),
                    self.nodes[entry].rel.refs[3]
                )
            )
            for i in range(1, len(replacement.nodes)):
                node_copy = Node(
                    replacement.nodes[i].term,
                    Relation(*[increase_index(ref, offset - 1) for ref in replacement.nodes[i].rel.refs])
                )
                self.nodes.append(node_copy)
            if self.subtree(entry).left() != INVALID_INDEX:
                self.nodes[self.subtree(entry).left()].rel.refs[3] = entry
            if self.subtree(entry).right() != INVALID_INDEX:
                self.nodes[self.subtree(entry).right()].rel.refs[3] = entry
            offset = len(self.nodes)
        return self

    @staticmethod
    def construct(lhs: 'Expression', op: Operation, rhs: 'Expression') -> 'Expression':
        expression = Expression()
        offset = 1

        expression.nodes.append(Node(
            Term('Function', op),
            Relation(0, 1, 1 + len(lhs))
        ))

        for node in lhs.nodes:
            node_copy = Node(node.term, Relation(*[increase_index(ref, offset) for ref in node.rel.refs]))
            if node_copy.rel.refs[3] == INVALID_INDEX:
                node_copy.rel.refs[3] = 0
            expression.nodes.append(node_copy)

        offset += len(lhs)
        for node in rhs.nodes:
            node_copy = Node(node.term, Relation(*[increase_index(ref, offset) for ref in node.rel.refs]))
            if node_copy.rel.refs[3] == INVALID_INDEX:
                node_copy.rel.refs[3] = 0
            expression.nodes.append(node_copy)

        return expression

    def __lt__(self, other):
        return len(self) > len(other)

    def equals(self, other: 'Expression', var_ignore=True) -> bool:
        if len(self) != len(other):
            return False
        for i in range(len(self)):
            if (self.nodes[i].term.type == 'Function') != (other.nodes[i].term.type == 'Function'):
                return False
            if (self.nodes[i].term.type == 'Function' and
                self.nodes[i].term.op != other.nodes[i].term.op):
                return False
            if not var_ignore and self.nodes[i].term.type != other.nodes[i].term.type:
                return False
            if (self.nodes[i].term.value != other.nodes[i].term.value or
                self.nodes[i].term.op != other.nodes[i].term.op):
                return False
        return True

    def __str__(self):
        return self.to_string()
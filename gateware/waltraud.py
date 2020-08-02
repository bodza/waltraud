import builtins, math, operator, os, subprocess
from collections import defaultdict, Iterable, OrderedDict
from copy import copy
from enum import IntEnum
from functools import reduce
from itertools import combinations

def write_file(filename, contents):
    old_contents = None
    if os.path.exists(filename):
        with open(filename, "r") as f:
            old_contents = f.read()
    if old_contents != contents:
        with open(filename, "w") as f:
            f.write(contents)

def flat_iteration(l):
    for element in l:
        if isinstance(element, Iterable):
            for element2 in flat_iteration(element):
                yield element2
        else:
            yield element

def xdir(obj):
    for attr in dir(obj):
        if attr[:2] != "__" and attr[-2:] != "__":
            yield attr, getattr(obj, attr)

def gcd_multiple(numbers):
    l = len(numbers)
    if l == 1:
        return numbers[0]
    else:
        s = l // 2
        return math.gcd(gcd_multiple(numbers[:s]), gcd_multiple(numbers[s:]))

def log2_int(n, need_pow2=True):
    if n == 0:
        return 0
    r = (n - 1).bit_length()
    if need_pow2 and (1 << r) != n:
        raise ValueError("Not a power of 2")
    return r

def bits_for(n, require_sign_bit=False):
    if n > 0:
        r = log2_int(n + 1, False)
    else:
        require_sign_bit = True
        r = log2_int(-n, False)
    if require_sign_bit:
        r += 1
    return r

# Bit length and signedness of a value.
#
# int, bool
#     Number of bits required to store v or available in v, followed by whether v has a sign bit (included in the bit count).

def value_bits_sign(v):
    def _bitwise_binary_bits_sign(a, b):
        if not a[1] and not b[1]:
            # both operands unsigned
            return max(a[0], b[0]), False
        elif a[1] and b[1]:
            # both operands signed
            return max(a[0], b[0]), True
        elif not a[1] and b[1]:
            # first operand unsigned (add sign bit), second operand signed
            return max(a[0] + 1, b[0]), True
        else:
            # first signed, second operand unsigned (add sign bit)
            return max(a[0], b[0] + 1), True

    if isinstance(v, (Constant, Signal)):
        return v.nbits, v.signed
    elif isinstance(v, (ClockSignal, ResetSignal)):
        return 1, False
    elif isinstance(v, _Operator):
        obs = list(map(value_bits_sign, v.operands))
        if v.op == "+" or v.op == "-":
            if len(obs) == 1:
                if v.op == "-" and not obs[0][1]:
                    return obs[0][0] + 1, True
                else:
                    return obs[0]
            n, s = _bitwise_binary_bits_sign(*obs)
            return n + 1, s
        elif v.op == "*":
            if not obs[0][1] and not obs[1][1]:
                # both operands unsigned
                return obs[0][0] + obs[1][0], False
            elif obs[0][1] and obs[1][1]:
                # both operands signed
                return obs[0][0] + obs[1][0] - 1, True
            else:
                # one operand signed, the other unsigned (add sign bit)
                return obs[0][0] + obs[1][0] + 1 - 1, True
        elif v.op == "<<<":
            if obs[1][1]:
                extra = 2**(obs[1][0] - 1) - 1
            else:
                extra = 2**obs[1][0] - 1
            return obs[0][0] + extra, obs[0][1]
        elif v.op == ">>>":
            if obs[1][1]:
                extra = 2**(obs[1][0] - 1)
            else:
                extra = 0
            return obs[0][0] + extra, obs[0][1]
        elif v.op == "&" or v.op == "^" or v.op == "|":
            return _bitwise_binary_bits_sign(*obs)
        elif (v.op == "<" or v.op == "<=" or v.op == "==" or v.op == "!=" or
              v.op == ">" or v.op == ">="):
            return 1, False
        elif v.op == "~":
            return obs[0]
        elif v.op == "m":
            return _bitwise_binary_bits_sign(obs[1], obs[2])
        else:
            raise TypeError
    elif isinstance(v, _Slice):
        return v.stop - v.start, False
    elif isinstance(v, _Part):
        return v.width, False
    elif isinstance(v, Cat):
        return sum(value_bits_sign(sv)[0] for sv in v.l), False
    elif isinstance(v, Replicate):
        return (value_bits_sign(v.v)[0]) * v.n, False
    elif isinstance(v, _ArrayProxy):
        bsc = list(map(value_bits_sign, v.choices))
        return max(bs[0] for bs in bsc), any(bs[1] for bs in bsc)
    else:
        raise TypeError("Can not calculate bit length of {} {}".format(type(v), v))

# Deterministic Unique IDentifier

class DUID:
    __next_uid = 0
    def __init__(self):
        self.duid = DUID.__next_uid
        DUID.__next_uid += 1

# Base class for operands
#
# Instances of _Value or its subclasses can be operands to arithmetic, comparison, bitwise, and logic operators.
# They can be assigned (eq) or indexed/sliced (using the usual Python indexing and slicing notation).
#
# Values created from integers have the minimum bit width to necessary to represent the integer.

class _Value(DUID):
    def __bool__(self):
        # Special case: Constants and Signals are part of a set or used as dictionary keys, and Python needs to check for equality.
        if isinstance(self, _Operator) and self.op == "==":
            a, b = self.operands
            if isinstance(a, Constant) and isinstance(b, Constant):
                return a.value == b.value
            if isinstance(a, Signal) and isinstance(b, Signal):
                return a is b
            if (isinstance(a, Constant) and isinstance(b, Signal) or isinstance(a, Signal) and isinstance(b, Constant)):
                return False
        raise TypeError("Attempted to convert Eigen value to boolean")

    def __invert__(self):       return _Operator("~", [self])
    def __neg__(self):          return _Operator("-", [self])

    def __add__(self, other):   return _Operator("+", [self, other])
    def __radd__(self, other):  return _Operator("+", [other, self])
    def __sub__(self, other):   return _Operator("-", [self, other])
    def __rsub__(self, other):  return _Operator("-", [other, self])
    def __mul__(self, other):   return _Operator("*", [self, other])
    def __rmul__(self, other):  return _Operator("*", [other, self])

    def __lshift__(self, other): return _Operator("<<<", [self, other])
    def __rlshift__(self, other): return _Operator("<<<", [other, self])
    def __rshift__(self, other): return _Operator(">>>", [self, other])
    def __rrshift__(self, other): return _Operator(">>>", [other, self])

    def __and__(self, other):   return _Operator("&", [self, other])
    def __rand__(self, other):  return _Operator("&", [other, self])
    def __xor__(self, other):   return _Operator("^", [self, other])
    def __rxor__(self, other):  return _Operator("^", [other, self])
    def __or__(self, other):    return _Operator("|", [self, other])
    def __ror__(self, other):   return _Operator("|", [other, self])

    def __lt__(self, other):    return _Operator("<", [self, other])
    def __le__(self, other):    return _Operator("<=", [self, other])
    def __eq__(self, other):    return _Operator("==", [self, other])
    def __ne__(self, other):    return _Operator("!=", [self, other])
    def __gt__(self, other):    return _Operator(">", [self, other])
    def __ge__(self, other):    return _Operator(">=", [self, other])

    def __len__(self):
        return value_bits_sign(self)[0]

    def __getitem__(self, key):
        n = len(self)
        if isinstance(key, int):
            if key >= n:
                raise IndexError
            if key < 0:
                key += n
            return _Slice(self, key, key + 1)
        elif isinstance(key, slice):
            start, stop, step = key.indices(n)
            if step != 1:
                return Cat(self[i] for i in range(start, stop, step))
            return _Slice(self, start, stop)
        else:
            raise TypeError("Cannot use type {} ({}) as key".format(type(key), repr(key)))

    def eq(self, r):
        return _Assign(self, r)

    def part(self, offset, width):
        return _Part(self, wrap(offset), width)

    def __hash__(self):
        raise TypeError("unhashable type: '{}'".format(type(self).__name__))

def wrap(value):
    if isinstance(value, (bool, int)):
        value = Constant(value)
    if not isinstance(value, _Value):
        raise TypeError("Object '{}' of type {} is not a Eigen value".format(value, type(value)))
    return value

class _Operator(_Value):
    def __init__(self, op, operands):
        _Value.__init__(self)
        self.op = op
        self.operands = [wrap(o) for o in operands]

class _Slice(_Value):
    def __init__(self, value, start, stop):
        _Value.__init__(self)
        if not isinstance(start, int) or not isinstance(stop, int):
            raise TypeError("Slice boundaries must be integers")
        self.value = wrap(value)
        self.start = start
        self.stop = stop

class _Part(_Value):
    def __init__(self, value, offset, width):
        _Value.__init__(self)
        if not isinstance(width, int):
            raise TypeError("Cannot use non int width {} ({}) for part".format(width, repr(width)))
        if not isinstance(offset, Constant) and not isinstance(offset, _Value):
            raise TypeError("Must use Value or Constant offset instead of {} ({}) for part".format(offset, repr(offset)))
        self.value = value
        self.offset = offset
        self.width = width

# Concatenate values
#
# Form a compound _Value from several smaller ones by concatenation. The first argument occupies the lower bits of the result.
# The return value can be used on either side of an assignment, that is, the concatenated value can be used as an argument on the RHS or
# as a target on the LHS. If it is used on the LHS, it must solely consist of Signal s, slices of Signal s, and other concatenations
# meeting these properties. The bit length of the return value is the sum of the bit lengths of the arguments:
#
#     len(Cat(args)) == sum(len(arg) for arg in args)
#
# *args : _Values or iterables of _Values, inout
#     _Value s to be concatenated.
#
# Cat, inout
#     Resulting _Value obtained by concatentation.

class Cat(_Value):
    def __init__(self, *args):
        _Value.__init__(self)
        self.l = [wrap(v) for v in flat_iteration(args)]

# Replicate a value
#
# An input value is replicated (repeated) several times to be used on the RHS of assignments:
#
#     len(Replicate(s, n)) == len(s) * n
#
# Replicate, out
#     Replicated value.

class Replicate(_Value):
    def __init__(self, v, n):
        _Value.__init__(self)
        if not isinstance(n, int) or n < 0:
            raise TypeError("Replication count must be a positive integer")
        self.v = wrap(v)
        self.n = n

# A constant, HDL-literal integer _Value
#
# value : int
# bits_sign : int or tuple or None
#     Either an integer bits or a tuple (bits, signed) specifying the number of bits in this Constant and whether
#     it is signed (can represent negative values). bits_sign defaults to the minimum width and signedness of value.

class Constant(_Value):
    def __init__(self, value, bits_sign=None):
        _Value.__init__(self)

        self.value = int(value)
        if bits_sign is None:
            bits_sign = bits_for(self.value), self.value < 0
        elif isinstance(bits_sign, int):
            bits_sign = bits_sign, self.value < 0
        self.nbits, self.signed = bits_sign
        if not isinstance(self.nbits, int) or self.nbits <= 0:
            raise TypeError("Width must be a strictly positive integer")

    def __hash__(self):
        return self.value

# A _Value that can change
#
# The Signal object represents a value that is expected to change in the circuit.
# It does exactly what Verilog's wire and reg and VHDL's signal do.
#
# A Signal can be indexed to access a subset of its bits.
# Negative indices (signal[-1]) and the extended Python slicing notation (signal[start:stop:step]) are supported.
# The indices 0 and -1 are the least and most significant bits respectively.
#
# bits_sign : int or tuple
#     Either an integer bits or a tuple (bits, signed) specifying the number of bits in this Signal and whether
#     it is signed (can represent negative values). signed defaults to False.
# name : str or None
#     Name hint for this signal.
#     Name collisions are automatically resolved by appending integer sequences.
# variable : bool
#     Deprecated.
# reset : int
#     Reset (synchronous) or default (combinatorial) value.
#     When this Signal is assigned to in synchronous context and the corresponding clock domain is reset,
#     the Signal assumes the given value. When this Signal is unassigned in combinatorial context
#     (due to conditional assignments not being taken), the Signal assumes its reset value. Defaults to 0.
# reset_less : bool
#     If True, do not generate reset logic for this Signal in synchronous statements.
#     The reset value is only used as a combinatorial default or as the initial value. Defaults to False.
# min : int or None
# max : int or None
#     If bits_sign is None, the signal bit width and signedness are determined by the integer range given
#     by min (inclusive, defaults to 0) and max (exclusive, defaults to 2).
# related : Signal or None
# attr : set of synthesis attributes

class Signal(_Value):
    def __init__(self, name, bits_sign=None, variable=False, reset=0, reset_less=False, min=None, max=None, related=None, attr=None):
        _Value.__init__(self)

        self.name = name

        # determine number of bits and signedness
        if bits_sign is None:
            if min is None:
                min = 0
            if max is None:
                max = 2
            max -= 1  # make both bounds inclusive
            self.signed = min < 0 or max < 0
            self.nbits = builtins.max(bits_for(min, self.signed), bits_for(max, self.signed))
        else:
            if isinstance(bits_sign, tuple):
                self.nbits, self.signed = bits_sign
            else:
                self.nbits, self.signed = bits_sign, False
        if isinstance(reset, (bool, int)):
            reset = Constant(reset, (self.nbits, self.signed))
        if not isinstance(self.nbits, int) or self.nbits <= 0:
            raise ValueError("Signal width must be a strictly positive integer")
        if attr is None:
            attr = set()

        self.variable = variable  # deprecated
        self.reset = reset
        self.reset_less = reset_less
        self.related = related
        self.attr = attr

    def __setattr__(self, k, v):
        if k == "reset":
            v = wrap(v)
        _Value.__setattr__(self, k, v)

    @classmethod
    def like(cls, other, **kwargs):
        # Create Signal based on another
        kw = dict(bits_sign=value_bits_sign(other))
        if isinstance(other, cls):
            kw.update(variable=other.variable, reset=other.reset.value, reset_less=other.reset_less, related=other.related, attr=set(other.attr))
        kw.update(kwargs)
        return cls(None, **kw)

    def __hash__(self):
        return self.duid

class ClockSignal(_Value):
    def __init__(self, cd="sys"):
        _Value.__init__(self)
        if not isinstance(cd, str):
            raise TypeError("Argument of ClockSignal must be a string")
        self.cd = cd

class ResetSignal(_Value):
    def __init__(self, cd="sys", allow_reset_less=False):
        _Value.__init__(self)
        if not isinstance(cd, str):
            raise TypeError("Argument of ResetSignal must be a string")
        self.cd = cd
        self.allow_reset_less = allow_reset_less

class _Statement:
    pass

class _Assign(_Statement):
    def __init__(self, l, r):
        self.l = wrap(l)
        self.r = wrap(r)

def _check_statement(s):
    if isinstance(s, Iterable):
        return all(_check_statement(ss) for ss in s)
    else:
        return isinstance(s, _Statement)

class If(_Statement):
    def __init__(self, cond, *t):
        if not _check_statement(t):
            raise TypeError("Not all test body objects are Eigen statements")
        self.cond = wrap(cond)
        self.t = list(t)
        self.f = []

    def Else(self, *f):
        if not _check_statement(f):
            raise TypeError("Not all test body objects are Eigen statements")
        _insert_else(self, list(f))
        return self

    def Elif(self, cond, *t):
        _insert_else(self, [If(cond, *t)])
        return self

def _insert_else(obj, clause):
    o = obj
    while o.f:
        o = o.f[0]
    o.f = clause

# Case/Switch statement
#
# test : _Value, in
#     Selector value used to decide which block to execute
# cases : dict
#     Dictionary of cases. The keys are numeric constants to compare with test.
#     The values are statements to be executed the corresponding key matches test.
#     The dictionary may contain a string key "default" to mark a fall-through case that is executed if no other key matches.

class Case(_Statement):
    def __init__(self, test, cases):
        self.test = wrap(test)
        self.cases = dict()
        for k, v in cases.items():
            if isinstance(k, (bool, int)):
                k = Constant(k)
            if (not isinstance(k, Constant) and not (isinstance(k, str) and k == "default")):
                raise TypeError("Case object is not a Eigen constant")
            if not isinstance(v, Iterable):
                v = [v]
            if not _check_statement(v):
                raise TypeError("Not all objects for case {} are Eigen statements".format(k))
            self.cases[k] = v

    # Mark a key as the default case
    #
    # Deletes/substitutes any previously existing default case.
    #
    # key : int, Constant or None
    #     Key to use as default case if no other key matches.
    #     By default, the largest key is the default key.

    def makedefault(self, key=None):
        if key is None:
            for choice in self.cases.keys():
                if (key is None or (isinstance(choice, str) and choice == "default") or choice.value > key.value):
                    key = choice
        if not isinstance(key, str) or key != "default":
            key = wrap(key)
        stmts = self.cases[key]
        del self.cases[key]
        self.cases["default"] = stmts
        return self

class _ArrayProxy(_Value):
    def __init__(self, choices, key):
        _Value.__init__(self)
        self.choices = []
        for c in choices:
            if isinstance(c, (bool, int)):
                c = Constant(c)
            self.choices.append(c)
        self.key = key

    def __getattr__(self, attr):
        return _ArrayProxy([getattr(choice, attr) for choice in self.choices], self.key)

    def __getitem__(self, key):
        return _ArrayProxy([choice.__getitem__(key) for choice in self.choices], self.key)

# Addressable multiplexer
#
# An array is created from an iterable of values and indexed using the usual Python simple indexing notation (no negative indices or slices).
# It can be indexed by numeric constants, _Value s, or Signal s.
#
# The result of indexing the array is a proxy for the entry at the given index that can be used on either RHS or LHS of assignments.
#
# An array can be indexed multiple times.
#
# Multidimensional arrays are supported by packing inner arrays into outer arrays.
#
# values : iterable of ints, _Values, Signals
#     Entries of the array. Each entry can be a numeric constant, a Signal or a Record.
#
# >>> a = Array(range(10))
# >>> b = Signal("...", max=10)
# >>> c = Signal("...", max=10)
# >>> b.eq(a[9 - c])

class Array(list):
    def __getitem__(self, key):
        if isinstance(key, Constant):
            return list.__getitem__(self, key.value)
        elif isinstance(key, _Value):
            return _ArrayProxy(self, key)
        else:
            return list.__getitem__(self, key)

# Synchronous domain
#
# name : str or None
#     Domain name.
# reset_less : bool
#     The domain does not use a reset signal. Registers within this domain are still all initialized to their reset state once,
#     e.g. through Verilog "initial" statements.
#
# clk : Signal, inout
#     The clock for this domain. Can be driven or used to drive other signals (preferably in combinatorial context).
# rst : Signal or None, inout
#     Reset signal for this domain. Can be driven or used to drive.

class ClockDomain:
    def __init__(self, name, reset_less=False):
        self.name = name
        if self.name is None:
            raise ValueError("Cannot extract clock domain name from code, need to specify.")
        if self.name.startswith("cd_"):
            self.name = self.name[3:]
        if self.name[0].isdigit():
            raise ValueError("Clock domain name cannot start with a number.")
        self.clk = Signal(self.name + "_clk")
        if reset_less:
            self.rst = None
        else:
            self.rst = Signal(self.name + "_rst")

    def rename(self, new_name):
        self.name = new_name
        self.clk.name = new_name + "_clk"
        if self.rst is not None:
            self.rst.name = new_name + "_rst"

class _ClockDomainList(list):
    def __getitem__(self, key):
        if isinstance(key, str):
            for cd in self:
                if cd.name == key:
                    return cd
            raise KeyError(key)
        else:
            return list.__getitem__(self, key)

    def __contains__(self, cd_or_name):
        if isinstance(cd_or_name, str):
            for cd in self:
                if cd.name == cd_or_name:
                    return True
            return False
        else:
            return list.__contains__(self, cd_or_name)

(SPECIAL_INPUT, SPECIAL_OUTPUT, SPECIAL_INOUT) = range(3)

class Display(_Statement):
    def __init__(self, s, *args):
        self.s = s
        self.args = args

class Finish(_Statement):
    pass

class _Fragment:
    def __init__(self, comb=None, sync=None, specials=None, clock_domains=None):
        if comb is None: comb = []
        if sync is None: sync = dict()
        if specials is None: specials = set()
        if clock_domains is None: clock_domains = _ClockDomainList()

        self.comb = comb
        self.sync = sync
        self.specials = specials
        self.clock_domains = _ClockDomainList(clock_domains)

    def __add__(self, other):
        newsync = defaultdict(list)
        for k, v in self.sync.items():
            newsync[k] = v[:]
        for k, v in other.sync.items():
            newsync[k].extend(v)
        return _Fragment(self.comb + other.comb, newsync, self.specials | other.specials, self.clock_domains + other.clock_domains)

    def __iadd__(self, other):
        newsync = defaultdict(list)
        for k, v in self.sync.items():
            newsync[k] = v[:]
        for k, v in other.sync.items():
            newsync[k].extend(v)
        self.comb += other.comb
        self.sync = newsync
        self.specials |= other.specials
        self.clock_domains += other.clock_domains
        return self

class NodeVisitor:
    def visit(self, node):
        if isinstance(node, Constant):      self.visit_Constant(node)
        elif isinstance(node, Signal):      self.visit_Signal(node)
        elif isinstance(node, ClockSignal): self.visit_ClockSignal(node)
        elif isinstance(node, ResetSignal): self.visit_ResetSignal(node)
        elif isinstance(node, _Operator):   self.visit_Operator(node)
        elif isinstance(node, _Slice):      self.visit_Slice(node)
        elif isinstance(node, Cat):         self.visit_Cat(node)
        elif isinstance(node, Replicate):   self.visit_Replicate(node)
        elif isinstance(node, _Assign):     self.visit_Assign(node)
        elif isinstance(node, If):          self.visit_If(node)
        elif isinstance(node, Case):        self.visit_Case(node)
        elif isinstance(node, _Fragment):   self.visit_Fragment(node)
        elif isinstance(node, (list, tuple)): self.visit_statements(node)
        elif isinstance(node, dict):        self.visit_clock_domains(node)
        elif isinstance(node, _ArrayProxy): self.visit_ArrayProxy(node)
        else:                               self.visit_unknown(node)

    def visit_Constant(self, node):    pass
    def visit_Signal(self, node):      pass
    def visit_ClockSignal(self, node): pass
    def visit_ResetSignal(self, node): pass

    def visit_Operator(self, node):
        for o in node.operands:
            self.visit(o)

    def visit_Slice(self, node):
        self.visit(node.value)

    def visit_Part(self, node):
        self.visit(node.value)
        self.visit(node.offset)

    def visit_Cat(self, node):
        for e in node.l:
            self.visit(e)

    def visit_Replicate(self, node):
        self.visit(node.v)

    def visit_Assign(self, node):
        self.visit(node.l)
        self.visit(node.r)

    def visit_If(self, node):
        self.visit(node.cond)
        self.visit(node.t)
        self.visit(node.f)

    def visit_Case(self, node):
        self.visit(node.test)
        for v, statements in sorted(node.cases.items(), key=lambda x: -1 if isinstance(x[0], str) and x[0] == "default" else x[0].duid):
            self.visit(statements)

    def visit_Fragment(self, node):
        self.visit(node.comb)
        self.visit(node.sync)

    def visit_statements(self, node):
        for statement in node:
            self.visit(statement)

    def visit_clock_domains(self, node):
        for clockname, statements in sorted(node.items(), key=operator.itemgetter(0)):
            self.visit(statements)

    def visit_ArrayProxy(self, node):
        for choice in node.choices:
            self.visit(choice)
        self.visit(node.key)

    def visit_unknown(self, node):
        pass

# Default methods always copy the node, except for:
# - Signals, ClockSignals and ResetSignals
# - Unknown objects
# - All fragment fields except comb and sync
# In those cases, the original node is returned unchanged.

class NodeTransformer:
    def visit(self, node):
        if isinstance(node, Constant):      return self.visit_Constant(node)
        elif isinstance(node, Signal):      return self.visit_Signal(node)
        elif isinstance(node, ClockSignal): return self.visit_ClockSignal(node)
        elif isinstance(node, ResetSignal): return self.visit_ResetSignal(node)
        elif isinstance(node, _Operator):   return self.visit_Operator(node)
        elif isinstance(node, _Slice):      return self.visit_Slice(node)
        elif isinstance(node, _Part):       return self.visit_Part(node)
        elif isinstance(node, Cat):         return self.visit_Cat(node)
        elif isinstance(node, Replicate):   return self.visit_Replicate(node)
        elif isinstance(node, _Assign):     return self.visit_Assign(node)
        elif isinstance(node, If):          return self.visit_If(node)
        elif isinstance(node, Case):        return self.visit_Case(node)
        elif isinstance(node, _Fragment):   return self.visit_Fragment(node)
        elif isinstance(node, (list, tuple)): return self.visit_statements(node)
        elif isinstance(node, dict):        return self.visit_clock_domains(node)
        elif isinstance(node, _ArrayProxy): return self.visit_ArrayProxy(node)
        else:                               return self.visit_unknown(node)

    def visit_Constant(self, node):    return node
    def visit_Signal(self, node):      return node
    def visit_ClockSignal(self, node): return node
    def visit_ResetSignal(self, node): return node

    def visit_Operator(self, node):
        return _Operator(node.op, [self.visit(o) for o in node.operands])

    def visit_Slice(self, node):
        return _Slice(self.visit(node.value), node.start, node.stop)

    def visit_Part(self, node):
        return _Part(self.visit(node.value), self.visit(node.offset), node.width)

    def visit_Cat(self, node):
        return Cat(*[self.visit(e) for e in node.l])

    def visit_Replicate(self, node):
        return Replicate(self.visit(node.v), node.n)

    def visit_Assign(self, node):
        return _Assign(self.visit(node.l), self.visit(node.r))

    def visit_If(self, node):
        r = If(self.visit(node.cond))
        r.t = self.visit(node.t)
        r.f = self.visit(node.f)
        return r

    def visit_Case(self, node):
        cases = {v: self.visit(statements) for v, statements in sorted(node.cases.items(), key=lambda x: -1 if isinstance(x[0], str) and x[0] == "default" else x[0].duid)}
        r = Case(self.visit(node.test), cases)
        return r

    def visit_Fragment(self, node):
        r = copy(node)
        r.comb = self.visit(node.comb)
        r.sync = self.visit(node.sync)
        return r

    # NOTE: this will always return a list, even if node is a tuple
    def visit_statements(self, node):
        return [self.visit(statement) for statement in node]

    def visit_clock_domains(self, node):
        return {clockname: self.visit(statements) for clockname, statements in sorted(node.items(), key=operator.itemgetter(0))}

    def visit_ArrayProxy(self, node):
        return _ArrayProxy([self.visit(choice) for choice in node.choices], self.visit(node.key))

    def visit_unknown(self, node):
        return node

class _SignalLister(NodeVisitor):
    def __init__(self):
        self.output_list = set()

    def visit_Signal(self, node):
        self.output_list.add(node)

class _TargetLister(NodeVisitor):
    def __init__(self):
        self.output_list = set()
        self.target_context = False

    def visit_Signal(self, node):
        if self.target_context:
            self.output_list.add(node)

    def visit_Assign(self, node):
        self.target_context = True
        self.visit(node.l)
        self.target_context = False

    def visit_ArrayProxy(self, node):
        for choice in node.choices:
            self.visit(choice)

class _InputLister(NodeVisitor):
    def __init__(self):
        self.output_list = set()

    def visit_Signal(self, node):
        self.output_list.add(node)

    def visit_Assign(self, node):
        self.visit(node.r)

def list_signals(node):
    lister = _SignalLister()
    lister.visit(node)
    return lister.output_list

def list_targets(node):
    lister = _TargetLister()
    lister.visit(node)
    return lister.output_list

def list_inputs(node):
    lister = _InputLister()
    lister.visit(node)
    return lister.output_list

def _resort_statements(ol):
    return [statement for i, statement in sorted(ol, key=lambda x: x[0])]

def group_by_targets(sl):
    groups = []
    seen = set()
    for order, stmt in enumerate(flat_iteration(sl)):
        targets = set(list_targets(stmt))
        group = [(order, stmt)]
        disjoint = targets.isdisjoint(seen)
        seen |= targets
        if not disjoint:
            groups, old_groups = [], groups
            for old_targets, old_group in old_groups:
                if targets.isdisjoint(old_targets):
                    groups.append((old_targets, old_group))
                else:
                    targets |= old_targets
                    group += old_group
        groups.append((targets, group))
    return [(targets, _resort_statements(stmts)) for targets, stmts in groups]

def list_special_ios(f, ins, outs, inouts):
    r = set()
    for special in f.specials:
        r |= special.list_ios(ins, outs, inouts)
    return r

class _ClockDomainLister(NodeVisitor):
    def __init__(self):
        self.clock_domains = set()

    def visit_ClockSignal(self, node):
        self.clock_domains.add(node.cd)

    def visit_ResetSignal(self, node):
        self.clock_domains.add(node.cd)

    def visit_clock_domains(self, node):
        for clockname, statements in node.items():
            self.clock_domains.add(clockname)
            self.visit(statements)

def list_clock_domains_expr(f):
    cdl = _ClockDomainLister()
    cdl.visit(f)
    return cdl.clock_domains

def list_clock_domains(f):
    r = list_clock_domains_expr(f)
    for special in f.specials:
        r |= special.list_clock_domains()
    for cd in f.clock_domains:
        r.add(cd.name)
    return r

def is_variable(node):
    if isinstance(node, Signal):
        return node.variable
    elif isinstance(node, _Slice):
        return is_variable(node.value)
    elif isinstance(node, _Part):
        if is_variable(node.offset) != is_variable(node.value):
            raise TypeError
        return is_variable(node.value)
    elif isinstance(node, Cat):
        arevars = list(map(is_variable, node.l))
        r = arevars[0]
        for x in arevars:
            if x != r:
                raise TypeError
        return r
    else:
        raise TypeError

def generate_reset(rst, sl):
    targets = list_targets(sl)
    return [t.eq(t.reset) for t in sorted(targets, key=lambda x: x.duid) if not t.reset_less]

def insert_reset(rst, sl):
    return sl + [If(rst, *generate_reset(rst, sl))]

def insert_resets(f):
    newsync = dict()
    for k, v in f.sync.items():
        if f.clock_domains[k].rst is not None:
            newsync[k] = insert_reset(ResetSignal(k), v)
        else:
            newsync[k] = v
    f.sync = newsync

class _Lowerer(NodeTransformer):
    def __init__(self):
        self.target_context = False
        self.extra_stmts = []
        self.comb = []

    def visit_Assign(self, node):
        old_target_context, old_extra_stmts = self.target_context, self.extra_stmts
        self.extra_stmts = []

        self.target_context = True
        lhs = self.visit(node.l)
        self.target_context = False
        rhs = self.visit(node.r)
        r = _Assign(lhs, rhs)
        if self.extra_stmts:
            r = [r] + self.extra_stmts

        self.target_context, self.extra_stmts = old_target_context, old_extra_stmts
        return r

# Basics are FHDL structure elements that back-ends are not required to support
# but can be expressed in terms of other elements (lowered) before conversion.

class _BasicLowerer(_Lowerer):
    def __init__(self, clock_domains):
        self.clock_domains = clock_domains
        _Lowerer.__init__(self)

    def visit_ArrayProxy(self, node):
        # TODO: rewrite without variables
        array_muxed = Signal("array_muxed", value_bits_sign(node), variable=True)
        if self.target_context:
            k = self.visit(node.key)
            cases = {}
            for n, choice in enumerate(node.choices):
                cases[n] = [self.visit_Assign(_Assign(choice, array_muxed))]
            self.extra_stmts.append(Case(k, cases).makedefault())
        else:
            cases = dict((n, _Assign(array_muxed, self.visit(choice))) for n, choice in enumerate(node.choices))
            self.comb.append(Case(self.visit(node.key), cases).makedefault())
        return array_muxed

    def visit_ClockSignal(self, node):
        return self.clock_domains[node.cd].clk

    def visit_ResetSignal(self, node):
        rst = self.clock_domains[node.cd].rst
        if rst is None:
            if node.allow_reset_less:
                return 0
            else:
                raise ValueError("Attempted to get reset signal of resetless domain '{}'".format(node.cd))
        else:
            return rst

class _ComplexSliceLowerer(_Lowerer):
    def visit_Slice(self, node):
        if not isinstance(node.value, Signal):
            slice_proxy = Signal("slice_proxy", value_bits_sign(node.value))
            if self.target_context:
                a = _Assign(node.value, slice_proxy)
            else:
                a = _Assign(slice_proxy, node.value)
            self.comb.append(self.visit_Assign(a))
            node = _Slice(slice_proxy, node.start, node.stop)
        return NodeTransformer.visit_Slice(self, node)

def _apply_lowerer(l, f):
    f = l.visit(f)
    f.comb += l.comb

    for special in sorted(f.specials, key=lambda s: s.duid):
        for obj, attr, direction in special.iter_expressions():
            if direction != SPECIAL_INOUT:
                # inouts are only supported by Eigen when connected directly to top-level in this case, they are Signal and never need lowering
                l.comb = []
                l.target_context = direction != SPECIAL_INPUT
                l.extra_stmts = []
                expr = getattr(obj, attr)
                expr = l.visit(expr)
                setattr(obj, attr, expr)
                f.comb += l.comb + l.extra_stmts

    return f

def lower_basics(f):
    return _apply_lowerer(_BasicLowerer(f.clock_domains), f)

def lower_complex_slices(f):
    return _apply_lowerer(_ComplexSliceLowerer(), f)

class _ClockDomainRenamer(NodeVisitor):
    def __init__(self, old, new):
        self.old = old
        self.new = new

    def visit_ClockSignal(self, node):
        if node.cd == self.old:
            node.cd = self.new

    def visit_ResetSignal(self, node):
        if node.cd == self.old:
            node.cd = self.new

def rename_clock_domain_expr(f, old, new):
    _ClockDomainRenamer(old, new).visit(f)

def rename_clock_domain(f, old, new):
    rename_clock_domain_expr(f, old, new)
    if new != old:
        if old in f.sync:
            if new in f.sync:
                f.sync[new].extend(f.sync[old])
            else:
                f.sync[new] = f.sync[old]
            del f.sync[old]
    for special in f.specials:
        special.rename_clock_domain(old, new)
    try:
        cd = f.clock_domains[old]
    except KeyError:
        pass
    else:
        cd.rename(new)

def call_special_classmethod(overrides, obj, method, *args, **kwargs):
    cl = obj.__class__
    if cl in overrides:
        cl = overrides[cl]
    if hasattr(cl, method):
        return getattr(cl, method)(obj, *args, **kwargs)
    else:
        return None

def _lower_specials_step(overrides, specials):
    f = _Fragment()
    lowered_specials = set()
    for special in sorted(specials, key=lambda x: x.duid):
        impl = call_special_classmethod(overrides, special, "lower")
        if impl is not None:
            f += impl.get_fragment()
            lowered_specials.add(special)
    return f, lowered_specials

def lower_specials(overrides, f):
    lowered_specials = set()
    while True:
        fs, lowered_specials_step = _lower_specials_step(overrides, f.specials)
        f += fs
        if lowered_specials_step:
            lowered_specials |= lowered_specials_step
            f.specials -= lowered_specials_step
        else:
            break
    return f, lowered_specials

class FinalizeError(Exception):
    pass

def _flat_list(e):
    if isinstance(e, Iterable):
        return flat_iteration(e)
    else:
        return [e]

class _ModuleProxy:
    def __init__(self, fm):
        object.__setattr__(self, "_fm", fm)

class _ModuleComb(_ModuleProxy):
    def __iadd__(self, other):
        self._fm._fragment.comb += _flat_list(other)
        return self

def _cd_append(d, key, statements):
    try:
        l = d[key]
    except KeyError:
        l = []
        d[key] = l
    l += _flat_list(statements)

class _ModuleSyncCD:
    def __init__(self, fm, cd):
        self._fm = fm
        self._cd = cd

    def __iadd__(self, other):
        _cd_append(self._fm._fragment.sync, self._cd, other)
        return self

class _ModuleSync(_ModuleProxy):
    def __iadd__(self, other):
        _cd_append(self._fm._fragment.sync, "sys", other)
        return self

    def __getattr__(self, name):
        return _ModuleSyncCD(self._fm, name)

    def __setattr__(self, name, value):
        if not isinstance(value, _ModuleSyncCD):
            raise AttributeError("Attempted to assign sync property - use += instead")

class _ModuleForwardAttr:
    def __setattr__(self, name, value):
        self.__iadd__(value)
        setattr(self._fm, name, value)

class _ModuleSpecials(_ModuleProxy, _ModuleForwardAttr):
    def __iadd__(self, other):
        self._fm._fragment.specials |= set(_flat_list(other))
        return self

class _ModuleSubmodules(_ModuleProxy):
    def __setattr__(self, name, value):
        self._fm._submodules += [(name, e) for e in _flat_list(value)]
        setattr(self._fm, name, value)

    def __iadd__(self, other):
        self._fm._submodules += [(None, e) for e in _flat_list(other)]
        return self

class _ModuleClockDomains(_ModuleProxy, _ModuleForwardAttr):
    def __iadd__(self, other):
        self._fm._fragment.clock_domains += _flat_list(other)
        return self

class Module:
    def get_fragment(self):
        self.get_fragment_called = True
        self.finalize()
        return self._fragment

    def __getattr__(self, name):
        if name == "comb":            return _ModuleComb(self)
        elif name == "sync":          return _ModuleSync(self)
        elif name == "specials":      return _ModuleSpecials(self)
        elif name == "submodules":    return _ModuleSubmodules(self)
        elif name == "clock_domains": return _ModuleClockDomains(self)

        # hack to have initialized regular attributes without using __init__ (which would require derived classes to call it)
        elif name == "finalized":
            self.finalized = False
            return self.finalized
        elif name == "_fragment":
            self._fragment = _Fragment()
            return self._fragment
        elif name == "_submodules":
            self._submodules = []
            return self._submodules
        elif name == "_clock_domains":
            self._clock_domains = []
            return self._clock_domains
        elif name == "get_fragment_called":
            self.get_fragment_called = False
            return self.get_fragment_called

        else:
            raise AttributeError("'"+self.__class__.__name__+"' object has no attribute '"+name+"'")

    def __setattr__(self, name, value):
        if name in ["comb", "sync", "specials", "submodules", "clock_domains"]:
            if not isinstance(value, _ModuleProxy):
                raise AttributeError("Attempted to assign special Module property - use += instead")
        else:
            object.__setattr__(self, name, value)

    def _collect_submodules(self):
        r = []
        for name, submodule in self._submodules:
            if not submodule.get_fragment_called:
                r.append((name, submodule.get_fragment()))
        return r

    def finalize(self, *args, **kwargs):
        if not self.finalized:
            self.finalized = True
            # finalize existing submodules before finalizing us
            subfragments = self._collect_submodules()
            self.do_finalize(*args, **kwargs)
            # finalize submodules created by do_finalize
            subfragments += self._collect_submodules()
            # resolve clock domain name conflicts
            needs_renaming = set()
            for (mod_name1, f1), (mod_name2, f2) in combinations(subfragments, 2):
                f1_names = set(cd.name for cd in f1.clock_domains)
                f2_names = set(cd.name for cd in f2.clock_domains)
                common_names = f1_names & f2_names
                if common_names:
                    if mod_name1 is None or mod_name2 is None:
                        raise ValueError("Multiple submodules with local clock domains cannot be anonymous")
                    if mod_name1 == mod_name2:
                        raise ValueError("Multiple submodules with local clock domains cannot have the same name")
                needs_renaming |= common_names
            for mod_name, f in subfragments:
                for cd in f.clock_domains:
                    if cd.name in needs_renaming:
                        rename_clock_domain(f, cd.name, mod_name + "_" + cd.name)
            # sum subfragments
            for mod_name, f in subfragments:
                self._fragment += f

    def do_finalize(self):
        pass

    def do_exit(self, *args, **kwargs):
        for name, submodule in self._submodules:
            submodule.do_exit(*args, **kwargs)

class ModuleTransformer:
    # overload this in derived classes
    def transform_instance(self, i):
        pass

    # overload this in derived classes
    def transform_fragment(self, i, f):
        pass

    def wrap_class(self, victim):
        class Wrapped(victim):
            def __init__(i, *args, **kwargs):
                victim.__init__(i, *args, **kwargs)
                self.transform_instance(i)

            def get_fragment(i):
                f = victim.get_fragment(i)
                self.transform_fragment(i, f)
                return f

        Wrapped.__name__ = victim.__name__
        Wrapped.__doc__ = victim.__doc__
        Wrapped.__module__ = victim.__module__
        return Wrapped

    def wrap_instance(self, victim):
        self.transform_instance(victim)
        orig_get_fragment = victim.get_fragment

        def get_fragment():
            f = orig_get_fragment()
            self.transform_fragment(victim, f)
            return f

        victim.get_fragment = get_fragment
        return victim

    def __call__(self, victim):
        if isinstance(victim, Module):
            return self.wrap_instance(victim)
        else:
            return self.wrap_class(victim)

class ControlInserter(ModuleTransformer):
    control_name = None  # override this

    def __init__(self, clock_domains=None):
        self.clock_domains = clock_domains

    def transform_instance(self, i):
        if self.clock_domains is None:
            ctl = Signal(self.control_name)
            setattr(i, self.control_name, ctl)
        else:
            for cd in self.clock_domains:
                name = self.control_name + "_" + cd
                ctl = Signal(name)
                setattr(i, name, ctl)

    def transform_fragment(self, i, f):
        if self.clock_domains is None:
            if not f.sync:
                return
            if len(f.sync) > 1:
                raise ValueError("Control signal clock domains must be specified when module has more than one domain")
            cdn = list(f.sync.keys())[0]
            to_insert = [(getattr(i, self.control_name), cdn)]
        else:
            to_insert = [(getattr(i, self.control_name + "_" + cdn), cdn)
                for cdn in self.clock_domains]
        self.transform_fragment_insert(i, f, to_insert)

class CEInserter(ControlInserter):
    control_name = "ce"

    def transform_fragment_insert(self, i, f, to_insert):
        for ce, cdn in to_insert:
            f.sync[cdn] = [If(ce, *f.sync[cdn])]

class ResetInserter(ControlInserter):
    control_name = "reset"

    def transform_fragment_insert(self, i, f, to_insert):
        for reset, cdn in to_insert:
            f.sync[cdn] = insert_reset(reset, f.sync[cdn])

class ClockDomainsRenamer(ModuleTransformer):
    def __init__(self, cd_remapping):
        if isinstance(cd_remapping, str):
            cd_remapping = {"sys": cd_remapping}
        self.cd_remapping = cd_remapping

    def transform_fragment(self, i, f):
        for old, new in self.cd_remapping.items():
            rename_clock_domain(f, old, new)

class Special(DUID):
    def iter_expressions(self):
        for x in []:
            yield x

    def rename_clock_domain(self, old, new):
        for obj, attr, direction in self.iter_expressions():
            rename_clock_domain_expr(getattr(obj, attr), old, new)

    def list_clock_domains(self):
        r = set()
        for obj, attr, direction in self.iter_expressions():
            r |= list_clock_domains_expr(getattr(obj, attr))
        return r

    def list_ios(self, ins, outs, inouts):
        r = set()
        for obj, attr, direction in self.iter_expressions():
            if (direction == SPECIAL_INPUT and ins) or (direction == SPECIAL_OUTPUT and outs) or (direction == SPECIAL_INOUT and inouts):
                signals = list_signals(getattr(obj, attr))
                r.update(signals)
        return r

class _TristateModule(Module):
    def __init__(self, target, o, oe, i):
        self.comb += [
            target.o.eq(o),
            target.oe.eq(oe)
        ]
        if i is not None:
            self.comb += i.eq(target.i)

class Tristate(Special):
    def __init__(self, target, o, oe, i=None):
        Special.__init__(self)
        self._isrecord = hasattr(target, "o") and hasattr(target, "oe")
        if not self._isrecord:
            self.target = wrap(target)
        else:
            self.target = target
            self._target_o = target.o
            self._target_oe = target.oe
            self._target_i = getattr(target, "i", None)
            if i is not None and not hasattr(target, "i"):
                raise ValueError("target has to have i field if parameter i is not None")
        self.o = wrap(o)
        self.oe = wrap(oe)
        self.i = wrap(i) if i is not None else None

    def iter_expressions(self):
        if not self._isrecord:
            tri_attr_context = [
                ("target", SPECIAL_INOUT)
            ]
        else:
            tri_attr_context = [
                ("_target_o", SPECIAL_OUTPUT),
                ("_target_oe", SPECIAL_OUTPUT),
                ("_target_i", SPECIAL_INPUT)
            ]
        tri_attr_context += [
            ("o", SPECIAL_INPUT),
            ("oe", SPECIAL_INPUT),
            ("i", SPECIAL_OUTPUT)
        ]
        for attr, target_context in tri_attr_context:
            if getattr(self, attr) is not None:
                yield self, attr, target_context

    @staticmethod
    def lower(tristate):
        if not tristate._isrecord:
            return None
        else:
            return _TristateModule(tristate.target, tristate.o, tristate.oe, tristate.i)

    @staticmethod
    def emit_verilog(tristate, ns, add_data_file):
        def pe(e):
            return _printexpr(ns, e)[0]
        w, s = value_bits_sign(tristate.target)
        r = "assign " + pe(tristate.target) + " = " + pe(tristate.oe) + " ? " + pe(tristate.o) + " : " + str(w) + "'bz;\n"
        if tristate.i is not None:
            r += "assign " + pe(tristate.i) + " = " + pe(tristate.target) + ";\n"
        r += "\n"
        return r

class TSTriple:
    def __init__(self, bits_sign=None, min=None, max=None, reset_o=0, reset_oe=0, reset_i=0, name=None):
        self.o = Signal(None if name is None else name + "_o", bits_sign, min=min, max=max, reset=reset_o)
        self.oe = Signal(None if name is None else name + "_oe", reset=reset_oe)
        self.i = Signal(None if name is None else name + "_i", bits_sign, min=min, max=max, reset=reset_i)

    def get_tristate(self, target):
        return Tristate(target, self.o, self.oe, self.i)

    def __len__(self):
        return len(self.o)

class Instance(Special):
    class _IO:
        def __init__(self, name, expr=None):
            self.name = name
            if expr is None:
                expr = Signal("expr")
            self.expr = wrap(expr)
    class Input(_IO):
        pass
    class Output(_IO):
        pass
    class InOut(_IO):
        pass
    class Parameter:
        def __init__(self, name, value):
            self.name = name
            if isinstance(value, (int, bool)):
                value = Constant(value)
            self.value = value
    class PreformattedParam(str):
        pass

    def __init__(self, of, *items, name="", synthesis_directive=None, attr=None, **kwargs):
        Special.__init__(self)
        self.of = of
        if name:
            self.name = name
        else:
            self.name = of
        self.items = list(items)
        self.synthesis_directive = synthesis_directive
        if attr is None:
            attr = set()
        self.attr = attr
        for k, v in sorted(kwargs.items(), key=operator.itemgetter(0)):
            try:
                item_type, item_name = k.split("_", maxsplit=1)
            except ValueError:
                raise TypeError("Wrong format for value '" + str(k) + "', format should be 'type_name'")

            item_class = {
                "i": Instance.Input,
                "o": Instance.Output,
                "io": Instance.InOut,
                "p": Instance.Parameter
            }[item_type]
            self.items.append(item_class(item_name, v))

    def get_io(self, name):
        for item in self.items:
            if isinstance(item, Instance._IO) and item.name == name:
                return item.expr

    def iter_expressions(self):
        for item in self.items:
            if isinstance(item, Instance.Input):
                yield item, "expr", SPECIAL_INPUT
            elif isinstance(item, Instance.Output):
                yield item, "expr", SPECIAL_OUTPUT
            elif isinstance(item, Instance.InOut):
                yield item, "expr", SPECIAL_INOUT

    @staticmethod
    def emit_verilog(instance, ns, add_data_file):
        r = instance.of + " "
        parameters = list(filter(lambda i: isinstance(i, Instance.Parameter), instance.items))
        if parameters:
            r += "#(\n"
            firstp = True
            for p in parameters:
                if not firstp:
                    r += ",\n"
                firstp = False
                r += "\t." + p.name + "("
                if isinstance(p.value, Constant):
                    r += _printexpr(ns, p.value)[0]
                elif isinstance(p.value, float):
                    r += str(p.value)
                elif isinstance(p.value, Instance.PreformattedParam):
                    r += p.value
                elif isinstance(p.value, str):
                    r += "\"" + p.value + "\""
                else:
                    raise TypeError
                r += ")"
            r += "\n) "
        r += ns.get_name(instance)
        if parameters: r += " "
        r += "(\n"
        firstp = True
        for p in instance.items:
            if isinstance(p, Instance._IO):
                name_inst = p.name
                name_design = _printexpr(ns, p.expr)[0]
                if not firstp:
                    r += ",\n"
                firstp = False
                r += "\t." + name_inst + "(" + name_design + ")"
        if not firstp:
            r += "\n"
        if instance.synthesis_directive is not None:
            synthesis_directive = "/* synthesis {} */".format(instance.synthesis_directive)
            r += ")" + synthesis_directive + ";\n\n"
        else:
            r += ");\n\n"
        return r

(READ_FIRST, WRITE_FIRST, NO_CHANGE) = range(3)

class _MemoryPort(Special):
    def __init__(self, adr, dat_r, we=None, dat_w=None, async_read=False, re=None, we_granularity=0, mode=WRITE_FIRST, clock_domain="sys"):
        Special.__init__(self)
        self.adr = adr
        self.dat_r = dat_r
        self.we = we
        self.dat_w = dat_w
        self.async_read = async_read
        self.re = re
        self.we_granularity = we_granularity
        self.mode = mode
        self.clock = ClockSignal(clock_domain)

    def iter_expressions(self):
        for attr, target_context in [
          ("adr", SPECIAL_INPUT),
          ("we", SPECIAL_INPUT),
          ("dat_w", SPECIAL_INPUT),
          ("re", SPECIAL_INPUT),
          ("dat_r", SPECIAL_OUTPUT),
          ("clock", SPECIAL_INPUT)]:
            yield self, attr, target_context

    @staticmethod
    def emit_verilog(port, ns, add_data_file):
        return ""  # done by parent Memory object

class Memory(Special):
    def __init__(self, name, width, depth, init=None):
        Special.__init__(self)
        self.width = width
        self.depth = depth
        self.ports = []
        self.init = init
        self.name = name or "mem"

    def get_port(self, write_capable=False, async_read=False, has_re=False, we_granularity=0, mode=WRITE_FIRST, clock_domain="sys"):
        if we_granularity >= self.width:
            we_granularity = 0
        adr = Signal("adr", max=self.depth)
        dat_r = Signal("dat_r", self.width)
        if write_capable:
            if we_granularity:
                we = Signal("we", self.width // we_granularity)
            else:
                we = Signal("we")
            dat_w = Signal("dat_w", self.width)
        else:
            we = None
            dat_w = None
        if has_re:
            re = Signal("re")
        else:
            re = None
        mp = _MemoryPort(adr, dat_r, we, dat_w, async_read, re, we_granularity, mode, clock_domain)
        self.ports.append(mp)
        return mp

    @staticmethod
    def emit_verilog(memory, ns, add_data_file):
        r = ""
        def gn(e):
            if isinstance(e, Memory):
                return ns.get_name(e)
            else:
                return _printexpr(ns, e)[0]
        adrbits = bits_for(memory.depth - 1)

        r += "reg [" + str(memory.width - 1) + ":0] " + gn(memory) + "[0:" + str(memory.depth - 1) + "];\n"

        adr_regs = {}
        data_regs = {}
        for port in memory.ports:
            if not port.async_read:
                if port.mode == WRITE_FIRST:
                    adr_reg = Signal("memadr")
                    r += "reg [" + str(adrbits - 1) + ":0] " + gn(adr_reg) + ";\n"
                    adr_regs[id(port)] = adr_reg
                else:
                    data_reg = Signal("memdat")
                    r += "reg [" + str(memory.width - 1) + ":0] " + gn(data_reg) + ";\n"
                    data_regs[id(port)] = data_reg

        for port in memory.ports:
            r += "always @(posedge " + gn(port.clock) + ") begin\n"
            if port.we is not None:
                if port.we_granularity:
                    n = memory.width // port.we_granularity
                    for i in range(n):
                        m = i * port.we_granularity
                        M = (i + 1) * port.we_granularity - 1
                        sl = "[" + str(M) + ":" + str(m) + "]"
                        r += "\tif (" + gn(port.we) + "[" + str(i) + "])\n"
                        r += "\t\t" + gn(memory) + "[" + gn(port.adr) + "]" + sl + " <= " + gn(port.dat_w) + sl + ";\n"
                else:
                    r += "\tif (" + gn(port.we) + ")\n"
                    r += "\t\t" + gn(memory) + "[" + gn(port.adr) + "] <= " + gn(port.dat_w) + ";\n"
            if not port.async_read:
                if port.mode == WRITE_FIRST:
                    rd = "\t" + gn(adr_regs[id(port)]) + " <= " + gn(port.adr) + ";\n"
                else:
                    bassign = gn(data_regs[id(port)]) + " <= " + gn(memory) + "[" + gn(port.adr) + "];\n"
                    if port.mode == READ_FIRST:
                        rd = "\t" + bassign
                    elif port.mode == NO_CHANGE:
                        rd = "\tif (!" + gn(port.we) + ")\n" + "\t\t" + bassign
                if port.re is None:
                    r += rd
                else:
                    r += "\tif (" + gn(port.re) + ")\n"
                    r += "\t" + rd.replace("\n\t", "\n\t\t")
            r += "end\n\n"

        for port in memory.ports:
            if port.async_read:
                r += "assign " + gn(port.dat_r) + " = " + gn(memory) + "[" + gn(port.adr) + "];\n"
            else:
                if port.mode == WRITE_FIRST:
                    r += "assign " + gn(port.dat_r) + " = " + gn(memory) + "[" + gn(adr_regs[id(port)]) + "];\n"
                else:
                    r += "assign " + gn(port.dat_r) + " = " + gn(data_regs[id(port)]) + ";\n"
        r += "\n"

        if memory.init is not None:
            content = ""
            for d in memory.init:
                content += "{:x}\n".format(d)
            memory_filename = add_data_file(gn(memory) + ".init", content)

            r += "initial begin\n"
            r += "\t$readmemh(\"" + memory_filename + "\", " + gn(memory) + ");\n"
            r += "end\n\n"

        return r

def chooser(signal, shift, output, n=None, reverse=False):
    if shift is None:
        return output.eq(signal)
    if n is None:
        n = 2**len(shift)
    w = len(output)
    cases = {}
    for i in range(n):
        if reverse:
            s = n - i - 1
        else:
            s = i
        cases[i] = [output.eq(signal[s * w : (s + 1) * w])]
    return Case(shift, cases).makedefault()

class WaitTimer(Module):
    def __init__(self, t):
        self.wait = Signal("wait")
        self.done = Signal("done")

        count = Signal("count", bits_for(t), reset=t)
        self.comb += self.done.eq(count == 0)
        self.sync += \
            If(self.wait,
                If(~self.done, count.eq(count - 1))
            ).Else(count.eq(count.reset))

(DIR_NONE, DIR_S_TO_M, DIR_M_TO_S) = range(3)

# Possible layout elements:
#   1. (name, size)
#   2. (name, size, direction)
#   3. (name, sublayout)
# size can be an int, or a (int, bool) tuple for signed numbers sublayout must be a list

def set_layout_parameters(layout, **layout_dict):
    def resolve(p):
        if isinstance(p, str):
            try:
                return layout_dict[p]
            except KeyError:
                return p
        else:
            return p

    r = []
    for f in layout:
        if isinstance(f[1], (int, tuple, str)):  # cases 1/2
            if len(f) == 3:
                r.append((f[0], resolve(f[1]), f[2]))
            else:
                r.append((f[0], resolve(f[1])))
        elif isinstance(f[1], list):  # case 3
            r.append((f[0], set_layout_parameters(f[1], **layout_dict)))
        else:
            raise TypeError
    return r

def layout_len(layout):
    r = 0
    for f in layout:
        if isinstance(f[1], (int, tuple)):  # cases 1/2
            if len(f) == 3:
                fname, fsize, fdirection = f
            else:
                fname, fsize = f
        elif isinstance(f[1], list):  # case 3
            fname, fsublayout = f
            fsize = layout_len(fsublayout)
        else:
            raise TypeError
        if isinstance(fsize, tuple):
            r += fsize[0]
        else:
            r += fsize
    return r

class Record:
    def __init__(self, name, layout):
        self.name = name
        self.layout = layout

        if self.name:
            prefix = self.name + "_"
        else:
            prefix = ""
        for f in self.layout:
            if isinstance(f[1], (int, tuple)):  # cases 1/2
                if len(f) == 3:
                    fname, fsize, fdirection = f
                else:
                    fname, fsize = f
                finst = Signal(prefix + fname, fsize)
            elif isinstance(f[1], list):  # case 3
                fname, fsublayout = f
                finst = Record(prefix + fname, fsublayout)
            else:
                raise TypeError
            setattr(self, fname, finst)

    def eq(self, other):
        return [getattr(self, f[0]).eq(getattr(other, f[0])) for f in self.layout if hasattr(other, f[0])]

    def iter_flat(self):
        for f in self.layout:
            e = getattr(self, f[0])
            if isinstance(e, Signal):
                if len(f) == 3:
                    yield e, f[2]
                else:
                    yield e, DIR_NONE
            elif isinstance(e, Record):
                yield from e.iter_flat()
            else:
                raise TypeError

    def flatten(self):
        return [signal for signal, direction in self.iter_flat()]

    def raw_bits(self):
        return Cat(*self.flatten())

    def connect(self, *slaves, keep=None, omit=None):
        if keep is None:
            _keep = set([f[0] for f in self.layout])
        elif isinstance(keep, list):
            _keep = set(keep)
        else:
            _keep = keep
        if omit is None:
            _omit = set()
        elif isinstance(omit, list):
            _omit = set(omit)
        else:
            _omit = omit

        _keep = _keep - _omit

        r = []
        for f in self.layout:
            field = f[0]
            self_e = getattr(self, field)
            if isinstance(self_e, Signal):
                if field in _keep:
                    direction = f[2]
                    if direction == DIR_M_TO_S:
                        r += [getattr(slave, field).eq(self_e) for slave in slaves]
                    elif direction == DIR_S_TO_M:
                        r.append(self_e.eq(reduce(operator.or_, [getattr(slave, field) for slave in slaves])))
                    else:
                        raise TypeError
            else:
                for slave in slaves:
                    r += self_e.connect(getattr(slave, field), keep=keep, omit=omit)
        return r

    def connect_flat(self, *slaves):
        r = []
        iter_slaves = [slave.iter_flat() for slave in slaves]
        for m_signal, m_direction in self.iter_flat():
            if m_direction == DIR_M_TO_S:
                for iter_slave in iter_slaves:
                    s_signal, s_direction = next(iter_slave)
                    r.append(s_signal.eq(m_signal))
            elif m_direction == DIR_S_TO_M:
                s_signals = []
                for iter_slave in iter_slaves:
                    s_signal, s_direction = next(iter_slave)
                    s_signals.append(s_signal)
                r.append(m_signal.eq(reduce(operator.or_, s_signals)))
            else:
                raise TypeError
        return r

    def __len__(self):
        return layout_len(self.layout)

class AnonymousState:
    pass

class NextState(_Statement):
    def __init__(self, state):
        self.state = state

class NextValue(_Statement):
    def __init__(self, target, value):
        self.target = target
        self.value = value

def _target_eq(a, b):
    if type(a) != type(b):
        return False
    ty = type(a)
    if ty == Constant:
        return a.value == b.value
    elif ty == Signal:
        return a is b
    elif ty == Cat:
        return all(_target_eq(x, y) for x, y in zip(a.l, b.l))
    elif ty == _Slice:
        return (_target_eq(a.value, b.value) and a.start == b.start and a.stop == b.stop)
    elif ty == _Part:
        return (_target_eq(a.value, b.value) and _target_eq(a.offset == b.offset) and a.width == b.width)
    elif ty == _ArrayProxy:
        return (all(_target_eq(x, y) for x, y in zip(a.choices, b.choices)) and _target_eq(a.key, b.key))
    else:
        raise ValueError("NextValue cannot be used with target type '{}'".format(ty))

class _LowerNext(NodeTransformer):
    def __init__(self, next_state_signal, encoding, aliases):
        self.next_state_signal = next_state_signal
        self.encoding = encoding
        self.aliases = aliases
        # (target, next_value_ce, next_value)
        self.registers = []

    def _get_register_control(self, target):
        for x in self.registers:
            if _target_eq(target, x[0]):
                return x[1], x[2]
        raise KeyError

    def visit_unknown(self, node):
        if isinstance(node, NextState):
            try:
                actual_state = self.aliases[node.state]
            except KeyError:
                actual_state = node.state
            return self.next_state_signal.eq(self.encoding[actual_state])
        elif isinstance(node, NextValue):
            try:
                next_value_ce, next_value = self._get_register_control(node.target)
            except KeyError:
                related = node.target if isinstance(node.target, Signal) else None
                next_value = Signal("next_value", bits_sign=value_bits_sign(node.target), related=related)
                next_value_ce = Signal("next_value_ce", related=related)
                self.registers.append((node.target, next_value_ce, next_value))
            return next_value.eq(node.value), next_value_ce.eq(1)
        else:
            return node

# Finite state machine
#
# reset_state
#     Reset state. Defaults to the first added state.
#
# >>> self.active = Signal("...")
# >>> self.bitno = Signal("...", 3)
# >>>
# >>> fsm = FSM(reset_state="START")
# >>> self.submodules += fsm
# >>>
# >>> fsm.act("START",
# ...     self.active.eq(1),
# ...     If(strobe,
# ...         NextState("DATA")
# ...     )
# ... )
# >>> fsm.act("DATA",
# ...     self.active.eq(1),
# ...     If(strobe,
# ...         NextValue(self.bitno, self.bitno + 1),
# ...         If(self.bitno == 7,
# ...             NextState("END")
# ...         )
# ...     )
# ... )
# >>> fsm.act("END",
# ...     self.active.eq(0),
# ...     NextState("STOP")
# ... )

class FSM(Module):
    def __init__(self, reset_state=None):
        self.actions = OrderedDict()
        self.state_aliases = dict()
        self.reset_state = reset_state

        self.before_entering_signals = OrderedDict()
        self.before_leaving_signals = OrderedDict()
        self.after_entering_signals = OrderedDict()
        self.after_leaving_signals = OrderedDict()

    # Schedules statements to be executed in state. Statements may include:
    #
    # * combinatorial statements of form a.eq(b), equivalent to
    #     self.comb += a.eq(b) when the FSM is in the given state;
    # * synchronous statements of form NextValue(a, b), equivalent to
    #     self.sync += a.eq(b) when the FSM is in the given state;
    # * a statement of form NextState(new_state), selecting the next state;
    # * If, Case, etc.

    def act(self, state, *statements):
        if self.finalized:
            raise FinalizeError
        if self.reset_state is None:
            self.reset_state = state
        if state not in self.actions:
            self.actions[state] = []
        self.actions[state] += statements

    def delayed_enter(self, name, target, delay):
        if self.finalized:
            raise FinalizeError
        if delay > 0:
            state = name
            for i in range(delay):
                if i == delay - 1:
                    next_state = target
                else:
                    next_state = AnonymousState()
                self.act(state, NextState(next_state))
                state = next_state
        else:
            self.state_aliases[name] = target

    # Returns a signal that has the value 1 when the FSM is in the given state, and 0 otherwise.

    def ongoing(self, state):
        is_ongoing = Signal("is_ongoing")
        self.act(state, is_ongoing.eq(1))
        return is_ongoing

    def _get_signal(self, d, state):
        if state not in self.actions:
            self.actions[state] = []
        try:
            return d[state]
        except KeyError:
            is_el = Signal("is_el")
            d[state] = is_el
            return is_el

    def before_entering(self, state):
        return self._get_signal(self.before_entering_signals, state)

    def before_leaving(self, state):
        return self._get_signal(self.before_leaving_signals, state)

    def after_entering(self, state):
        signal = self._get_signal(self.after_entering_signals, state)
        self.sync += signal.eq(self.before_entering(state))
        return signal

    def after_leaving(self, state):
        signal = self._get_signal(self.after_leaving_signals, state)
        self.sync += signal.eq(self.before_leaving(state))
        return signal

    def do_finalize(self):
        nstates = len(self.actions)
        self.encoding = dict((s, n) for n, s in enumerate(self.actions.keys()))
        self.decoding = {n: s for s, n in self.encoding.items()}

        self.state = Signal("state", max=nstates, reset=self.encoding[self.reset_state])
        self.state._enumeration = self.decoding
        self.next_state = Signal("next_state", max=nstates)
        self.next_state._enumeration = {n: "{}:{}".format(n, s) for n, s in self.decoding.items()}

        # drive entering/leaving signals
        for state, signal in self.before_leaving_signals.items():
            encoded = self.encoding[state]
            self.comb += signal.eq((self.state == encoded) & ~(self.next_state == encoded))
        if self.reset_state in self.after_entering_signals:
            self.after_entering_signals[self.reset_state].reset = 1
        for state, signal in self.before_entering_signals.items():
            encoded = self.encoding[state]
            self.comb += signal.eq(~(self.state == encoded) & (self.next_state == encoded))

        # Allow overriding and extending control functionality (Next*) in subclasses.
        self._finalize_sync(self._lower_controls())

    def _lower_controls(self):
        return _LowerNext(self.next_state, self.encoding, self.state_aliases)

    def _finalize_sync(self, ls):
        cases = dict((self.encoding[k], ls.visit(v)) for k, v in self.actions.items() if v)
        self.comb += [
            self.next_state.eq(self.state),
            Case(self.state, cases).makedefault(self.encoding[self.reset_state])
        ]
        self.sync += self.state.eq(self.next_state)
        for register, next_value_ce, next_value in ls.registers:
            self.sync += If(next_value_ce, register.eq(next_value))

(SP_WITHDRAW, SP_CE) = range(2)

class RoundRobin(Module):
    def __init__(self, n, switch_policy=SP_WITHDRAW):
        self.request = Signal("request", n)
        self.grant = Signal("grant", max=max(2, n))
        self.switch_policy = switch_policy
        if self.switch_policy == SP_CE:
            self.ce = Signal("ce")

        if n > 1:
            cases = {}
            for i in range(n):
                switch = []
                for j in reversed(range(i + 1, i + n)):
                    t = j % n
                    switch = [
                        If(self.request[t],
                            self.grant.eq(t)
                        ).Else(
                            *switch
                        )
                    ]
                if self.switch_policy == SP_WITHDRAW:
                    case = [If(~self.request[i], *switch)]
                else:
                    case = switch
                cases[i] = case
            statement = Case(self.grant, cases)
            if self.switch_policy == SP_CE:
                statement = If(self.ce, statement)
            self.sync += statement
        else:
            self.comb += self.grant.eq(0)

class AsyncResetSynchronizer(Special):
    def __init__(self, cd, async_reset):
        Special.__init__(self)
        self.cd = cd
        self.async_reset = wrap(async_reset)

    def iter_expressions(self):
        yield self.cd, "clk", SPECIAL_INPUT
        yield self.cd, "rst", SPECIAL_OUTPUT
        yield self, "async_reset", SPECIAL_INPUT

    @staticmethod
    def lower(dr):
        raise NotImplementedError("Attempted to use a reset synchronizer, but platform does not support them")

class MultiRegImpl(Module):
    def __init__(self, i, o, odomain, n, reset=0):
        self.i = i
        self.o = o
        self.odomain = odomain

        w, signed = value_bits_sign(self.i)
        self.regs = [Signal("regs", (w, signed), reset=reset, reset_less=True) for i in range(n)]

        sd = getattr(self.sync, self.odomain)
        src = self.i
        for reg in self.regs:
            sd += reg.eq(src)
            src = reg
        self.comb += self.o.eq(src)
        for reg in self.regs:
            reg.attr.add("no_retiming")

class MultiReg(Special):
    def __init__(self, i, o, odomain="sys", n=2, reset=0):
        Special.__init__(self)
        self.i = wrap(i)
        self.o = wrap(o)
        self.odomain = odomain
        self.n = n
        self.reset = reset

    def iter_expressions(self):
        yield self, "i", SPECIAL_INPUT
        yield self, "o", SPECIAL_OUTPUT

    def rename_clock_domain(self, old, new):
        Special.rename_clock_domain(self, old, new)
        if self.odomain == old:
            self.odomain = new

    def list_clock_domains(self):
        r = Special.list_clock_domains(self)
        r.add(self.odomain)
        return r

    @staticmethod
    def lower(dr):
        return MultiRegImpl(dr.i, dr.o, dr.odomain, dr.n, dr.reset)

class PulseSynchronizer(Module):
    def __init__(self, idomain, odomain):
        self.i = Signal("i")
        self.o = Signal("o")

        toggle_i = Signal("toggle_i", reset_less=True)
        toggle_o = Signal("toggle_o")  # registered reset_less by MultiReg
        toggle_o_r = Signal("toggle_o_r", reset_less=True)

        sync_i = getattr(self.sync, idomain)
        sync_o = getattr(self.sync, odomain)

        sync_i += If(self.i, toggle_i.eq(~toggle_i))
        self.specials += MultiReg(toggle_i, toggle_o, odomain)
        sync_o += toggle_o_r.eq(toggle_o)
        self.comb += self.o.eq(toggle_o ^ toggle_o_r)

class GrayCounter(Module):
    def __init__(self, width):
        self.ce = Signal("ce")
        self.q = Signal("q", width)
        self.q_next = Signal("q_next", width)
        self.q_binary = Signal("q_binary", width)
        self.q_next_binary = Signal("q_next_binary", width)

        self.comb += [
            If(self.ce,
                self.q_next_binary.eq(self.q_binary + 1)
            ).Else(
                self.q_next_binary.eq(self.q_binary)
            ),
            self.q_next.eq(self.q_next_binary ^ self.q_next_binary[1:])
        ]
        self.sync += [
            self.q_binary.eq(self.q_next_binary),
            self.q.eq(self.q_next)
        ]

def _inc(signal, modulo):
    if modulo == 2**len(signal):
        return signal.eq(signal + 1)
    else:
        return If(signal == (modulo - 1),
            signal.eq(0)
        ).Else(
            signal.eq(signal + 1)
        )

# Data written to the input interface (din, we, writable) is buffered and can be read at the output interface (dout, re, readable).
# The data entry written first to the input also appears first on the output.
#
# din : in, width
#     Input data
# writable : out
#     There is space in the FIFO and we can be asserted to load new data.
# we : in
#     Write enable signal to latch din into the FIFO. Does nothing if writable is not asserted.
# dout : out, width
#     Output data. Only valid if readable is asserted.
# readable : out
#     Output data dout valid, FIFO not empty.
# re : in
#     Acknowledge dout. If asserted, the next entry will be available on the next cycle (if readable is high then).

class _FIFOInterface:
    def __init__(self, width, depth):
        self.we = Signal("we")
        self.writable = Signal("writable")  # not full
        self.re = Signal("re")
        self.readable = Signal("readable")  # not empty

        self.din = Signal("din", width, reset_less=True)
        self.dout = Signal("dout", width, reset_less=True)
        self.width = width
        self.depth = depth

# Synchronous FIFO (first in, first out)
#
# Read and write interfaces are accessed from the same clock domain.
# If different clock domains are needed, use _AsyncFIFO.
#
# level : out
#     Number of unread entries.
# replace : in
#     Replaces the last entry written into the FIFO with din.
#     Does nothing if that entry has already been read (i.e. the FIFO is empty).
#     Assert in conjunction with we.

class _SyncFIFO(Module, _FIFOInterface):
    def __init__(self, width, depth, fwft=True):
        _FIFOInterface.__init__(self, width, depth)

        self.level = Signal("level", max=depth + 1)
        self.replace = Signal("replace")

        produce = Signal("produce", max=depth)
        consume = Signal("consume", max=depth)
        storage = Memory("storage", self.width, depth)
        self.specials += storage

        wrport = storage.get_port(write_capable=True, mode=READ_FIRST)
        self.specials += wrport
        self.comb += [
            If(self.replace,
                wrport.adr.eq(produce - 1)
            ).Else(
                wrport.adr.eq(produce)
            ),
            wrport.dat_w.eq(self.din),
            wrport.we.eq(self.we & (self.writable | self.replace))
        ]
        self.sync += If(self.we & self.writable & ~self.replace, _inc(produce, depth))

        do_read = Signal("do_read")
        self.comb += do_read.eq(self.readable & self.re)

        rdport = storage.get_port(async_read=fwft, has_re=not fwft, mode=READ_FIRST)
        self.specials += rdport
        self.comb += [
            rdport.adr.eq(consume),
            self.dout.eq(rdport.dat_r)
        ]
        if not fwft:
            self.comb += rdport.re.eq(do_read)
        self.sync += If(do_read, _inc(consume, depth))

        self.sync += \
            If(self.we & self.writable & ~self.replace,
                If(~do_read, self.level.eq(self.level + 1))
            ).Elif(do_read,
                self.level.eq(self.level - 1)
            )
        self.comb += [
            self.writable.eq(self.level != depth),
            self.readable.eq(self.level != 0)
        ]

# Has an interface compatible with _SyncFIFO with fwft=True, but does not use asynchronous RAM reads that are not compatible with block RAMs.
# Increases latency by one cycle.

class _SyncFIFOBuffered(Module, _FIFOInterface):
    def __init__(self, width, depth):
        _FIFOInterface.__init__(self, width, depth)
        self.submodules.fifo = fifo = _SyncFIFO(width, depth, False)

        self.writable = fifo.writable
        self.din = fifo.din
        self.we = fifo.we
        self.dout = fifo.dout
        self.level = Signal("level", max=depth + 2)

        self.comb += fifo.re.eq(fifo.readable & (~self.readable | self.re))
        self.sync += \
            If(fifo.re,
                self.readable.eq(1),
            ).Elif(self.re,
                self.readable.eq(0),
            )
        self.comb += self.level.eq(fifo.level + self.readable)

# Asynchronous FIFO (first in, first out)
#
# Read and write interfaces are accessed from different clock domains, named read and write.
# Use ClockDomainsRenamer to rename to other names.

class _AsyncFIFO(Module, _FIFOInterface):
    def __init__(self, width, depth):
        _FIFOInterface.__init__(self, width, depth)

        depth_bits = log2_int(depth, True)

        produce = ClockDomainsRenamer("write")(GrayCounter(depth_bits + 1))
        consume = ClockDomainsRenamer("read")(GrayCounter(depth_bits + 1))
        self.submodules += produce, consume
        self.comb += [
            produce.ce.eq(self.writable & self.we),
            consume.ce.eq(self.readable & self.re)
        ]

        produce_rdomain = Signal("produce_rdomain", depth_bits + 1)
        produce.q.attr.add("no_retiming")
        self.specials += MultiReg(produce.q, produce_rdomain, "read")
        consume_wdomain = Signal("consume_wdomain", depth_bits + 1)
        consume.q.attr.add("no_retiming")
        self.specials += MultiReg(consume.q, consume_wdomain, "write")
        if depth_bits == 1:
            self.comb += self.writable.eq((produce.q[-1] == consume_wdomain[-1]) | (produce.q[-2] == consume_wdomain[-2]))
        else:
            self.comb += [
                self.writable.eq((produce.q[-1] == consume_wdomain[-1]) | (produce.q[-2] == consume_wdomain[-2]) | (produce.q[:-2] != consume_wdomain[:-2]))
            ]
        self.comb += self.readable.eq(consume.q != produce_rdomain)

        storage = Memory("storage", self.width, depth)
        self.specials += storage
        wrport = storage.get_port(write_capable=True, clock_domain="write")
        self.specials += wrport
        self.comb += [
            wrport.adr.eq(produce.q_binary[:-1]),
            wrport.dat_w.eq(self.din),
            wrport.we.eq(produce.ce)
        ]
        rdport = storage.get_port(clock_domain="read")
        self.specials += rdport
        self.comb += [
            rdport.adr.eq(consume.q_next_binary[:-1]),
            self.dout.eq(rdport.dat_r)
        ]

# Improves timing when it breaks due to sluggish clock-to-output delay in block RAMs.
# Increases latency by one cycle.

class _AsyncFIFOBuffered(Module, _FIFOInterface):
    def __init__(self, width, depth):
        _FIFOInterface.__init__(self, width, depth)
        self.submodules.fifo = fifo = _AsyncFIFO(width, depth)

        self.writable = fifo.writable
        self.din = fifo.din
        self.we = fifo.we

        self.sync.read += \
            If(self.re | ~self.readable,
                self.dout.eq(fifo.dout),
                self.readable.eq(fifo.readable)
            )
        self.comb += fifo.re.eq(self.re | ~self.readable)

def _make_m2s(layout):
    r = []
    for f in layout:
        if isinstance(f[1], (int, tuple)):
            r.append((f[0], f[1], DIR_M_TO_S))
        else:
            r.append((f[0], _make_m2s(f[1])))
    return r

def set_reset_less(field):
    if isinstance(field, Signal):
        field.reset_less = True
    elif isinstance(field, Record):
        for s, _ in field.iter_flat():
            s.reset_less = True

class EndpointDescription:
    def __init__(self, payload_layout=[], param_layout=[]):
        self.payload_layout = payload_layout
        self.param_layout   = param_layout

    def get_full_layout(self):
        reserved   = {"valid", "ready", "payload", "param", "first", "last", "description"}
        attributed = set()
        for f in self.payload_layout + self.param_layout:
            if f[0] in attributed:
                raise ValueError(f[0] + " already attributed in payload or param layout")
            if f[0] in reserved:
                raise ValueError(f[0] + " cannot be used in endpoint layout")
            attributed.add(f[0])

        full_layout = [
            ("valid",   1, DIR_M_TO_S),
            ("ready",   1, DIR_S_TO_M),
            ("first",   1, DIR_M_TO_S),
            ("last",    1, DIR_M_TO_S),
            ("payload", _make_m2s(self.payload_layout)),
            ("param",   _make_m2s(self.param_layout))
        ]
        return full_layout

class Endpoint(Record):
    def __init__(self, name, description_or_layout=[]):
        if isinstance(description_or_layout, EndpointDescription):
            self.description = description_or_layout
        else:
            self.description = EndpointDescription(description_or_layout)
        Record.__init__(self, name, self.description.get_full_layout())
        set_reset_less(self.first)
        set_reset_less(self.last)
        set_reset_less(self.payload)
        set_reset_less(self.param)

    def __getattr__(self, name):
        try:
            return getattr(object.__getattribute__(self, "payload"), name)
        except:
            return getattr(object.__getattribute__(self, "param"), name)

class _FIFOWrapper(Module):
    def __init__(self, fifo_class, layout, depth):
        self.sink   = sink   = Endpoint("sink", layout)
        self.source = source = Endpoint("source", layout)

        description = sink.description
        fifo_layout = [
            ("payload", description.payload_layout),
            ("param",   description.param_layout),
            ("first",   1),
            ("last",    1)
        ]

        self.submodules.fifo = fifo = fifo_class(layout_len(fifo_layout), depth)
        fifo_in  = Record("fifo_in", fifo_layout)
        fifo_out = Record("fifo_out", fifo_layout)
        self.comb += [
            fifo.din.eq(fifo_in.raw_bits()),
            fifo_out.raw_bits().eq(fifo.dout)
        ]

        self.comb += [
            sink.ready.eq(fifo.writable),
            fifo.we.eq(sink.valid),
            fifo_in.first.eq(sink.first),
            fifo_in.last.eq(sink.last),
            fifo_in.payload.eq(sink.payload),
            fifo_in.param.eq(sink.param),

            source.valid.eq(fifo.readable),
            source.first.eq(fifo_out.first),
            source.last.eq(fifo_out.last),
            source.payload.eq(fifo_out.payload),
            source.param.eq(fifo_out.param),
            fifo.re.eq(source.ready)
        ]

class AsyncFIFO(_FIFOWrapper):
    def __init__(self, layout, depth=4, buffered=False):
        _FIFOWrapper.__init__(self, fifo_class=_AsyncFIFOBuffered if buffered else _AsyncFIFO, layout=layout, depth=depth)

class PipeValid(Module):
    def __init__(self, layout):
        self.sink   = sink   = Endpoint("sink", layout)
        self.source = source = Endpoint("source", layout)

        # Pipe when source is not valid or is ready.
        self.sync += [
            If(~source.valid | source.ready,
                source.valid.eq(sink.valid),
                source.first.eq(sink.first),
                source.last.eq(sink.last),
                source.payload.eq(sink.payload),
                source.param.eq(sink.param),
            )
        ]
        self.comb += sink.ready.eq(~source.valid | source.ready)

# Configuration and Status Registers
#
# The lowest-level description of a register is provided by the CSR class, which maps to the value at a single address on the target bus.
# Also provided are helper classes for dealing with values larger than the CSR buses data width.
#
# CSRStatus,  for providing information to the CPU.
# CSRStorage, for allowing control via the CPU.
#
# Generating register banks
#
# A module can provide bus-independent CSRs by implementing a get_csrs method that returns a list of instances of the classes described above.
#
# Similarly, bus-independent memories can be returned as a list by a get_memories method.
#
# To avoid listing those manually, a module can inherit from the AutoCSR class, which provides get_csrs and get_memories methods that
# scan for CSR and memory attributes and return their list.

class _CSRBase(DUID):
    def __init__(self, name, size):
        DUID.__init__(self)
        self.name = name
        if self.name is None:
            raise ValueError("Cannot extract CSR name from code, need to specify.")
        self.size = size

# Basic CSR register.
#
# size : int
#     Size of the CSR register in bits. Must be less than CSR bus width!
#
# r : Signal("...", size), out
#     Contains the data written from the bus interface. r is only valid when re is high.
#
# re : Signal("..."), out
#     The strobe signal for r. It is active for one cycle, after or during a write from the bus.
#
# w : Signal("...", size), in
#     The value to be read from the bus. Must be provided at all times.
#
# we : Signal("..."), out
#     The strobe signal for w. It is active for one cycle, after or during a read from the bus.

class CSR(_CSRBase):
    def __init__(self, name, size=1):
        _CSRBase.__init__(self, name, size)
        self.re = Signal(self.name + "_re")
        self.r  = Signal(self.name + "_r", self.size)
        self.we = Signal(self.name + "_we")
        self.w  = Signal(self.name + "_w", self.size)

class _CompoundCSR(_CSRBase):
    def __init__(self, name, size):
        _CSRBase.__init__(self, name, size)
        self.simple_csrs = []

    def get_simple_csrs(self):
        if not self.finalized:
            raise FinalizeError
        return self.simple_csrs

    def do_finalize(self, busword):
        raise NotImplementedError

class CSRAccess(IntEnum):
    WriteOnly = 0
    ReadOnly  = 1
    ReadWrite = 2

# CSR Field.
#
# offset : int (optional)
#     Offset of the CSR field on the CSR register in bits.
#
# reset: int (optional)
#     Reset value of the CSR field.
#
# pulse: boolean (optional)
#     Field value is only valid for one cycle when set to True. Only valid for 1-bit fields.
#
# access: enum (optional)
#     Access type of the CSR field.
#
# values: list (optional)
#     A list of supported values.
#     If this is specified, a table will be generated containing the values in the specified order.
#     The value must be an integer in order to allow for automatic constant generation in an IDE, except "do not care" bits are allowed.
#     In the three-tuple variation, the middle value represents an enum value that can be displayed instead of the value.
#         [
#             ("0b0000", "disable the timer"),
#             ("0b0001", "slow", "slow timer"),
#             ("0b1xxx", "fast timer"),
#         ]

class CSRField(Signal):
    def __init__(self, name, size=1, offset=None, reset=0, pulse=False, access=None, values=None):
        self.name        = name
        self.size        = size
        self.offset      = offset
        self.reset_value = reset
        self.access      = access
        self.pulse       = pulse
        self.values      = values
        Signal.__init__(self, name, size, reset=reset)

class CSRFieldAggregate:
    def __init__(self, fields, access):
        self.check_names(fields)
        self.check_ordering_overlap(fields)
        self.fields = fields
        for field in fields:
            if field.access is None:
                field.access = access
            elif field.access == CSRAccess.ReadOnly:
                pass
            elif field.access == CSRAccess.ReadWrite:
                if field.pulse:
                    field.access = CSRAccess.WriteOnly
            setattr(self, field.name, field)

    @staticmethod
    def check_names(fields):
        names = []
        for field in fields:
            if field.name in names:
                raise ValueError("CSRField \"{}\" name is already used in CSR register".format(field.name))
            else:
                names.append(field.name)

    @staticmethod
    def check_ordering_overlap(fields):
        offset = 0
        for field in fields:
            if field.offset is not None:
                if field.offset < offset:
                    raise ValueError("CSRField ordering/overlap issue on \"{}\" field".format(field.name))
                offset = field.offset
            else:
                field.offset = offset
            offset += field.size

    def get_size(self):
        return self.fields[-1].offset + self.fields[-1].size

    def get_reset(self):
        reset = 0
        for field in self.fields:
            reset |= (field.reset_value << field.offset)
        return reset

# Status Register.
#
# The CSRStatus class is meant to be used as a status register that is read-only from the CPU.
# The user design is expected to drive its status signal.
# The advantage of using CSRStatus instead of using CSR and driving w is that the width of CSRStatus can be arbitrary.
# Status registers larger than the bus word width are automatically broken down into several CSR registers to span several addresses.
# *Be careful, though:* the atomicity of reads is not guaranteed.
#
# size : int
#     Size of the CSR register in bits. Can be bigger than the CSR bus width.
#
# reset : string
#     Value of the register after reset.
#
# status : Signal("...", size), in
#     The value of the CSRStatus register.

class CSRStatus(_CompoundCSR, Module):
    def __init__(self, name, size=1, reset=0, fields=[]):
        if fields != []:
            self.fields = CSRFieldAggregate(fields, CSRAccess.ReadOnly)
            size  = self.fields.get_size()
            reset = self.fields.get_reset()
        _CompoundCSR.__init__(self, name, size)
        self.status = Signal("status", self.size, reset=reset)
        self.we = Signal("we")
        for field in fields:
            self.comb += self.status[field.offset:field.offset + field.size].eq(getattr(self.fields, field.name))

    def do_finalize(self, busword):
        nwords = (self.size + busword - 1) // busword
        for i in reversed(range(nwords)):
            nbits = min(self.size - i * busword, busword)
            sc = CSR(self.name + str(i) if nwords > 1 else self.name, nbits)
            self.comb += sc.w.eq(self.status[i * busword : i * busword + nbits])
            self.simple_csrs.append(sc)
        self.comb += self.we.eq(sc.we)

# Control Register.
#
# The CSRStorage class provides a memory location that can be read and written by the CPU, and read and optionally written by the design.
# It can span several CSR addresses.
#
# size : int
#     Size of the CSR register in bits. Can be bigger than the CSR bus width.
#
# reset : string
#     Value of the register after reset.
#
# reset_less : bool
#     If True, do not generate reset logic for CSRStorage.
#
# atomic_write : bool
#     Provide an mechanism for atomic CPU writes is provided. When enabled, writes to the first CSR addresses go to a back-buffer whose contents
#     are atomically copied to the main buffer when the last address is written.
#
# write_from_dev : bool
#     Allow the design to update the CSRStorage value. *Warning*: The atomicity of reads by the CPU is not guaranteed.
#
# storage : Signal("...", size), out
#     Signal providing the value of the CSRStorage object.
#
# re : Signal("..."), in
#     The strobe signal indicating a write to the CSRStorage register from the CPU. It is active for one cycle, after or during a write from the bus.
#
# we : Signal("..."), out
#     The strobe signal to write to the CSRStorage register from the logic. Only available when write_from_dev == True
#
# dat_w : Signal("..."), out
#     The write data to write to the CSRStorage register from the logic. Only available when write_from_dev == True

class CSRStorage(_CompoundCSR, Module):
    def __init__(self, name, size=1, reset=0, reset_less=False, fields=[], atomic_write=False, write_from_dev=False):
        if fields != []:
            self.fields = CSRFieldAggregate(fields, CSRAccess.ReadWrite)
            size  = self.fields.get_size()
            reset = self.fields.get_reset()
        _CompoundCSR.__init__(self, name, size)
        self.storage = Signal("storage", self.size, reset=reset, reset_less=reset_less)
        self.atomic_write = atomic_write
        self.re = Signal("re")
        if write_from_dev:
            self.we = Signal("we")
            self.dat_w = Signal("dat_w", self.size)
            self.sync += If(self.we, self.storage.eq(self.dat_w))
        for field in [*fields]:
            field_assign = getattr(self.fields, field.name).eq(self.storage[field.offset:field.offset + field.size])
            if field.pulse:
                self.comb += If(self.re, field_assign)
            else:
                self.comb += field_assign

    def do_finalize(self, busword):
        nwords = (self.size + busword - 1) // busword
        if nwords > 1 and self.atomic_write:
            backstore = Signal(self.name + "_backstore", self.size - busword)
        for i in reversed(range(nwords)):
            nbits = min(self.size - i * busword, busword)
            sc = CSR(self.name + str(i) if nwords else self.name, nbits)
            self.simple_csrs.append(sc)
            lo = i * busword
            hi = lo + nbits
            # read
            self.comb += sc.w.eq(self.storage[lo:hi])
            # write
            if nwords > 1 and self.atomic_write:
                if i:
                    self.sync += If(sc.re, backstore[lo - busword : hi - busword].eq(sc.r))
                else:
                    self.sync += If(sc.re, self.storage.eq(Cat(sc.r, backstore)))
            else:
                self.sync += If(sc.re, self.storage[lo:hi].eq(sc.r))
        self.sync += self.re.eq(sc.re)

def csrprefix(prefix, csrs, done):
    for csr in csrs:
        if csr.duid not in done:
            csr.name = prefix + csr.name
            done.add(csr.duid)

def memprefix(prefix, memories, done):
    for memory in memories:
        if memory.duid not in done:
            memory.name = prefix + memory.name
            done.add(memory.duid)

def _make_gatherer(method, cls, prefix_cb):
    def gatherer(self):
        try:
            exclude = self.autocsr_exclude
        except AttributeError:
            exclude = {}
        try:
            prefixed = self.__prefixed
        except AttributeError:
            prefixed = self.__prefixed = set()
        r = []
        for k, v in xdir(self):
            if k not in exclude:
                if isinstance(v, cls):
                    r.append(v)
                elif hasattr(v, method) and callable(getattr(v, method)):
                    items = getattr(v, method)()
                    prefix_cb(k + "_", items, prefixed)
                    r += items
        return sorted(r, key=lambda x: x.duid)
    return gatherer

# MixIn to provide bus independent access to CSR registers.
#
# A module can inherit from the AutoCSR class, which provides get_csrs and get_memories methods
# that scan for CSR and memory attributes and return their list.
#
# If the module has child objects that implement get_csrs or get_memories, they will be called by
# theAutoCSR methods and their CSR and memories added to the lists returned,
# with the child objects' names as prefixes.

class AutoCSR:
    get_memories = _make_gatherer("get_memories", Memory, memprefix)
    get_csrs = _make_gatherer("get_csrs", _CSRBase, csrprefix)

_csr_bus_layout = [
    ("adr",  "address_width", DIR_M_TO_S),
    ("we",                 1, DIR_M_TO_S),
    ("dat_w",   "data_width", DIR_M_TO_S),
    ("dat_r",   "data_width", DIR_S_TO_M)
]

class CSRBusInterface(Record):
    def __init__(self, data_width=8, address_width=14, alignment=32):
        self.data_width    = data_width
        self.address_width = address_width
        self.alignment     = alignment
        Record.__init__(self, None, set_layout_parameters(_csr_bus_layout, data_width=data_width, address_width=address_width))
        self.adr.reset_less   = True
        self.dat_w.reset_less = True
        self.dat_r.reset_less = True

    @classmethod
    def like(self, other):
        return CSRBusInterface(len(other.dat_w), len(other.adr))

class CSRBusInterconnect(Module):
    def __init__(self, master, slaves):
        self.comb += master.connect(*slaves)

class CSRBusInterconnectShared(Module):
    def __init__(self, masters, slaves):
        intermediate = CSRBusInterface.like(masters[0])
        self.comb += [
            intermediate.adr.eq(reduce(operator.or_, [masters[i].adr for i in range(len(masters))])),
            intermediate.we.eq(reduce(operator.or_, [masters[i].we for i in range(len(masters))])),
            intermediate.dat_w.eq(reduce(operator.or_, [masters[i].dat_w for i in range(len(masters))]))
        ]
        for i in range(len(masters)):
            self.comb += masters[i].dat_r.eq(intermediate.dat_r)
        self.comb += intermediate.connect(*slaves)

class CSRBusSRAM(Module):
    def __init__(self, mem_or_size, address, read_only=None, init=None, bus=None, paging=0x800, soc_bus_data_width=32):
        if bus is None:
            bus = CSRBusInterface()
        self.bus = bus
        aligned_paging = paging // (soc_bus_data_width // 8)
        data_width = len(self.bus.dat_w)
        if isinstance(mem_or_size, Memory):
            mem = mem_or_size
        else:
            mem = Memory("mem", data_width, mem_or_size // (data_width // 8), init)
        mem_size = int(mem.width * mem.depth / 8)
        csrw_per_memw = (mem.width + data_width - 1) // data_width
        word_bits = log2_int(csrw_per_memw)
        page_bits = log2_int((mem.depth * csrw_per_memw + aligned_paging - 1) // aligned_paging, False)
        if page_bits:
            self._page = CSRStorage(mem.name + "_page", page_bits)
            printf("WARNING: SRAM CSR memory will requires paged access.")
        else:
            self._page = None
        if read_only is None:
            if hasattr(mem, "bus_read_only"):
                read_only = mem.bus_read_only
            else:
                read_only = False

        port = mem.get_port(write_capable=not read_only)
        self.specials += mem, port

        sel = Signal("sel")
        sel_r = Signal("sel_r")
        self.sync += sel_r.eq(sel)
        self.comb += sel.eq(self.bus.adr[log2_int(aligned_paging):] == address)

        if word_bits:
            word_index    = Signal("word_index", word_bits, reset_less=True)
            word_expanded = Signal("word_expanded", csrw_per_memw * data_width)
            self.sync += word_index.eq(self.bus.adr[:word_bits])
            self.comb += [
                word_expanded.eq(port.dat_r),
                If(sel_r, chooser(word_expanded, word_index, self.bus.dat_r, n=csrw_per_memw, reverse=True))
            ]
            if not read_only:
                wregs = []
                for i in range(csrw_per_memw - 1):
                    wreg = Signal("wreg", data_width, reset_less=True)
                    self.sync += If(sel & self.bus.we & (self.bus.adr[:word_bits] == i), wreg.eq(self.bus.dat_w))
                    wregs.append(wreg)
                memword_chunks = [self.bus.dat_w] + list(reversed(wregs))
                self.comb += [
                    port.we.eq(sel & self.bus.we & (self.bus.adr[:word_bits] == csrw_per_memw - 1)),
                    port.dat_w.eq(Cat(*memword_chunks))
                ]
        else:
            self.comb += If(sel_r, self.bus.dat_r.eq(port.dat_r))
            if not read_only:
                self.comb += [
                    port.we.eq(sel & self.bus.we),
                    port.dat_w.eq(self.bus.dat_w)
                ]

        if self._page is None:
            self.comb += port.adr.eq(self.bus.adr[word_bits : word_bits + len(port.adr)])
        else:
            pv = self._page.storage
            self.comb += port.adr.eq(Cat(self.bus.adr[word_bits : word_bits + len(port.adr) - len(pv)], pv))

    def get_csrs(self):
        if self._page is None:
            return []
        else:
            return [self._page]

class CSRBank(Module):
    def __init__(self, description, address=0, bus=None, paging=0x800, soc_bus_data_width=32):
        if bus is None:
            bus = CSRBusInterface()
        self.bus = bus
        aligned_paging = paging // (soc_bus_data_width // 8)

        busword = len(self.bus.dat_w)
        # Turn description into simple CSRs and claim ownership of compound CSR modules
        self.simple_csrs = []
        for c in description:
            if isinstance(c, CSR):
                self.simple_csrs.append(c)
            else:
                c.finalize(busword)
                self.simple_csrs += c.get_simple_csrs()
                self.submodules += c
        self.decode_bits = bits_for(len(self.simple_csrs) - 1)

        sel = Signal("sel")
        self.comb += sel.eq(self.bus.adr[log2_int(aligned_paging):] == address)

        for i, c in enumerate(self.simple_csrs):
            self.comb += [
                c.r.eq(self.bus.dat_w[:c.size]),
                c.re.eq(sel & self.bus.we & (self.bus.adr[:self.decode_bits] == i)),
                c.we.eq(sel & ~self.bus.we & (self.bus.adr[:self.decode_bits] == i)),
            ]

        brcases = dict((i, self.bus.dat_r.eq(c.w)) for i, c in enumerate(self.simple_csrs))
        self.sync += [
            self.bus.dat_r.eq(0),
            If(sel, Case(self.bus.adr[:self.decode_bits], brcases))
        ]

# address_map(name, memory) returns the CSR offset at which to map the CSR object (register bank or memory).
# If memory=None, the object is the register bank of object source.name.
# Otherwise, it is a memory object belonging to source.name.
# address_map is called exactly once for each object at each call to scan(), so it can have side effects.

class CSRBankArray(Module):
    def __init__(self, source, address_map, *ifargs, paging=0x800, soc_bus_data_width=32, **ifkwargs):
        self.source             = source
        self.address_map        = address_map
        self.paging             = paging
        self.soc_bus_data_width = soc_bus_data_width

        self.banks = []
        self.srams = []
        for name, obj in xdir(self.source):
            if hasattr(obj, "get_csrs"):
                csrs = obj.get_csrs()
            else:
                csrs = []
            if hasattr(obj, "get_memories"):
                memories = obj.get_memories()
                for memory in memories:
                    if isinstance(memory, tuple):
                        read_only, memory = memory
                    else:
                        read_only = False
                    mapaddr = self.address_map(name, memory)
                    if mapaddr is None:
                        continue
                    sram_bus = CSRBusInterface(*ifargs, **ifkwargs)
                    mmap = CSRBusSRAM(memory, mapaddr,
                        read_only = read_only,
                        bus       = sram_bus,
                        paging    = self.paging)
                    self.submodules += mmap
                    csrs += mmap.get_csrs()
                    self.srams.append((name, memory, mapaddr, mmap))
            if csrs:
                mapaddr = self.address_map(name, None)
                if mapaddr is None:
                    continue
                bank_bus = CSRBusInterface(*ifargs, **ifkwargs)
                rmap = CSRBank(csrs, mapaddr,
                    bus                = bank_bus,
                    paging             = self.paging,
                    soc_bus_data_width = self.soc_bus_data_width)
                self.submodules += rmap
                self.banks.append((name, csrs, mapaddr, rmap))

    def get_rmaps(self):
        return [rmap for name, csrs, mapaddr, rmap in self.banks]

    def get_mmaps(self):
        return [mmap for name, memory, mapaddr, mmap in self.srams]

    def get_buses(self):
        return [i.bus for i in self.get_rmaps() + self.get_mmaps()]

# Base class for EventSources.
#
# trigger : Signal("..."), in
#     Signal which interfaces with the user design.
#
# status : Signal("..."), out
#     Contains the current level of the trigger signal.
#     This value ends up in the status register.
#
# pending : Signal("..."), out
#     A trigger event has occurred and not yet cleared.
#     This value ends up in the pending register.
#
# clear : Signal("..."), in
#     Clear after a trigger event.
#     Ignored by some event sources.

class _EventSource(DUID):
    def __init__(self, name=None):
        DUID.__init__(self)
        self.status = Signal("status")
        self.pending = Signal("pending")
        self.trigger = Signal("trigger")
        self.clear = Signal("clear")
        self.name = name or "evs"

# EventSource which triggers on a pulse.
#
# The event stays asserted after the trigger signal goes low, and until software acknowledges it.
# An example use is to pulse trigger high for 1 cycle after the reception of a character in a UART.

class EventSourcePulse(Module, _EventSource):
    def __init__(self, name=None):
        _EventSource.__init__(self, name)
        self.comb += self.status.eq(0)
        self.sync += [
            If(self.clear, self.pending.eq(0)),
            If(self.trigger, self.pending.eq(1))
        ]

# EventSource which triggers on a falling edge.
#
# The purpose of this event source is to monitor the status of processes and generate an interrupt on their completion.

class EventSourceProcess(Module, _EventSource):
    def __init__(self, name=None):
        _EventSource.__init__(self, name)
        self.comb += self.status.eq(self.trigger)
        old_trigger = Signal("old_trigger")
        self.sync += [
            If(self.clear, self.pending.eq(0)),
            old_trigger.eq(self.trigger),
            If(~self.trigger & old_trigger, self.pending.eq(1))
        ]

# Provide an IRQ and CSR registers for a set of event sources.
#
# Each event source is assigned one bit in each of those registers.
#
# irq : Signal("..."), out
#     A signal which is driven high whenever there is a pending and unmasked event.
#     It is typically connected to an interrupt line of a CPU.
#
# status : CSR(n), read-only
#     Contains the current level of the trigger line of EventSourceProcess and EventSourceLevel sources.
#     It is always 0 for EventSourcePulse
#
# pending : CSR(n), read-write
#     Contains the currently asserted events. Writing 1 to the bit assigned to an event clears it.
#
# enable : CSR(n), read-write
#     Defines which asserted events will cause the irq line to be asserted.

class EventManager(Module, AutoCSR):
    def __init__(self):
        self.irq = Signal("irq")

    def do_finalize(self):
        sources_u = [v for k, v in xdir(self) if isinstance(v, _EventSource)]
        sources = sorted(sources_u, key=lambda x: x.duid)
        n = len(sources)
        self.status = CSR("status", n)
        self.pending = CSR("pending", n)
        self.enable = CSRStorage("enable", n)

        for i, source in enumerate(sources):
            self.comb += [
                self.status.w[i].eq(source.status),
                If(self.pending.re & self.pending.r[i], source.clear.eq(1)),
                self.pending.w[i].eq(source.pending)
            ]

        irqs = [self.pending.w[i] & self.enable.storage[i] for i in range(n)]
        self.comb += self.irq.eq(reduce(operator.or_, irqs))

    def __setattr__(self, name, value):
        object.__setattr__(self, name, value)
        if isinstance(value, _EventSource):
            if self.finalized:
                raise FinalizeError
            self.submodules += value

class SharedIRQ(Module):
    def __init__(self, *event_managers):
        self.irq = Signal("irq")
        self.comb += self.irq.eq(reduce(operator.or_, [ev.irq for ev in event_managers]))

class GPIOIn(Module, AutoCSR):
    def __init__(self, signal):
        self._in = CSRStatus("in", len(signal))
        self.specials += MultiReg(signal, self._in.status)

class GPIOOut(Module, AutoCSR):
    def __init__(self, signal):
        self._out = CSRStorage("out", len(signal))
        self.comb += signal.eq(self._out.storage)

class GPIOInOut(Module):
    def __init__(self, in_signal, out_signal):
        self.submodules.gpio_in  = GPIOIn(in_signal)
        self.submodules.gpio_out = GPIOOut(out_signal)

    def get_csrs(self):
        return self.gpio_in.get_csrs() + self.gpio_out.get_csrs()

_wishbone_layout = [
    ("adr",    "adr_width", DIR_M_TO_S),
    ("dat_w", "data_width", DIR_M_TO_S),
    ("dat_r", "data_width", DIR_S_TO_M),
    ("sel",    "sel_width", DIR_M_TO_S),
    ("cyc",              1, DIR_M_TO_S),
    ("stb",              1, DIR_M_TO_S),
    ("ack",              1, DIR_S_TO_M),
    ("we",               1, DIR_M_TO_S),
    ("cti",              3, DIR_M_TO_S),
    ("bte",              2, DIR_M_TO_S),
    ("err",              1, DIR_S_TO_M)
]

class WishboneInterface(Record):
    def __init__(self, data_width=32, adr_width=30):
        self.data_width = data_width
        self.adr_width  = adr_width
        Record.__init__(self, None, set_layout_parameters(_wishbone_layout,
            adr_width  = adr_width,
            data_width = data_width,
            sel_width  = data_width // 8))
        self.adr.reset_less   = True
        self.dat_w.reset_less = True
        self.dat_r.reset_less = True
        self.sel.reset_less   = True

class WishboneTimeout(Module):
    def __init__(self, master, cycles):
        self.error = Signal("error")

        timer = WaitTimer(int(cycles))
        self.submodules += timer
        self.comb += [
            timer.wait.eq(master.stb & master.cyc & ~master.ack),
            If(timer.done,
                master.dat_r.eq((2**len(master.dat_w)) - 1),
                master.ack.eq(1),
                self.error.eq(1)
            )
        ]

class WishboneInterconnect(Module):
    def __init__(self, master, slave):
        self.comb += master.connect(slave)

class WishboneArbiter(Module):
    def __init__(self, masters, target):
        self.submodules.rr = RoundRobin(len(masters))

        # mux master->slave signals
        for name, size, direction in _wishbone_layout:
            if direction == DIR_M_TO_S:
                choices = Array(getattr(m, name) for m in masters)
                self.comb += getattr(target, name).eq(choices[self.rr.grant])

        # connect slave->master signals
        for name, size, direction in _wishbone_layout:
            if direction == DIR_S_TO_M:
                source = getattr(target, name)
                for i, m in enumerate(masters):
                    dest = getattr(m, name)
                    if name == "ack" or name == "err":
                        self.comb += dest.eq(source & (self.rr.grant == i))
                    else:
                        self.comb += dest.eq(source)

        # connect bus requests to round-robin selector
        reqs = [m.cyc for m in masters]
        self.comb += self.rr.request.eq(Cat(*reqs))

class WishboneDecoder(Module):
    # slaves is a list of pairs:
    # 0) function that takes the address signal and returns a FHDL expression
    #    that evaluates to 1 when the slave is selected and 0 otherwise.
    # 1) wishbone.Slave reference.
    # register adds flip-flops after the address comparators. Improves timing,
    # but breaks Wishbone combinatorial feedback.

    def __init__(self, master, slaves, register=False):
        ns = len(slaves)
        slave_sel = Signal("slave_sel", ns)
        slave_sel_r = Signal("slave_sel_r", ns)

        # decode slave addresses
        self.comb += [slave_sel[i].eq(fun(master.adr))
            for i, (fun, bus) in enumerate(slaves)]
        if register:
            self.sync += slave_sel_r.eq(slave_sel)
        else:
            self.comb += slave_sel_r.eq(slave_sel)

        # connect master->slaves signals except cyc
        for slave in slaves:
            for name, size, direction in _wishbone_layout:
                if direction == DIR_M_TO_S and name != "cyc":
                    self.comb += getattr(slave[1], name).eq(getattr(master, name))

        # combine cyc with slave selection signals
        self.comb += [slave[1].cyc.eq(master.cyc & slave_sel[i])
            for i, slave in enumerate(slaves)]

        # generate master ack (resp. err) by ORing all slave acks (resp. errs)
        self.comb += [
            master.ack.eq(reduce(operator.or_, [slave[1].ack for slave in slaves])),
            master.err.eq(reduce(operator.or_, [slave[1].err for slave in slaves]))
        ]

        # mux (1-hot) slave data return
        masked = [Replicate(slave_sel_r[i], len(master.dat_r)) & slaves[i][1].dat_r for i in range(ns)]
        self.comb += master.dat_r.eq(reduce(operator.or_, masked))

class WishboneInterconnectShared(Module):
    def __init__(self, masters, slaves, register=False, timeout_cycles=1e6):
        shared = WishboneInterface()
        self.submodules.arbiter = WishboneArbiter(masters, shared)
        self.submodules.decoder = WishboneDecoder(shared, slaves, register)
        if timeout_cycles is not None:
            self.submodules.timeout = WishboneTimeout(shared, timeout_cycles)

# This module splits Wishbone accesses from a master interface to a smaller slave interface.
#
# Writes:
#     Writes from master are splitted N writes to the slave. Access is acked when the last access is acked by the slave.
#
# Reads:
#     Read from master are splitted in N reads to the the slave. Read datas from the slave are cached before being presented concatenated on the last access.

class WishboneDownConverter(Module):
    def __init__(self, master, slave):
        dw_from = len(master.dat_r)
        dw_to   = len(slave.dat_w)
        ratio   = dw_from // dw_to

        skip    = Signal("skip")
        counter = Signal("counter", max=ratio)

        # Control Path
        fsm = FSM(reset_state="IDLE")
        fsm = ResetInserter()(fsm)
        self.submodules.fsm = fsm
        self.comb += fsm.reset.eq(~master.cyc)
        fsm.act("IDLE",
            NextValue(counter, 0),
            If(master.stb & master.cyc,
                NextState("CONVERT"),
            )
        )
        fsm.act("CONVERT",
            slave.adr.eq(Cat(counter, master.adr)),
            Case(counter, {i: slave.sel.eq(master.sel[i * dw_to // 8:]) for i in range(ratio)}),
            If(master.stb & master.cyc,
                skip.eq(slave.sel == 0),
                slave.we.eq(master.we),
                slave.cyc.eq(~skip),
                slave.stb.eq(~skip),
                If(slave.ack | skip,
                    NextValue(counter, counter + 1),
                    If(counter == (ratio - 1),
                        master.ack.eq(1),
                        NextState("IDLE")
                    )
                )
            )
        )

        # Write Datapath
        self.comb += Case(counter, {i: slave.dat_w.eq(master.dat_w[i * dw_to:]) for i in range(ratio)})

        # Read Datapath
        dat_r = Signal("dat_r", dw_from, reset_less=True)
        self.comb += master.dat_r.eq(Cat(dat_r[dw_to:], slave.dat_r))
        self.sync += If(slave.ack | skip, dat_r.eq(master.dat_r))

# This module is a wrapper for DownConverter and UpConverter.
# It should preferably be used rather than direct instantiations of specific converters.

class WishboneConverter(Module):
    def __init__(self, master, slave):
        self.master = master
        self.slave = slave

        dw_from = len(master.dat_r)
        dw_to = len(slave.dat_r)
        if dw_from > dw_to:
            downconverter = WishboneDownConverter(master, slave)
            self.submodules += downconverter
        elif dw_from < dw_to:
            raise NotImplementedError
        else:
            self.comb += master.connect(slave)

class WishboneSRAM(Module):
    def __init__(self, mem_or_size, read_only=None, init=None, bus=None):
        if bus is None:
            bus = WishboneInterface()
        self.bus = bus
        bus_data_width = len(self.bus.dat_r)
        if isinstance(mem_or_size, Memory):
            self.mem = mem_or_size
        else:
            self.mem = Memory("mem", bus_data_width, mem_or_size // (bus_data_width // 8), init)
        if read_only is None:
            if hasattr(self.mem, "bus_read_only"):
                read_only = self.mem.bus_read_only
            else:
                read_only = False

        # memory
        port = self.mem.get_port(write_capable=not read_only, we_granularity=8, mode=READ_FIRST if read_only else WRITE_FIRST)
        self.specials += self.mem, port
        # generate write enable signal
        if not read_only:
            self.comb += [port.we[i].eq(self.bus.cyc & self.bus.stb & self.bus.we & self.bus.sel[i]) for i in range(bus_data_width // 8)]
        # address and data
        self.comb += [
            port.adr.eq(self.bus.adr[:len(port.adr)]),
            self.bus.dat_r.eq(port.dat_r)
        ]
        if not read_only:
            self.comb += port.dat_w.eq(self.bus.dat_w),
        # generate ack
        self.sync += [
            self.bus.ack.eq(0),
            If(self.bus.cyc & self.bus.stb & ~self.bus.ack, self.bus.ack.eq(1))
        ]

class Wishbone2CSR(Module):
    def __init__(self, bus_wishbone=None, bus_csr=None):
        self.csr = bus_csr
        if self.csr is None:
            self.csr = CSRBusInterface()
        self.wishbone = bus_wishbone
        if self.wishbone is None:
            self.wishbone = WishboneInterface()

        self.comb += [
            self.csr.dat_w.eq(self.wishbone.dat_w),
            self.wishbone.dat_r.eq(self.csr.dat_r)
        ]

        fsm = FSM(reset_state="WRITE-READ")
        self.submodules += fsm
        fsm.act("WRITE-READ",
            If(self.wishbone.cyc & self.wishbone.stb,
                self.csr.adr.eq(self.wishbone.adr),
                self.csr.we.eq(self.wishbone.we & (self.wishbone.sel != 0)),
                NextState("ACK")
            )
        )
        fsm.act("ACK",
            self.wishbone.ack.eq(1),
            NextState("WRITE-READ")
        )

_reserved_keywords = {
    "always", "and", "assign", "automatic", "begin", "buf", "bufif0", "bufif1", "case", "casex", "casez", "cell", "cmos", "config", "deassign", "default",
    "defparam", "design", "disable", "edge", "else", "end", "endcase", "endconfig", "endfunction", "endgenerate", "endmodule", "endprimitive",
    "endspecify", "endtable", "endtask", "event", "for", "force", "forever", "fork", "function", "generate", "genvar", "highz0", "highz1", "if",
    "ifnone", "incdir", "include", "initial", "inout", "input", "instance", "integer", "join", "large", "liblist", "library", "localparam",
    "macromodule", "medium", "module", "nand", "negedge", "nmos", "nor", "noshowcancelled", "not", "notif0", "notif1", "or", "output", "parameter",
    "pmos", "posedge", "primitive", "pull0", "pull1" "pulldown", "pullup", "pulsestyle_onevent", "pulsestyle_ondetect", "remos", "real",
    "realtime", "reg", "release", "repeat", "rnmos", "rpmos", "rtran", "rtranif0", "rtranif1", "scalared", "showcancelled", "signed", "small",
    "specify", "specparam", "strong0", "strong1", "supply0", "supply1", "table", "task", "time", "tran", "tranif0", "tranif1", "tri", "tri0",
    "tri1", "triand", "trior", "trireg", "unsigned", "use", "vectored", "wait", "wand", "weak0", "weak1", "while", "wire", "wor", "xnor", "xor", "do"
}

def _printsig(ns, s):
    if s.signed:
        n = "signed "
    else:
        n = ""
    if len(s) > 1:
        n += "[" + str(len(s) - 1) + ":0] "
    n += ns.get_name(s)
    return n

def _printconstant(node):
    if node.signed:
        sign = "-" if node.value < 0 else ""
        return (sign + str(node.nbits) + "'d" + str(abs(node.value)), True)
    else:
        return str(node.nbits) + "'d" + str(node.value), False

def _printexpr(ns, node):
    if isinstance(node, Constant):
        return _printconstant(node)
    elif isinstance(node, Signal):
        return ns.get_name(node), node.signed
    elif isinstance(node, _Operator):
        arity = len(node.operands)
        r1, s1 = _printexpr(ns, node.operands[0])
        if arity == 1:
            if node.op == "-":
                if s1:
                    r = node.op + r1
                else:
                    r = "-$signed({1'd0, " + r1 + "})"
                s = True
            else:
                r = node.op + r1
                s = s1
        elif arity == 2:
            r2, s2 = _printexpr(ns, node.operands[1])
            if node.op not in ["<<<", ">>>"]:
                if s2 and not s1:
                    r1 = "$signed({1'd0, " + r1 + "})"
                if s1 and not s2:
                    r2 = "$signed({1'd0, " + r2 + "})"
            r = r1 + " " + node.op + " " + r2
            s = s1 or s2
        elif arity == 3:
            r2, s2 = _printexpr(ns, node.operands[1])
            r3, s3 = _printexpr(ns, node.operands[2])
            if s2 and not s3:
                r3 = "$signed({1'd0, " + r3 + "})"
            if s3 and not s2:
                r2 = "$signed({1'd0, " + r2 + "})"
            r = r1 + " ? " + r2 + " : " + r3
            s = s2 or s3
        else:
            raise TypeError
        return "(" + r + ")", s
    elif isinstance(node, _Slice):
        # Verilog does not like us slicing non-array signals...
        if isinstance(node.value, Signal) and len(node.value) == 1 and node.start == 0 and node.stop == 1:
            return _printexpr(ns, node.value)

        if node.start + 1 == node.stop:
            sr = "[" + str(node.start) + "]"
        else:
            sr = "[" + str(node.stop - 1) + ":" + str(node.start) + "]"
        r, s = _printexpr(ns, node.value)
        return r + sr, s
    elif isinstance(node, Cat):
        l = [_printexpr(ns, v)[0] for v in reversed(node.l)]
        return "{" + ", ".join(l) + "}", False
    elif isinstance(node, Replicate):
        return "{" + str(node.n) + "{" + _printexpr(ns, node.v)[0] + "}}", False
    else:
        raise TypeError("Expression of unrecognized type: '{}'".format(type(node).__name__))

(_AT_BLOCKING, _AT_NONBLOCKING, _AT_SIGNAL) = range(3)

def _printnode(ns, at, level, node, target_filter=None):
    if target_filter is not None and target_filter not in list_targets(node):
        return ""
    elif isinstance(node, _Assign):
        if at == _AT_BLOCKING:
            assignment = " = "
        elif at == _AT_NONBLOCKING:
            assignment = " <= "
        elif is_variable(node.l):
            assignment = " = "
        else:
            assignment = " <= "
        return "\t"*level + _printexpr(ns, node.l)[0] + assignment + _printexpr(ns, node.r)[0] + ";\n"
    elif isinstance(node, Iterable):
        return "".join(_printnode(ns, at, level, n, target_filter) for n in node)
    elif isinstance(node, If):
        r = "\t"*level + "if (" + _printexpr(ns, node.cond)[0] + ") begin\n"
        r += _printnode(ns, at, level + 1, node.t, target_filter)
        if node.f:
            r += "\t"*level + "end else begin\n"
            r += _printnode(ns, at, level + 1, node.f, target_filter)
        r += "\t"*level + "end\n"
        return r
    elif isinstance(node, Case):
        if node.cases:
            r = "\t"*level + "case (" + _printexpr(ns, node.test)[0] + ")\n"
            css = [(k, v) for k, v in node.cases.items() if isinstance(k, Constant)]
            css = sorted(css, key=lambda x: x[0].value)
            for choice, statements in css:
                r += "\t"*(level + 1) + _printexpr(ns, choice)[0] + ": begin\n"
                r += _printnode(ns, at, level + 2, statements, target_filter)
                r += "\t"*(level + 1) + "end\n"
            if "default" in node.cases:
                r += "\t"*(level + 1) + "default: begin\n"
                r += _printnode(ns, at, level + 2, node.cases["default"], target_filter)
                r += "\t"*(level + 1) + "end\n"
            r += "\t"*level + "endcase\n"
            return r
        else:
            return ""
    elif isinstance(node, Display):
        s = "\"" + node.s + "\""
        for arg in node.args:
            s += ", "
            if isinstance(arg, Signal):
                s += ns.get_name(arg)
            else:
                s += str(arg)
        return "\t"*level + "$display(" + s + ");\n"
    elif isinstance(node, Finish):
        return "\t"*level + "$finish;\n"
    else:
        raise TypeError("Node of unrecognized type: "+str(type(node)))

def _list_comb_wires(f):
    r = set()
    groups = group_by_targets(f.comb)
    for g in groups:
        if len(g[1]) == 1 and isinstance(g[1][0], _Assign):
            r |= g[0]
    return r

def _printattr(attr, attr_translate):
    r = ""
    firsta = True
    for attr in sorted(attr, key=lambda x: ("", x) if isinstance(x, str) else x):
        if isinstance(attr, tuple):
            # platform-dependent attribute
            attr_name, attr_value = attr
        else:
            # translated attribute
            at = attr_translate[attr]
            if at is None:
                continue
            attr_name, attr_value = at
        if not firsta:
            r += ", "
        firsta = False
        const_expr = "\"" + attr_value + "\"" if not isinstance(attr_value, int) else str(attr_value)
        r += attr_name + " = " + const_expr
    if r:
        r = "(* " + r + " *)"
    return r

def _printheader(f, ios, name, ns, attr_translate):
    sigs = list_signals(f) | list_special_ios(f, True, True, True)
    special_outs = list_special_ios(f, False, True, True)
    inouts = list_special_ios(f, False, False, True)
    targets = list_targets(f) | special_outs
    wires = _list_comb_wires(f) | special_outs
    r = "module " + name + "(\n"
    firstp = True
    for sig in sorted(ios, key=lambda x: x.duid):
        if not firstp:
            r += ",\n"
        firstp = False
        attr = _printattr(sig.attr, attr_translate)
        if attr:
            r += "\t" + attr
        sig.type = "wire"
        if sig in inouts:
            sig.direction = "inout"
            r += "\tinout wire " + _printsig(ns, sig)
        elif sig in targets:
            sig.direction = "output"
            if sig in wires:
                r += "\toutput wire " + _printsig(ns, sig)
            else:
                sig.type = "reg"
                r += "\toutput reg " + _printsig(ns, sig)
        else:
            sig.direction = "input"
            r += "\tinput wire " + _printsig(ns, sig)
    r += "\n);\n\n"
    for sig in sorted(sigs - ios, key=lambda x: x.duid):
        attr = _printattr(sig.attr, attr_translate)
        if attr:
            r += attr + " "
        if sig in wires:
            r += "wire " + _printsig(ns, sig) + ";\n"
        else:
            r += "reg " + _printsig(ns, sig) + " = " + _printexpr(ns, sig.reset)[0] + ";\n"
    r += "\n"
    return r

def _printcomb(f, ns):
    r = ""
    if f.comb:
        groups = group_by_targets(f.comb)

        for n, g in enumerate(groups):
            if len(g[1]) == 1 and isinstance(g[1][0], _Assign):
                r += "assign " + _printnode(ns, _AT_BLOCKING, 0, g[1][0])
            else:
                r += "always @(*) begin\n"
                for t in g[0]:
                    r += "\t" + ns.get_name(t) + " <= " + _printexpr(ns, t.reset)[0] + ";\n"
                r += _printnode(ns, _AT_NONBLOCKING, 1, g[1])
                r += "end\n"
    r += "\n"
    return r

def _printsync(f, ns):
    r = ""
    for k, v in sorted(f.sync.items(), key=operator.itemgetter(0)):
        r += "always @(posedge " + ns.get_name(f.clock_domains[k].clk) + ") begin\n"
        r += _printnode(ns, _AT_SIGNAL, 1, v)
        r += "end\n\n"
    return r

def _printspecials(overrides, specials, ns, add_data_file, attr_translate):
    r = ""
    for special in sorted(specials, key=lambda x: x.duid):
        if hasattr(special, "attr"):
            attr = _printattr(special.attr, attr_translate)
            if attr:
                r += attr + " "
        pr = call_special_classmethod(overrides, special, "emit_verilog", ns, add_data_file)
        if pr is None:
            raise NotImplementedError("Special " + str(special) + " failed to implement emit_verilog")
        r += pr
    return r

class ConvOutput:
    def __init__(self):
        self.main_source = ""
        self.data_files = dict()

    def set_main_source(self, src):
        self.main_source = src

    def add_data_file(self, filename_base, content):
        filename = filename_base
        i = 1
        while filename in self.data_files:
            parts = filename_base.split(".", maxsplit=1)
            parts[0] += "_" + str(i)
            filename = ".".join(parts)
            i += 1
        self.data_files[filename] = content
        return filename

    def write(self, main_filename):
        with open(main_filename, "w") as f:
            f.write(self.main_source)
        for filename, content in self.data_files.items():
            with open(filename, "w") as f:
                f.write(content)

class _Node:
    def __init__(self):
        self.signal_count = 0
        self.numbers = set()
        self.use_name = False
        self.use_number = False
        self.children = OrderedDict()

def _build_tree(signals, basic_tree=None):
    root = _Node()
    for signal in signals:
        current_b = basic_tree
        current = root
        current.signal_count += 1
        for name, number in [("sig", 0)]: #signal.backtrace
            if basic_tree is None:
                use_number = False
            else:
                current_b = current_b.children[name]
                use_number = current_b.use_number
            if use_number:
                key = (name, number)
            else:
                key = name
            try:
                current = current.children[key]
            except KeyError:
                new = _Node()
                current.children[key] = new
                current = new
            current.numbers.add(number)
            if use_number:
                current.all_numbers = sorted(current_b.numbers)
            current.signal_count += 1
    return root

def _set_use_name(node, node_name=""):
    cnames = [(k, _set_use_name(v, k)) for k, v in node.children.items()]
    for (c1_prefix, c1_names), (c2_prefix, c2_names) in combinations(cnames, 2):
        if not c1_names.isdisjoint(c2_names):
            node.children[c1_prefix].use_name = True
            node.children[c2_prefix].use_name = True
    r = set()
    for c_prefix, c_names in cnames:
        if node.children[c_prefix].use_name:
            for c_name in c_names:
                r.add((c_prefix, ) + c_name)
        else:
            r |= c_names

    if node.signal_count > sum(c.signal_count for c in node.children.values()):
        node.use_name = True
        r.add((node_name, ))

    return r

def _name_signal(tree, signal):
    elements = []
    treepos = tree
    for step_name, step_n in [("sig", 0)]: #signal.backtrace
        try:
            treepos = treepos.children[(step_name, step_n)]
            use_number = True
        except KeyError:
            treepos = treepos.children[step_name]
            use_number = False
        if treepos.use_name:
            elname = step_name
            if use_number:
                elname += str(treepos.all_numbers.index(step_n))
            elements.append(elname)
    return "_".join(elements)

def _build_pnd_from_tree(tree, signals):
    return dict((signal, _name_signal(tree, signal)) for signal in signals)

def _invert_pnd(pnd):
    inv_pnd = dict()
    for k, v in pnd.items():
        inv_pnd[v] = inv_pnd.get(v, [])
        inv_pnd[v].append(k)
    return inv_pnd

def _list_conflicting_signals(pnd):
    inv_pnd = _invert_pnd(pnd)
    r = set()
    for k, v in inv_pnd.items():
        if len(v) > 1:
            r.update(v)
    return r

def _set_use_number(tree, signals):
    for signal in signals:
        current = tree
        for step_name, step_n in [("sig", 0)]: #signal.backtrace
            current = current.children[step_name]
            current.use_number = current.signal_count > len(current.numbers) and len(current.numbers) > 1

def _build_pnd_for_group(group_n, signals):
    basic_tree = _build_tree(signals)
    _set_use_name(basic_tree)
    pnd = _build_pnd_from_tree(basic_tree, signals)

    # If there are conflicts, try splitting the tree by numbers on paths taken by conflicting signals.
    conflicting_signals = _list_conflicting_signals(pnd)
    if conflicting_signals:
        _set_use_number(basic_tree, conflicting_signals)
        numbered_tree = _build_tree(signals, basic_tree)
        _set_use_name(numbered_tree)
        pnd = _build_pnd_from_tree(numbered_tree, signals)

    # ...then add number suffixes by DUID
    inv_pnd = _invert_pnd(pnd)
    duid_suffixed = False
    for name, signals in inv_pnd.items():
        if len(signals) > 1:
            duid_suffixed = True
            for n, signal in enumerate(sorted(signals, key=lambda x: x.duid)):
                pnd[signal] += str(n)

    return pnd

def _build_signal_groups(signals):
    r = []
    for signal in signals:
        # build chain of related signals
        related_list = []
        cur_signal = signal
        while cur_signal is not None:
            related_list.insert(0, cur_signal)
            cur_signal = cur_signal.related
        # add to groups
        for _ in range(len(related_list) - len(r)):
            r.append(set())
        for target_set, source_signal in zip(r, related_list):
            target_set.add(source_signal)
    # with the algorithm above and a list of all signals,
    # a signal appears in all groups of a lower number than its.
    # make signals appear only in their group of highest number.
    for s1, s2 in zip(r, r[1:]):
        s1 -= s2
    return r

def _build_pnd(signals):
    groups = _build_signal_groups(signals)
    gpnds = [_build_pnd_for_group(n, gsignals) for n, gsignals in enumerate(groups)]

    pnd = dict()
    for gn, gpnd in enumerate(gpnds):
        for signal, name in gpnd.items():
            result = name
            cur_gn = gn
            cur_signal = signal
            while cur_signal.related is not None:
                cur_signal = cur_signal.related
                cur_gn -= 1
                result = gpnds[cur_gn][cur_signal] + "_" + result
            pnd[signal] = result

    return pnd

class Namespace:
    def __init__(self, pnd):
        self.counts = {k: 1 for k in _reserved_keywords}
        self.sigs = {}
        self.pnd = pnd
        self.clock_domains = dict()

    def get_name(self, sig):
        if isinstance(sig, ClockSignal):
            sig = self.clock_domains[sig.cd].clk
        if isinstance(sig, ResetSignal):
            sig = self.clock_domains[sig.cd].rst
            if sig is None:
                raise ValueError("Attempted to obtain name of non-existent reset signal of domain " + sig.cd)

        if sig.name is not None:
            sig_name = sig.name
        else:
            sig_name = self.pnd[sig]
        try:
            n = self.sigs[sig]
        except KeyError:
            try:
                n = self.counts[sig_name]
            except KeyError:
                n = 0
            self.sigs[sig] = n
            self.counts[sig_name] = n + 1
        if n:
            return sig_name + "_" + str(n)
        else:
            return sig_name

def build_namespace(signals):
    pnd = _build_pnd(signals)
    ns = Namespace(pnd)
    # register signals with name
    swno = {signal for signal in signals if signal.name is not None}
    for signal in sorted(swno, key=lambda x: x.duid):
        ns.get_name(signal)
    return ns

def to_verilog(f, name, ios, special_overrides, attr_translate):
    r = ConvOutput()
    if not isinstance(f, _Fragment):
        f = f.get_fragment()
    if ios is None:
        ios = set()

    for cd_name in sorted(list_clock_domains(f)):
        f.clock_domains[cd_name]

    f = lower_complex_slices(f)
    insert_resets(f)
    f = lower_basics(f)
    f, lowered_specials = lower_specials(special_overrides, f)
    f = lower_basics(f)

    ns = build_namespace(list_signals(f) | list_special_ios(f, True, True, True) | ios)
    ns.clock_domains = f.clock_domains
    r.ns = ns

    s = ""
    s += _printheader(f, ios, name, ns, attr_translate)
    s += _printcomb(f, ns)
    s += _printsync(f, ns)
    s += _printspecials(special_overrides, f.specials - lowered_specials, ns, r.add_data_file, attr_translate)
    s += "endmodule\n"
    r.set_main_source(s)

    return r

class PID(IntEnum):
    # USB Packet IDs

    # Token pids
    SETUP   = 0b1101 # D
    OUT     = 0b0001 # 1
    IN      = 0b1001 # 9
    SOF     = 0b0101 # 5

    # Data pid
    DATA0   = 0b0011 # 3
    DATA1   = 0b1011 # B
    # USB HS only
    DATA2   = 0b0111 # B
    MDATA   = 0b1111 # F

    # Handshake pids
    ACK     = 0b0010 # 2
    NAK     = 0b1010 # A
    STALL   = 0b1110 # E
    # USB HS only
    NYET    = 0b0110 # 6

    # USB HS only
    PRE      = 0b1100 # C
    ERR      = 0b1100 # C
    SPLIT    = 0b1000 # 8
    PING     = 0b0100 # 4
    RESERVED = 0b0000 # 0

    def byte(self):
        v = self.value
        return v | ((0b1111 ^ v) << 4)

    def encode(self, cycles=4):
        return nrzi(sync() + encode_pid(self.value), cycles)[cycles * len(sync()):]

class PIDTypes(IntEnum):

    TOKEN     = 0b0001
    DATA      = 0b0011
    HANDSHAKE = 0b0010
    SPECIAL   = 0b0000

    TYPE_MASK = 0b0011

    @staticmethod
    def token(p):
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.TOKEN

    @staticmethod
    def data(p):
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.DATA

    @staticmethod
    def handshake(p):
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.HANDSHAKE

    @staticmethod
    def special(p):
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.SPECIAL

class Raw(Instance.PreformattedParam):
    def __init__(self, value):
        self.value = value

class IoBuf(Module):
    def __init__(self, usbp_pin, usbn_pin, usb_pullup_pin=None):
        # tx/rx io interface
        self.usb_tx_en = Signal("usb_tx_en")
        self.usb_p_tx = Signal("usb_p_tx")
        self.usb_n_tx = Signal("usb_n_tx")

        self.usb_p_rx = Signal("usb_p_rx")
        self.usb_n_rx = Signal("usb_n_rx")

        self.usb_p_rx_io = Signal("usb_p_rx_io")
        self.usb_n_rx_io = Signal("usb_n_rx_io")

        usb_p_t = TSTriple()
        usb_n_t = TSTriple()

        self.specials += usb_p_t.get_tristate(usbp_pin)
        self.specials += usb_n_t.get_tristate(usbn_pin)

        self.usb_pullup = Signal("usb_pullup")
        if usb_pullup_pin is not None:
            self.comb += [
                usb_pullup_pin.eq(self.usb_pullup),
            ]

        usb_tx_en = Signal("usb_tx_en")
        usb_p_tx = Signal("usb_p_tx")
        usb_n_tx = Signal("usb_n_tx")

        self.sync.usb_48 += [
            usb_tx_en.eq(self.usb_tx_en),
        ]

        # Add IO buffers for outputs
        self.specials += Instance("OFS1P3BX",
            i_D=self.usb_p_tx,
            i_SCLK=ClockSignal("usb_48"),
            i_SP=1,
            i_PD=0,
            o_Q=usb_p_tx,
        )
        self.specials += Instance("OFS1P3BX",
            i_D=self.usb_n_tx,
            i_SCLK=ClockSignal("usb_48"),
            i_SP=1,
            i_PD=0,
            o_Q=usb_n_tx,
        )

        # Use IO buffers on input
        usb_p_rx_ = Signal("usb_p_rx_")
        usb_n_rx_ = Signal("usb_n_rx_")
        usb_p_t_i = Signal("usb_p_t_i")
        usb_n_t_i = Signal("usb_n_t_i")
        self.specials += Instance("IFS1P3BX",
            i_D=usb_p_t.i,
            i_SCLK=ClockSignal("usb_48"),
            i_SP=1,
            i_PD=0,
            o_Q=usb_p_rx_,
        )
        self.sync.usb_48 += usb_p_t_i.eq(usb_p_rx_)

        self.specials += Instance("IFS1P3BX",
            i_D=usb_n_t.i,
            i_SCLK=ClockSignal("usb_48"),
            i_SP=1,
            i_PD=0,
            o_Q=usb_n_rx_,
        )
        self.sync.usb_48 += usb_n_t_i.eq(usb_n_rx_)

        self.comb += [
            If(self.usb_tx_en,
                self.usb_p_rx.eq(0b1),
                self.usb_n_rx.eq(0b0),
            ).Else(
                self.usb_p_rx.eq(usb_p_t_i),
                self.usb_n_rx.eq(usb_n_t_i),
            ),
            usb_p_t.oe.eq(usb_tx_en),
            usb_n_t.oe.eq(usb_tx_en),
            usb_p_t.o.eq(usb_p_tx),
            usb_n_t.o.eq(usb_n_tx),
        ]

# RX Bitstuff Removal
#
# Long sequences of 1's would cause the receiver to lose it's lock on the transmitter's clock.
# USB solves this with bitstuffing. A '0' is stuffed after every 6 consecutive 1's. This extra bit
# is required to recover the clock, but it should not be passed on to higher layers in the device.
#
# usb_12 : 12MHz
#
# i_valid : Signal("...", 1)
#     Qualifier for all of the input signals. Indicates one bit of valid data is present on the inputs.
#
# i_data : Signal("...", 1)
#     Decoded data bit from USB bus. Qualified by valid.
#
# o_data : Signal("...", 1)
#     Decoded data bit from USB bus.
#
# o_stall : Signal("...", 1)
#     Indicates the bit stuffer just removed an extra bit, so no data available.
#
# o_error : Signal("...", 1)
#     Indicates there has been a bitstuff error. A bitstuff error occurs when there should be a stuffed '0'
#     after 6 consecutive 1's; but instead of a '0', there is an additional '1'. This is normal during IDLE,
#     but should never happen within a packet. Qualified by valid.

@ResetInserter()
class RxBitstuffRemover(Module):
    def __init__(self):
        self.i_valid = Signal("i_valid")
        self.i_data = Signal("i_data")

        # This state machine recognizes sequences of 6 bits and drops the 7th bit.
        # The fsm implements a counter in a series of several states.
        # This is intentional to help absolutely minimize the levels of logic used.
        self.submodules.stuff = stuff = FSM(reset_state="D0")

        drop_bit = Signal("drop_bit", 1)

        for i in range(6):
            stuff.act("D%d" % i,
                If(self.i_valid,
                    If(self.i_data,
                        # Receiving '1' increments the bitstuff counter.
                        NextState("D%d" % (i + 1))
                    ).Else(
                        # Receiving '0' resets the bitstuff counter.
                        NextState("D0")
                    )
                ),
            )

        stuff.act("D6",
            If(self.i_valid,
                drop_bit.eq(1),
                # Reset the bitstuff counter, drop the data.
                NextState("D0")
            )
        )

        # pass all of the outputs through a pipe stage
        self.o_data = Signal("o_data")
        self.o_error = Signal("o_error")
        self.o_stall = Signal("o_stall", reset=1)

        self.sync += [
            self.o_data.eq(self.i_data),
            self.o_stall.eq(drop_bit | ~self.i_valid),
            self.o_error.eq(drop_bit & self.i_data & self.i_valid),
        ]

# RX Clock Data Recovery module.
#
# RxClockDataRecovery synchronizes the USB differential pair with the FPGAs clocks,
# de-glitches the differential pair, and recovers the incoming clock and data.
#
# usb_48 : 48MHz
#
# usbp_raw : Signal("...", 1)
#     Raw USB+ input from the FPGA IOs, no need to synchronize.
#
# usbn_raw : Signal("...", 1)
#     Raw USB- input from the FPGA IOs, no need to synchronize.
#
# Output ports are data members of the module. All output ports are flopped.
# The line_state_dj/dk/se0/se1 outputs are 1-hot encoded.
#
# line_state_valid : Signal("...", 1)
#     Asserted for one clock when the output line state is ready to be sampled.
#
# line_state_dj : Signal("...", 1)
#     Represents Full Speed J-state on the incoming USB data pair. Qualify with line_state_valid.
#
# line_state_dk : Signal("...", 1)
#     Represents Full Speed K-state on the incoming USB data pair. Qualify with line_state_valid.
#
# line_state_se0 : Signal("...", 1)
#     Represents SE0 on the incoming USB data pair. Qualify with line_state_valid.
#
# line_state_se1 : Signal("...", 1)
#     Represents SE1 on the incoming USB data pair. Qualify with line_state_valid.

class RxClockDataRecovery(Module):
    def __init__(self, usbp_raw, usbn_raw):
        if False:
            # Synchronize raw USB signals
            #
            # We need to synchronize the raw USB signals with the usb_48 clock domain.
            # MultiReg implements a multi-stage shift register that takes care of this for us.
            # Without MultiReg we would have metastability issues.
            usbp = Signal("usbp", reset=1)
            usbn = Signal("usbn")

            self.specials += MultiReg(usbp_raw, usbp, n=1, reset=1)
            self.specials += MultiReg(usbn_raw, usbn, n=1)
        else:
            # Leave raw USB signals meta-stable. The synchronizer should clean them up.
            usbp = usbp_raw
            usbn = usbn_raw

        # Line State Recovery State Machine
        #
        # The receive path doesn't use a differential receiver. Because of
        # this there is a chance that one of the differential pairs will appear
        # to have changed to the new state while the other is still in the old
        # state. The following state machine detects transitions and waits an
        # extra sampling clock before decoding the state on the differential
        # pair. This transition period # will only ever last for one clock as
        # long as there is no noise on the line. If there is enough noise on
        # the line then the data may be corrupted and the packet will fail the
        # data integrity checks.
        self.submodules.lsr = lsr = FSM()

        dpair = Signal("dpair", 2)
        self.comb += dpair.eq(Cat(usbn, usbp))

        # output signals for use by the clock recovery stage
        line_state_dt = Signal("line_state_dt")
        line_state_dj = Signal("line_state_dj")
        line_state_dk = Signal("line_state_dk")
        line_state_se0 = Signal("line_state_se0")
        line_state_se1 = Signal("line_state_se1")

        # If we are in a transition state, then we can sample the pair and
        # move to the next corresponding line state.
        lsr.act("DT",
            line_state_dt.eq(1),
            Case(dpair, {
                0b10 : NextState("DJ"),
                0b01 : NextState("DK"),
                0b00 : NextState("SE0"),
                0b11 : NextState("SE1")
            })
        )

        # If we are in a valid line state and the value of the pair changes,
        # then we need to move to the transition state.
        lsr.act("DJ",  line_state_dj.eq(1),  If(dpair != 0b10, NextState("DT")))
        lsr.act("DK",  line_state_dk.eq(1),  If(dpair != 0b01, NextState("DT")))
        lsr.act("SE0", line_state_se0.eq(1), If(dpair != 0b00, NextState("DT")))
        lsr.act("SE1", line_state_se1.eq(1), If(dpair != 0b11, NextState("DT")))

        # Clock and Data Recovery
        #
        # The DT state from the line state recovery state machine is used to align to
        # transmit clock. The line state is sampled in the middle of the bit time.
        #
        # Example of signal relationships
        # -------------------------------
        # line_state        DT  DJ  DJ  DJ  DT  DK  DK  DK  DK  DK  DK  DT  DJ  DJ  DJ
        # line_state_valid  ________----____________----____________----________----____
        # bit_phase         0   0   1   2   3   0   1   2   3   0   1   2   0   1   2

        # We 4x oversample, so make the line_state_phase have 4 possible values.
        line_state_phase = Signal("line_state_phase", 2)

        self.line_state_valid = Signal("line_state_valid")
        self.line_state_dj = Signal("line_state_dj")
        self.line_state_dk = Signal("line_state_dk")
        self.line_state_se0 = Signal("line_state_se0")
        self.line_state_se1 = Signal("line_state_se1")

        self.sync += [
            self.line_state_valid.eq(line_state_phase == 1),

            If(line_state_dt,
                # re-align the phase with the incoming transition
                line_state_phase.eq(0),

                # make sure we never assert valid on a transition
                self.line_state_valid.eq(0),
            ).Else(
                # keep tracking the clock by incrementing the phase
                line_state_phase.eq(line_state_phase + 1)
            ),

            # flop all the outputs to help with timing
            self.line_state_dj.eq(line_state_dj),
            self.line_state_dk.eq(line_state_dk),
            self.line_state_se0.eq(line_state_se0),
            self.line_state_se1.eq(line_state_se1),
        ]

# Packet Detection
#
# Full Speed packets begin with the following sequence: KJKJKJKK
# This raw sequence corresponds to the following data: 00000001
# The bus idle condition is signaled with the J state: JJJJJJJJ
#
# This translates to a series of '1's since there are no transitions.
# Given this information, it is easy to detect the beginning of a packet by looking for 00000001.
#
# The end of a packet is even easier to detect.
# The end of a packet is signaled with two SE0 and one J.
# We can just look for the first SE0 to detect the end of the packet.
#
# Packet detection can occur in parallel with bitstuff removal.
#
# i_valid : Signal("...", 1)
#     Qualifier for all of the input signals. Indicates one bit of valid data is present on the inputs.
#
# i_data : Signal("...", 1)
#     Decoded data bit from USB bus. Qualified by valid.
#
# i_se0 : Signal("...", 1)
#     Indicator for SE0 from USB bus. Qualified by valid.
#
# o_pkt_start : Signal("...", 1)
#     Asserted for one clock on the last bit of the sync.
#
# o_pkt_active : Signal("...", 1)
#     Asserted while in the middle of a packet.
#
# o_pkt_end : Signal("...", 1)
#     Asserted for one clock after the last data bit of a packet was received.

@ResetInserter()
class RxPacketDetect(Module):
    def __init__(self):
        self.i_valid = Signal("i_valid")
        self.i_data = Signal("i_data")
        self.i_se0 = Signal("i_se0")

        self.submodules.pkt = pkt = FSM()

        pkt_start = Signal("pkt_start")
        pkt_active = Signal("pkt_active")
        pkt_end = Signal("pkt_end")

        for i in range(5):
            pkt.act("D%d" % i,
                If(self.i_valid,
                    If(self.i_data | self.i_se0,
                        # Receiving '1' or SE0 early resets the packet start counter.
                        NextState("D0")
                    ).Else(
                        # Receiving '0' increments the packet start counter.
                        NextState("D%d" % (i + 1))
                    )
                )
            )

        pkt.act("D5",
            If(self.i_valid,
                If(self.i_se0,
                    NextState("D0")
                # once we get a '1', the packet is active
                ).Elif(self.i_data,
                    pkt_start.eq(1),
                    NextState("PKT_ACTIVE")
                )
            )
        )

        pkt.act("PKT_ACTIVE",
            pkt_active.eq(1),
            If(self.i_valid & self.i_se0,
                NextState("D0"),
                pkt_active.eq(0),
                pkt_end.eq(1)
            )
        )

        # pass all of the outputs through a pipe stage
        self.o_pkt_start = Signal("o_pkt_start")
        self.o_pkt_active = Signal("o_pkt_active")
        self.o_pkt_end = Signal("o_pkt_end")
        self.comb += [
            self.o_pkt_start.eq(pkt_start),
            self.o_pkt_active.eq(pkt_active),
            self.o_pkt_end.eq(pkt_end),
        ]

# RX NRZI decoder.
#
# In order to ensure there are enough bit transitions for a receiver to recover the clock usb uses NRZI encoding.
# This module processes the incoming dj, dk, se0, and valid signals and decodes them to data values.
# It also pipelines the se0 signal and passes it through unmodified.
#
# usb_48 : 48MHz
#
# i_valid : Signal("...", 1)
#     Qualifier for all of the input signals. Indicates one bit of valid data is present on the inputs.
#
# i_dj : Signal("...", 1)
#     Indicates the bus is currently in a Full-Speed J-state. Qualified by valid.
#
# i_dk : Signal("...", 1)
#     Indicates the bus is currently in a Full-Speed K-state. Qualified by valid.
#
# i_se0 : Signal("...", 1)
#     Indicates the bus is currently in a SE0 state. Qualified by valid.
#
# Output ports are data members of the module. All output ports are flopped.
#
# o_valid : Signal("...", 1)
#     Qualifier for all of the output signals. Indicates one bit of valid data is present on the outputs.
#
# o_data : Signal("...", 1)
#     Decoded data bit from USB bus. Qualified by valid.
#
# o_se0 : Signal("...", 1)
#     Indicates the bus is currently in a SE0 state. Qualified by valid.

class RxNRZIDecoder(Module):
    def __init__(self):
        self.i_valid = Signal("i_valid")
        self.i_dj = Signal("i_dj")
        self.i_dk = Signal("i_dk")
        self.i_se0 = Signal("i_se0")

        # pass all of the outputs through a pipe stage
        self.o_valid = Signal("o_valid", 1)
        self.o_data = Signal("o_data", 1)
        self.o_se0 = Signal("o_se0", 1)

        if False:
            valid = Signal("valid", 1)
            data = Signal("data", 1)

            # simple state machine decodes a JK transition as a '0' and no transition as a '1'. se0 is ignored.
            self.submodules.nrzi = nrzi = FSM()

            nrzi.act("DJ",
                If(self.i_valid,
                    valid.eq(1),

                    If(self.i_dj,
                        data.eq(1)
                    ).Elif(self.i_dk,
                        data.eq(0),
                        NextState("DK")
                    )
                )
            )

            nrzi.act("DK",
                If(self.i_valid,
                    valid.eq(1),

                    If(self.i_dj,
                        data.eq(0),
                        NextState("DJ")
                    ).Elif(self.i_dk,
                        data.eq(1)
                    )
                )
            )

            self.sync += [
                self.o_valid.eq(valid),
                If(valid,
                    self.o_se0.eq(self.i_se0),
                    self.o_data.eq(data),
                ),
            ]
        else:
            last_data = Signal("last_data")
            self.sync += [
                If(self.i_valid,
                    last_data.eq(self.i_dk),
                    self.o_data.eq(~(self.i_dk ^ last_data)),
                    self.o_se0.eq((~self.i_dj) & (~self.i_dk)),
                ),
                self.o_valid.eq(self.i_valid),
            ]

# RX Shifter
#
# A shifter is responsible for shifting in serial bits and presenting them as parallel data.
# The shifter knows how many bits to shift and has controls for resetting the shifter.
#
# usb_12 : 12MHz
#
# width : int
#     Number of bits to shift in.
#
# i_valid : Signal("...", 1)
#     Qualifier for all of the input signals. Indicates one bit of valid data is present on the inputs.
#
# i_data : Signal("...", 1)
#     Serial input data. Qualified by valid.
#
# o_data : Signal("...", width)
#     Shifted in data.
#
# o_put : Signal("...", 1)
#     Asserted for one clock once the register is full.

@ResetInserter()
class RxShifter(Module):
    def __init__(self, width):
        self.i_valid = Signal("i_valid")
        self.i_data = Signal("i_data")

        self.o_data = Signal("o_data", width)
        self.o_put = Signal("o_put")

        # Instead of using a counter, we will use a sentinel bit in the shift register to indicate when it is full.
        shift_reg = Signal("shift_reg", width + 1, reset=0b1)

        self.comb += self.o_data.eq(shift_reg[0:width])
        self.sync += [
            self.o_put.eq(shift_reg[width - 1] & ~shift_reg[width] & self.i_valid),
            If(self.i_valid,
                If(shift_reg[width],
                    shift_reg.eq(Cat(self.i_data, shift_reg.reset[0:width])),
                ).Else(
                    shift_reg.eq(Cat(self.i_data, shift_reg[0:width])),
                ),
            ),
        ]

class RxPipeline(Module):
    def __init__(self):
        self.reset = Signal("reset")

        # 12MHz USB alignment pulse in 48MHz clock domain
        self.o_bit_strobe = Signal("o_bit_strobe")

        # Reset state is J
        self.i_usbp = Signal("i_usbp", reset=1)
        self.i_usbn = Signal("i_usbn", reset=0)

        self.o_data_strobe = Signal("o_data_strobe")
        self.o_data_payload = Signal("o_data_payload", 8)

        self.o_pkt_start = Signal("o_pkt_start")
        self.o_pkt_in_progress = Signal("o_pkt_in_progress")
        self.o_pkt_end = Signal("o_pkt_end")

        # 48MHz domain clock recovery
        clock_data_recovery = RxClockDataRecovery(self.i_usbp, self.i_usbn)
        self.submodules.clock_data_recovery = ClockDomainsRenamer("usb_48")(clock_data_recovery)
        self.comb += [
            self.o_bit_strobe.eq(clock_data_recovery.line_state_valid),
        ]

        # A reset condition is one where the device is in SE0 for more than 2.5 uS, which is ~30 bit times.
        self.o_reset = Signal("o_reset")
        reset_counter = Signal("reset_counter", 7)
        self.comb += self.o_reset.eq(reset_counter[6])
        self.sync.usb_48 += [
            If(clock_data_recovery.line_state_valid,
                If(clock_data_recovery.line_state_se0,
                    If(~reset_counter[6],
                        reset_counter.eq(reset_counter + 1),
                    )
                ).Else(
                    reset_counter.eq(0),
                )
            )
        ]

        # NRZI decoding
        nrzi = RxNRZIDecoder()
        self.submodules.nrzi = nrzi = ClockDomainsRenamer("usb_48")(nrzi)
        self.comb += [
            nrzi.i_valid.eq(self.o_bit_strobe),
            nrzi.i_dj.eq(clock_data_recovery.line_state_dj),
            nrzi.i_dk.eq(clock_data_recovery.line_state_dk),
            nrzi.i_se0.eq(clock_data_recovery.line_state_se0),
        ]

        # The packet detector asserts the reset of the pipeline.
        reset = Signal("reset")
        detect = RxPacketDetect()
        self.submodules.detect = detect = ClockDomainsRenamer("usb_48")(detect)
        self.comb += [
            detect.reset.eq(self.reset),
            detect.i_valid.eq(nrzi.o_valid),
            detect.i_se0.eq(nrzi.o_se0),
            detect.i_data.eq(nrzi.o_data),
            reset.eq(~detect.o_pkt_active),
        ]

        bitstuff = RxBitstuffRemover()
        self.submodules.bitstuff = ClockDomainsRenamer("usb_48")(bitstuff)
        self.comb += [
            bitstuff.reset.eq(~detect.o_pkt_active | self.reset),
            bitstuff.i_valid.eq(nrzi.o_valid),
            bitstuff.i_data.eq(nrzi.o_data),
        ]

        last_reset = Signal("last_reset")
        self.sync.usb_48 += [
            last_reset.eq(reset),
        ]

        # 1bit->8bit (1byte) serial to parallel conversion
        shifter = RxShifter(width=8)
        self.submodules.shifter = shifter = ClockDomainsRenamer("usb_48")(shifter)
        self.comb += [
            shifter.reset.eq(last_reset),
            shifter.i_data.eq(bitstuff.o_data),
            shifter.i_valid.eq(~bitstuff.o_stall & detect.o_pkt_active),
        ]

        # Cross the data from the 48MHz domain to the 12MHz domain
        flag_start = Signal("flag_start")
        flag_end = Signal("flag_end")
        flag_valid = Signal("flag_valid")
        payloadFifo = _AsyncFIFO(8, 2)
        self.submodules.payloadFifo = payloadFifo = ClockDomainsRenamer({"write":"usb_48", "read":"usb_12"})(payloadFifo)

        self.comb += [
            payloadFifo.din.eq(shifter.o_data[::-1]),
            payloadFifo.we.eq(shifter.o_put),
            self.o_data_payload.eq(payloadFifo.dout),
            self.o_data_strobe.eq(payloadFifo.readable),
            payloadFifo.re.eq(1),
        ]

        flagsFifo = _AsyncFIFO(2, 2)
        self.submodules.flagsFifo = flagsFifo = ClockDomainsRenamer({"write":"usb_48", "read":"usb_12"})(flagsFifo)

        self.comb += [
            flagsFifo.din[1].eq(detect.o_pkt_start),
            flagsFifo.din[0].eq(detect.o_pkt_end),
            flagsFifo.we.eq(detect.o_pkt_start | detect.o_pkt_end),
            flag_start.eq(flagsFifo.dout[1]),
            flag_end.eq(flagsFifo.dout[0]),
            flag_valid.eq(flagsFifo.readable),
            flagsFifo.re.eq(1),
        ]

        # Packet flag signals (in 12MHz domain)
        self.comb += [
            self.o_pkt_start.eq(flag_start & flag_valid),
            self.o_pkt_end.eq(flag_end & flag_valid),
        ]

        self.sync.usb_12 += [
            If(self.o_pkt_start,
                self.o_pkt_in_progress.eq(1),
            ).Elif(self.o_pkt_end,
                self.o_pkt_in_progress.eq(0),
            ),
        ]

# Bitstuff Insertion
#
# Long sequences of 1's would cause the receiver to lose it's lock on the transmitter's clock.
# USB solves this with bitstuffing. A '0' is stuffed after every 6 consecutive 1's.
#
# The TxBitstuffer is the only component in the transmit pipeline that can delay transmission of serial data.
# It is therefore responsible for generating the bit_strobe signal that keeps the pipe moving forward.
#
# usb_12 : 48MHz
#
# i_data : Signal("...", 1)
#     Data bit to be transmitted on USB.
#
# o_data : Signal("...", 1)
#     Data bit to be transmitted on USB.
#
# o_stall : Signal("...", 1)
#     Used to apply backpressure on the tx pipeline.

@ResetInserter()
class TxBitstuffer(Module):
    def __init__(self):
        self.i_data = Signal("i_data")

        self.o_stall = Signal("o_stall", 1)
        self.o_will_stall = Signal("o_will_stall", 1)
        self.o_data = Signal("o_data", 1)

        self.submodules.stuff = stuff = FSM()

        stuff_bit = Signal("stuff_bit", 1)

        for i in range(5):
            stuff.act("D%d" % i,
                If(self.i_data,
                    # Receiving '1' increments the bitstuff counter.
                    NextState("D%d" % (i + 1))
                ).Else(
                    # Receiving '0' resets the bitstuff counter.
                    NextState("D0")
                )
            )

        stuff.act("D5",
            If(self.i_data,
                # There's a '1', so indicate we might stall on the next loop.
                self.o_will_stall.eq(1),

                # Receiving '1' increments the bitstuff counter.
                NextState("D6")
            ).Else(
                # Receiving '0' resets the bitstuff counter.
                NextState("D0")
            )
        )

        stuff.act("D6",
            # stuff a bit
            stuff_bit.eq(1),

            # Reset the bitstuff counter
            NextState("D0")
        )

        self.comb += [
            self.o_stall.eq(stuff_bit)
        ]

        # flop outputs
        self.sync += [
            If(stuff_bit,
                self.o_data.eq(0),
            ).Else(
                self.o_data.eq(self.i_data),
            ),
        ]

# NRZI Encode
#
# In order to ensure there are enough bit transitions for a receiver to recover the clock usb uses NRZI encoding.
# This module processes the incoming dj, dk, se0, and valid signals and decodes them to data values.
# It also pipelines the se0 signal and passes it through unmodified.
#
# usb_48 : 48MHz
#
# i_valid : Signal("...", 1)
#     Qualifies oe, data, and se0.
#
# i_oe : Signal("...", 1)
#     Indicates that the transmit pipeline should be driving USB.
#
# i_data : Signal("...", 1)
#     Data bit to be transmitted on USB. Qualified by o_valid.
#
# i_se0 : Signal("...", 1)
#     Overrides value of o_data when asserted and indicates that SE0 state should be asserted on USB. Qualified by o_valid.
#
# o_usbp : Signal("...", 1)
#     Raw value of USB+ line.
#
# o_usbn : Signal("...", 1)
#     Raw value of USB- line.
#
# o_oe : Signal("...", 1)
#     When asserted it indicates that the tx pipeline should be driving USB.

class TxNRZIEncoder(Module):
    def __init__(self):
        self.i_valid = Signal("i_valid")
        self.i_oe = Signal("i_oe")
        self.i_data = Signal("i_data")

        # Simple state machine to perform NRZI encoding.
        self.submodules.nrzi = nrzi = FSM()

        usbp = Signal("usbp", 1)
        usbn = Signal("usbn", 1)
        oe = Signal("oe", 1)

        # wait for new packet to start
        nrzi.act("IDLE",
            usbp.eq(1),
            usbn.eq(0),
            oe.eq(0),

            If(self.i_valid,
                If(self.i_oe,
                    # first bit of sync always forces a transition, we idle in J so the first output bit is K.
                    NextState("DK")
                )
            )
        )

        # the output line is in state J
        nrzi.act("DJ",
            usbp.eq(1),
            usbn.eq(0),
            oe.eq(1),

            If(self.i_valid,
                If(~self.i_oe,
                    NextState("SE0A")
                ).Elif(self.i_data,
                    NextState("DJ")
                ).Else(
                    NextState("DK")
                )
            )
        )

        # the output line is in state K
        nrzi.act("DK",
            usbp.eq(0),
            usbn.eq(1),
            oe.eq(1),

            If(self.i_valid,
                If(~self.i_oe,
                    NextState("SE0A")
                ).Elif(self.i_data,
                    NextState("DK")
                ).Else(
                    NextState("DJ")
                )
            )
        )

        # first bit of the SE0 state
        nrzi.act("SE0A",
            usbp.eq(0),
            usbn.eq(0),
            oe.eq(1),

            If(self.i_valid,
                NextState("SE0B")
            )
        )
        # second bit of the SE0 state
        nrzi.act("SE0B",
            usbp.eq(0),
            usbn.eq(0),
            oe.eq(1),

            If(self.i_valid,
                NextState("EOPJ")
            )
        )

        # drive the bus back to J before relinquishing control
        nrzi.act("EOPJ",
            usbp.eq(1),
            usbn.eq(0),
            oe.eq(1),

            If(self.i_valid,
                NextState("IDLE")
            )
        )

        # flop all outputs
        self.o_usbp = Signal("o_usbp", 1)
        self.o_usbn = Signal("o_usbn", 1)
        self.o_oe = Signal("o_oe", 1)

        self.sync += [
            self.o_oe.eq(oe),
            self.o_usbp.eq(usbp),
            self.o_usbn.eq(usbn),
        ]

# Transmit Shifter
#
# TxShifter accepts parallel data and shifts it out serially.
#
# width : int
#     Width of the data to be shifted.
#
# i_data : Signal("...", width)
#     Data to be transmitted.
#
# Output ports are data members of the module. All outputs are flopped.
#
# o_data : Signal("...", 1)
#     Serial data output.
#
# o_empty : Signal("...", 1)
#     Asserted the cycle before the shifter loads in more i_data.
#
# o_get : Signal("...", 1)
#     Asserted the cycle after the shifter loads in i_data.

@ResetInserter()
@CEInserter()
class TxShifter(Module):
    def __init__(self, width):
        self.i_data = Signal("i_data", width)
        self.o_get = Signal("o_get", 1)
        self.o_empty = Signal("o_empty", 1)

        self.o_data = Signal("o_data", 1)

        shifter = Signal("shifter", width)
        pos = Signal("pos", width, reset=0b1)

        empty = Signal("empty", 1)
        self.sync += [
            pos.eq(pos >> 1),
            shifter.eq(shifter >> 1),
            If(empty,
                shifter.eq(self.i_data),
                pos.eq(1 << (width - 1)),
            ),
            self.o_get.eq(empty),
        ]
        self.comb += [
            empty.eq(pos[0]),
            self.o_empty.eq(empty),
            self.o_data.eq(shifter[0]),
        ]

def cols(rows):
    all_c = []
    for ci in range(len(rows[0])):
        all_c.append([])
    for ci in range(len(rows[0])):
        for ri in range(len(rows)):
            all_c[ci].append(rows[ri][ci])
    return all_c

def lfsr_serial_shift_crc(lfsr_poly, lfsr_cur, data):
    lfsr_poly = lfsr_poly[::-1]
    data = data[::-1]

    shift_by = len(data)
    lfsr_poly_size = len(lfsr_poly)

    lfsr_next = list(lfsr_cur)
    for j in range(shift_by):
        lfsr_upper_bit = lfsr_next[lfsr_poly_size - 1]
        for i in range(lfsr_poly_size - 1, 0, -1):
            if lfsr_poly[i]:
                lfsr_next[i] = lfsr_next[i - 1] ^ lfsr_upper_bit ^ data[j]
            else:
                lfsr_next[i] = lfsr_next[i - 1]
        lfsr_next[0] = lfsr_upper_bit ^ data[j]
    return list(lfsr_next[::-1])

def build_matrix(lfsr_poly, data_width):
    lfsr_poly_size = len(lfsr_poly)

    # data_width * lfsr_polysize matrix == lfsr(0, Nin)
    rows_nin = []

    # (a) calculate the N values when Min=0 and Build NxM matrix
    #  - Each value is one hot encoded (there is only one bit)
    #  - IE N=4, 0x1, 0x2, 0x4, 0x8
    #  - Mout = F(Nin, Min=0)
    #  - Each row contains the results of (a)
    #  - IE row[0] == 0x1, row[1] == 0x2
    #  - Output is M-bit wide (CRC width)
    #  - Each column of the matrix represents an output bit Mout[i] as a function of Nin
    info = []
    for i in range(data_width):
        # lfsr_cur = [0,...,0] = Min
        lfsr_cur = [0,] * lfsr_poly_size
        # data = [0,..,1,..,0] = Nin
        data = [0,] * data_width
        data[i] = 1
        # Calculate the CRC
        rows_nin.append(lfsr_serial_shift_crc(lfsr_poly, lfsr_cur, data))
        info.append("lfsr(%r, %r, %r) = %r" % (lfsr_poly, lfsr_cur, data, rows_nin[-1]))
    cols_nin = cols(rows_nin)[::-1]

    # lfsr_polysize * lfsr_polysize matrix == lfsr(Min, 0)
    info.append("")
    rows_min = []
    for i in range(lfsr_poly_size):
        # lfsr_cur = [0,..,1,...,0] = Min
        lfsr_cur = [0,] * lfsr_poly_size
        lfsr_cur[i] = 1
        # data = [0,..,0] = Nin
        data = [0,] * data_width
        # Calculate the crc
        rows_min.append(lfsr_serial_shift_crc(lfsr_poly, lfsr_cur, data))
        info.append("lfsr(%r, %r, %r) = %r" % (lfsr_poly, lfsr_cur, data, rows_min[-1]))
    cols_min = cols(rows_min)[::-1]

    # (c) Calculate CRC for the M values when Nin=0 and Build MxM matrix
    #  - Each value is one hot encoded
    #  - Mout = F(Nin=0, Min)
    #  - Each row contains results from (7)
    info.append("")
    for i in range(data_width, -1, -1):
        info.append("Mout[%i] = %r %r" % (i, cols_nin[i], cols_min[i]))

    return info, cols_nin, cols_min

# Transmit CRC Generator
#
# TxParallelCrcGenerator generates a running CRC.
#
# width : int
#     Width of the CRC.
#
# polynomial : int
#     CRC polynomial in integer form.
#
# initial : int
#     Initial value of the CRC register before data starts shifting in.
#
# i_data_payload : Signal("...", 8)
#     Byte wide data to generate CRC for.
#
# i_data_strobe : Signal("...", 1)
#     Strobe signal for the payload.
#
# o_crc : Signal("...", width)
#     Current CRC value.

@ResetInserter()
class TxParallelCrcGenerator(Module):
    def __init__(self, data_width, crc_width, polynomial, initial=0):
        self.i_data_payload = Signal("i_data_payload", data_width)
        self.i_data_strobe = Signal("i_data_strobe")
        self.o_crc = Signal("o_crc", crc_width)
        crc_dat = Signal("crc_dat", data_width)
        crc_cur = Signal("crc_cur", crc_width, reset=initial)
        crc_next = Signal("crc_next", crc_width, reset_less=True)

        crc_cur_reset_bits = [int(i) for i in "{0:0{width}b}".format(crc_cur.reset.value, width=crc_width)[::-1]]

        self.comb += [
            crc_dat.eq(self.i_data_payload[::-1]),
            # FIXME: Is XOR ^ initial actually correct here?
            self.o_crc.eq(crc_cur[::-1] ^ initial),
        ]

        self.sync += [
            If(self.i_data_strobe,
                crc_cur.eq(crc_next),
            ),
        ]

        poly_list = []
        for i in range(crc_width):
            poly_list.insert(0, polynomial >> i & 0x1)

        _, cols_nin, cols_min = build_matrix(poly_list, data_width)

        crc_next_reset_bits = list(crc_cur_reset_bits)
        for i in range(crc_width):
            to_xor = []
            crc_next_reset_bit_i = []
            for j, use in enumerate(cols_nin[i]):
                if use:
                    to_xor.append(crc_dat[j])
                    crc_next_reset_bit_i.append(0)
            for j, use in enumerate(cols_min[i]):
                if use:
                    to_xor.append(crc_cur[j])
                    crc_next_reset_bit_i.append(crc_cur_reset_bits[j])

            crc_next_reset_bits[i] = reduce(operator.xor, crc_next_reset_bit_i)

            self.comb += [
                crc_next[i].eq(reduce(operator.xor, to_xor)),
            ]

        crc_next_reset_value = int("0b"+"".join(str(i) for i in crc_next_reset_bits[::-1]), 2)
        crc_next.reset.value = crc_next_reset_value

class TxPipeline(Module):
    def __init__(self):
        self.i_bit_strobe = Signal("i_bit_strobe")

        self.i_data_payload = Signal("i_data_payload", 8)
        self.o_data_strobe = Signal("o_data_strobe")

        self.i_oe = Signal("i_oe")

        self.o_usbp = Signal("o_usbp")
        self.o_usbn = Signal("o_usbn")
        self.o_oe = Signal("o_oe")

        self.o_pkt_end = Signal("o_pkt_end")

        tx_pipeline_fsm = FSM()
        self.submodules.tx_pipeline_fsm = ClockDomainsRenamer("usb_12")(tx_pipeline_fsm)
        shifter = TxShifter(width=8)
        self.submodules.shifter = ClockDomainsRenamer("usb_12")(shifter)
        bitstuff = TxBitstuffer()
        self.submodules.bitstuff = ClockDomainsRenamer("usb_12")(bitstuff)
        nrzi = TxNRZIEncoder()
        self.submodules.nrzi = ClockDomainsRenamer("usb_48")(nrzi)

        sync_pulse = Signal("sync_pulse", 8)

        self.fit_dat = fit_dat = Signal("fit_dat")
        self.fit_oe  = fit_oe  = Signal("fit_oe")

        da_reset_shifter = Signal("da_reset_shifter")
        da_reset_bitstuff = Signal("da_reset_bitstuff") # Need to reset the bit stuffer 1 cycle after the shifter.
        stall = Signal("stall")

        # These signals are set during the sync pulse
        sp_reset_bitstuff = Signal("sp_reset_bitstuff")
        sp_reset_shifter = Signal("sp_reset_shifter")
        sp_bit = Signal("sp_bit")
        sp_o_data_strobe = Signal("sp_o_data_strobe")

        # 12MHz domain
        da_stalled_reset = Signal("da_stalled_reset")
        bitstuff_valid_data = Signal("bitstuff_valid_data")

        # Keep a Gray counter around to smoothly transition between states
        state_gray = Signal("state_gray", 2)
        state_data = Signal("state_data")
        state_sync = Signal("state_sync")

        self.comb += [
            shifter.i_data.eq(self.i_data_payload),
            # Send a data strobe when we're two bits from the end of the sync pulse.
            # This is because the pipeline takes two bit times, and we want to ensure the pipeline has spooled up enough by the time we're there.

            shifter.reset.eq(da_reset_shifter | sp_reset_shifter),
            shifter.ce.eq(~stall),

            bitstuff.reset.eq(da_reset_bitstuff),
            bitstuff.i_data.eq(shifter.o_data),
            stall.eq(bitstuff.o_stall),

            sp_bit.eq(sync_pulse[0]),
            sp_reset_bitstuff.eq(sync_pulse[0]),

            # The shifter has one clock cycle of latency, so reset it one cycle before the end of the sync byte.
            sp_reset_shifter.eq(sync_pulse[1]),

            sp_o_data_strobe.eq(sync_pulse[5]),

            state_data.eq(state_gray[0] & state_gray[1]),
            state_sync.eq(state_gray[0] & ~state_gray[1]),

            fit_oe.eq(state_data | state_sync),
            fit_dat.eq((state_data & shifter.o_data & ~bitstuff.o_stall) | sp_bit),
            self.o_data_strobe.eq((state_data & shifter.o_get & ~stall & self.i_oe) | sp_o_data_strobe),
        ]

        # If we reset the shifter, then o_empty will go high on the next cycle.

        self.sync.usb_12 += [
            # If the shifter runs out of data, percolate the "reset" signal to the shifter, and then down to the bitstuffer.
            # da_reset_shifter.eq(~stall & shifter.o_empty & ~da_stalled_reset),
            # da_stalled_reset.eq(da_reset_shifter),
            # da_reset_bitstuff.eq(~stall & da_reset_shifter),
            bitstuff_valid_data.eq(~stall & shifter.o_get & self.i_oe),
        ]

        tx_pipeline_fsm.act("IDLE",
            If(self.i_oe,
                NextState("SEND_SYNC"),
                NextValue(sync_pulse, 1 << 7),
                NextValue(state_gray, 0b01),
            ).Else(
                NextValue(state_gray, 0b00),
            )
        )

        tx_pipeline_fsm.act("SEND_SYNC",
            NextValue(sync_pulse, sync_pulse >> 1),

            If(sync_pulse[0],
                NextState("SEND_DATA"),
                NextValue(state_gray, 0b11),
            ).Else(
                NextValue(state_gray, 0b01),
            ),
        )

        tx_pipeline_fsm.act("SEND_DATA",
            If(~self.i_oe & shifter.o_empty & ~bitstuff.o_stall,
                If(bitstuff.o_will_stall,
                    NextState("STUFF_LAST_BIT")
                ).Else(
                    NextValue(state_gray, 0b10),
                    NextState("IDLE"),
                )
            ).Else(
                NextValue(state_gray, 0b11),
            ),
        )

        tx_pipeline_fsm.act("STUFF_LAST_BIT",
            NextValue(state_gray, 0b10),
            NextState("IDLE"),
        )

        # 48MHz domain NRZI encoding
        nrzi_dat = Signal("nrzi_dat")
        nrzi_oe = Signal("nrzi_oe")

        # Cross the data from the 12MHz domain to the 48MHz domain
        cdc_dat = MultiReg(fit_dat, nrzi_dat, odomain="usb_48", n=3)
        cdc_oe  = MultiReg(fit_oe, nrzi_oe, odomain="usb_48", n=3)
        self.specials += [cdc_dat, cdc_oe]

        self.comb += [
            nrzi.i_valid.eq(self.i_bit_strobe),
            nrzi.i_data.eq(nrzi_dat),
            nrzi.i_oe.eq(nrzi_oe),

            self.o_usbp.eq(nrzi.o_usbp),
            self.o_usbn.eq(nrzi.o_usbn),
            self.o_oe.eq(nrzi.o_oe),
        ]

class PacketHeaderDecode(Module):
    def __init__(self, rx):
        self.submodules.rx = rx

        self.o_pid = Signal("o_pid", 4)
        self.o_addr = Signal("o_addr", 7)
        endp4 = Signal("endp4")
        self.o_endp = Signal("o_endp", 4)
        crc5 = Signal("crc5", 5)
        self.o_decoded = Signal("o_decoded")

        # FIXME: This whole module should just be in the usb_12 clock domain?
        self.submodules.fsm = fsm = ClockDomainsRenamer("usb_12")(FSM())
        fsm.act("IDLE",
            If(rx.o_pkt_start,
                NextState("WAIT_PID"),
            ),
        )
        pid = rx.o_data_payload[0:4]
        fsm.act("WAIT_PID",
            If(rx.o_data_strobe,
                NextValue(self.o_pid, pid),
                Case(pid & PIDTypes.TYPE_MASK, {
                    PIDTypes.TOKEN:     NextState("WAIT_BYTE0"),
                    PIDTypes.DATA:      NextState("END"),
                    PIDTypes.HANDSHAKE: NextState("END"),
                }),
            ),
        )
        fsm.act("WAIT_BYTE0",
            If(rx.o_data_strobe,
                NextValue(self.o_addr[0:7], rx.o_data_payload[0:7]),
                NextValue(endp4, rx.o_data_payload[7]),
                NextState("WAIT_BYTE1"),
            ),
        )
        fsm.act("WAIT_BYTE1",
            If(rx.o_data_strobe,
                NextValue(self.o_endp, Cat(endp4, rx.o_data_payload[0:3])),
                NextValue(crc5, rx.o_data_payload[4:]),
                NextState("END"),
            ),
        )
        fsm.act("END",
            self.o_decoded.eq(1),
            NextState("IDLE"),
        )

class TxPacketSend(Module):
    def __init__(self, tx, auto_crc=True):
        self.submodules.tx = tx

        self.i_pkt_start = Signal("i_pkt_start")
        self.o_pkt_end = Signal("o_pkt_end")

        self.i_pid = Signal("i_pid", 4)
        self.i_data_payload = Signal("i_data_payload", 8)
        self.i_data_ready = Signal("i_data_ready")
        self.o_data_ack = Signal("o_data_ack")

        o_oe12 = Signal("o_oe12")
        self.specials += MultiReg(tx.o_oe, o_oe12, odomain="usb_12", n=1)

        pid = Signal("pid", 4)

        fsm = FSM()
        self.submodules.fsm = fsm = ClockDomainsRenamer("usb_12")(fsm)
        fsm.act("IDLE",
            NextValue(tx.i_oe, self.i_pkt_start),
            If(self.i_pkt_start,
                # If i_pkt_start is set, then send the next packet.
                # We pre-queue the SYNC byte here to cut down on latency.
                NextState("QUEUE_SYNC"),
            ).Else(
                NextValue(tx.i_oe, 0),
            )
        )

        # Send the QUEUE_SYNC byte
        fsm.act("QUEUE_SYNC",
            # The PID might change mid-sync, because we're still figuring out what the response ought to be.
            NextValue(pid, self.i_pid),
            tx.i_data_payload.eq(1),
            If(tx.o_data_strobe,
                NextState("QUEUE_PID"),
            ),
        )

        # Send the PID byte
        fsm.act("QUEUE_PID",
            tx.i_data_payload.eq(Cat(pid, pid ^ 0b1111)),
            If(tx.o_data_strobe,
                If(pid & PIDTypes.TYPE_MASK == PIDTypes.HANDSHAKE,
                    NextState("WAIT_TRANSMIT"),
                ).Elif(pid & PIDTypes.TYPE_MASK == PIDTypes.DATA,
                    NextState("QUEUE_DATA0"),
                ).Else(
                    NextState("ERROR"),
                ),
            ),
        )

        nextstate = 'WAIT_TRANSMIT'
        if auto_crc:
            nextstate = 'QUEUE_CRC0'

        fsm.act("QUEUE_DATA0",
            If(~self.i_data_ready,
                NextState(nextstate),
            ).Else(
                NextState("QUEUE_DATAn"),
            ),
        )

        # Keep transmitting data bytes until the i_data_ready signal is not high on a o_data_strobe event.
        fsm.act("QUEUE_DATAn",
            tx.i_data_payload.eq(self.i_data_payload),
            self.o_data_ack.eq(tx.o_data_strobe),
            If(~self.i_data_ready,
                NextState(nextstate),
            ),
        )

        if auto_crc:
            crc = TxParallelCrcGenerator(
                crc_width  = 16,
                data_width = 8,
                polynomial = 0b1000000000000101, # polynomial = (16, 15, 2, 0)
                initial    = 0b1111111111111111, # seed = 0xFFFF
            )
            self.submodules.crc = crc = ClockDomainsRenamer("usb_12")(crc)

            self.comb += [
                crc.i_data_payload.eq(self.i_data_payload),
                crc.reset.eq(fsm.ongoing("QUEUE_PID")),
                If(fsm.ongoing("QUEUE_DATAn"),
                    crc.i_data_strobe.eq(tx.o_data_strobe),
                ),
            ]

            fsm.act("QUEUE_CRC0",
                tx.i_data_payload.eq(crc.o_crc[:8]),
                If(tx.o_data_strobe,
                    NextState("QUEUE_CRC1"),
                ),
            )
            fsm.act("QUEUE_CRC1",
                tx.i_data_payload.eq(crc.o_crc[8:]),
                If(tx.o_data_strobe,
                    NextState("WAIT_TRANSMIT"),
                ),
            )

        fsm.act("WAIT_TRANSMIT",
            NextValue(tx.i_oe, 0),
            If(~o_oe12,
                self.o_pkt_end.eq(1),
                NextState("IDLE"),
            ),
        )

        fsm.act("ERROR")

class UsbTransfer(Module):
    def __init__(self, iobuf, auto_crc=True):
        self.submodules.iobuf = ClockDomainsRenamer("usb_48")(iobuf)

        self.submodules.tx = tx = TxPipeline()
        self.submodules.txstate = txstate = TxPacketSend(tx, auto_crc=auto_crc)

        self.submodules.rx = rx = RxPipeline()
        self.submodules.rxstate = rxstate = PacketHeaderDecode(rx)

        # USB 48MHz bit strobe
        self.comb += [
            tx.i_bit_strobe.eq(rx.o_bit_strobe),
        ]

        # Whether to reset the FSM
        self.reset = Signal("reset")

        # The state of the USB reset (SE0) signal
        self.usb_reset = Signal("usb_reset")
        self.comb += self.usb_reset.eq(rx.o_reset)

        # Data paths
        self.data_recv_put = Signal("data_recv_put")
        self.data_recv_payload = Signal("data_recv_payload", 8)

        self.data_send_get = Signal("data_send_get")
        self.data_send_have = Signal("data_send_have")
        self.data_send_payload = Signal("data_send_payload", 8)

        # State signally
        # The value of these signals are generally dependent on endp, so we need to wait for the rdy signal to use them.
        self.rdy  = Signal("rdy", reset=1)
        self.dtb  = Signal("dtb")
        self.arm  = Signal("arm")
        self.sta  = Signal("sta")
        self.addr = Signal("addr", 7) # If the address doesn't match, we won't respond

        # Tristate
        self.submodules.iobuf = iobuf
        self.comb += [
            rx.i_usbp.eq(iobuf.usb_p_rx),
            rx.i_usbn.eq(iobuf.usb_n_rx),
            iobuf.usb_tx_en.eq(tx.o_oe),
            iobuf.usb_p_tx.eq(tx.o_usbp),
            iobuf.usb_n_tx.eq(tx.o_usbn),
        ]

        self.tok  = Signal("tok", 4)  # Contains the transfer token type
        self.endp = Signal("endp", 4)

        self.idle     = Signal("idle", reset=0) # Asserted when in the "WAIT_TOKEN" state
        self.start    = Signal("start")         # Asserted when a transfer is starting
        self.poll     = Signal("poll")          # Asserted when polling for a response (i.e. one cycle after self.start)
        self.setup    = Signal("setup")         # Asserted when a transfer is a setup
        self.commit   = Signal("commit")        # Asserted when a transfer succeeds
        self.retry    = Signal("retry")         # Asserted when the host sends an IN without an ACK
        self.abort    = Signal("abort")         # Asserted when a transfer fails
        self.end      = Signal("end")           # Asserted when transfer ends
        self.data_end = Signal("data_end")      # Asserted when a DATAx transfer finishes
        self.error    = Signal("error")         # Asserted when in the ERROR state

        self.comb += [
            self.end.eq(self.commit | self.abort),
        ]

        # Host->Device data path (Out + Setup data path)
        #
        # Token
        # Data
        # Handshake
        #
        # Setup --------------------
        # >Setup
        # >Data0[bmRequestType, bRequest, wValue, wIndex, wLength]
        # <Ack
        # --------------------------
        #
        # Data ---------------------
        # >Out        >Out        >Out
        # >DataX[..]  >DataX[..]  >DataX
        # <Ack        <Nak        <Stall
        #
        # Status -------------------
        # >Out
        # >Data0[]
        # <Ack
        # ---------------------------
        #
        # Host<-Device data path (In data path)
        # --------------------------
        # >In         >In     >In
        # <DataX[..]  <Stall  <Nak
        # >Ack
        # ---------------------------
        # >In
        # <Data0[]
        # >Ack
        # ---------------------------
        transfer = ResetInserter()(FSM(reset_state="WAIT_TOKEN"))
        self.submodules.transfer = transfer = ClockDomainsRenamer("usb_12")(transfer)
        self.comb += transfer.reset.eq(self.reset)
        transfer.act("ERROR",
            self.error.eq(1),
        )

        transfer.act("WAIT_TOKEN",
            self.idle.eq(1),
            If(rx.o_pkt_start,
                NextState("RECV_TOKEN"),
            ),
        )

        transfer.act("RECV_TOKEN",
            self.idle.eq(0),
            If(rxstate.o_decoded,
                # If the address doesn't match, go back and wait for a new token.
                If(rxstate.o_addr != self.addr,
                    NextState("WAIT_TOKEN"),
                ).Else(
                    self.start.eq(1),
                    NextValue(self.tok,  rxstate.o_pid),
                    NextValue(self.endp, rxstate.o_endp),
                    NextState("POLL_RESPONSE"),
                ),
            ),
        )

        response_pid = Signal("response_pid", 4)
        transfer.act("POLL_RESPONSE",
            self.poll.eq(1),
            If(self.rdy,
                # Work out the response
                If(self.tok == PID.SETUP,
                    NextValue(response_pid, PID.ACK),
                ).Elif(self.sta,
                    NextValue(response_pid, PID.STALL),
                ).Elif(self.arm,
                    NextValue(response_pid, PID.ACK),
                ).Else(
                    NextValue(response_pid, PID.NAK),
                ),

                If(rxstate.o_pid == PID.SOF,
                    NextState("WAIT_TOKEN"),
                ).Elif(self.tok == PID.SETUP,
                    NextState("WAIT_DATA"),
                ).Elif(self.tok == PID.OUT,
                    NextState("WAIT_DATA"),
                ).Elif(self.tok == PID.IN,
                    If(~self.arm | self.sta,
                        NextState("SEND_HAND"),
                    ).Else(
                        NextState("SEND_DATA"),
                    ),
                ).Else(
                    NextState("WAIT_TOKEN"),
                ),
            ),
        )

        # Out + Setup pathway
        transfer.act("WAIT_DATA",
            If(rxstate.o_decoded,
                If((rxstate.o_pid & PIDTypes.TYPE_MASK) == PIDTypes.DATA,
                    NextState("RECV_DATA"),
                ).Elif(rxstate.o_pid == PID.SOF,
                    NextState("WAIT_DATA"),
                ).Else(
                    NextState("ERROR"),
                )
            ),
        )

        transfer.act("RECV_DATA",
            # If we've indicated that we'll accept the data, put it into data_recv_payload and strobe data_recv_put every time a full byte comes in.
            If(response_pid == PID.ACK,
                self.data_recv_put.eq(rx.o_data_strobe),
            ),
            If(rx.o_pkt_end,
                NextState("SEND_HAND"),
            ),
        )
        self.comb += [
            self.data_recv_payload.eq(rx.o_data_payload),
        ]

        # In pathway
        transfer.act("SEND_DATA",
            If(self.dtb,
                txstate.i_pid.eq(PID.DATA1),
            ).Else(
                txstate.i_pid.eq(PID.DATA0),
            ),
            self.data_send_get.eq(txstate.o_data_ack),
            self.data_end.eq(txstate.o_pkt_end),
            If(txstate.o_pkt_end, NextState("WAIT_HAND")),
        )
        self.comb += [
            txstate.i_data_payload.eq(self.data_send_payload),
            txstate.i_data_ready.eq(self.data_send_have),
        ]

        # Handshake
        transfer.act("WAIT_HAND",
            If(rxstate.o_decoded,
                self.commit.eq(1),
                If(rxstate.o_pid == PID.ACK,
                    NextState("WAIT_TOKEN"),
                ).Elif(rxstate.o_pid == PID.IN,
                    self.retry.eq(1),
                    NextState("SEND_DATA"),
                ).Else(
                    NextState("ERROR"),
                )
            ),
        )
        transfer.act("SEND_HAND",
            txstate.i_pid.eq(response_pid),
            If(txstate.o_pkt_end,
                self.setup.eq(self.tok == PID.SETUP),
                If(response_pid == PID.ACK,
                    self.commit.eq(1),
                ).Else(
                    self.abort.eq(1),
                ),
                NextState("WAIT_TOKEN"),
            ),
        )

        # Code to reset header decoder when entering the WAIT_XXX states.
        self.comb += [
            If(tx.o_oe,
                rx.reset.eq(1),
            ),
        ]

        # Code to initiate the sending of packets when entering the SEND_XXX states.
        self.comb += [
            If(transfer.before_entering("SEND_DATA"),
                If(self.dtb,
                    txstate.i_pid.eq(PID.DATA1),
                ).Else(
                    txstate.i_pid.eq(PID.DATA0),
                ),
                txstate.i_pkt_start.eq(1),
            ),
            If(transfer.before_entering("SEND_HAND"),
                txstate.i_pid.eq(response_pid),
                txstate.i_pkt_start.eq(1),
            ),
        ]

# USB Wishbone Bridge
#
# This bridge provides a transparent bridge to the target device's Wishbone bus over USB.
# It can operate without interfering with the device's USB stack. It is simple enough to
# be able to work even if the USB stack is not enumerated, though the host may not cooperate.
#
# USB Wishbone Debug Protocol
#
# The protocol transfers four bytes a time in big-endian (i.e. USB) order. It uses SETUP packets
# with the special type (0x43) as an attention word. This is then followed by an OUT packet.
#
#     Write to Wishbone
#
#     { "signal": [
#         ["Request",
#             {  "name": 'data',        "wave": 'x222...22x', "data": '0x43 0x00 [ADDRESS] 0x04 0x00'   },
#             {  "name": 'data bits',   "wave": 'xxx2222xxx', "data": '7:0 15:8 23:16 31:24'},
#             {  "name": 'usb meaning', "wave": 'x222.2.2.x', "data": 'bReq bTyp wValue wIndex wLength' },
#             {  "name": 'usb byte',    "wave": 'x22222222x', "data": '1 2 3 4 5 6 7 8'                 }
#         ],
#         {},
#         ["Payload",
#             {  "name": 'data',        "wave": 'x3...x', "data": '[DATA]'},
#             {  "name": 'data bits',   "wave": 'x3333x', "data": '7:0 15:8 23:16 31:24'},
#             {  "name": 'usb meaning', "wave": 'x3...x', "data": 'OUT'  },
#             {  "name": 'usb byte',    "wave": 'x3333x', "data": '1 2 3 4'}
#         ]
#     ]}
#
# To read data from the device, set the top bit of the bRequestType, followed by an IN packet.
#
#     Read from Wishbone
#
#     { "signal": [
#         ['Request',
#             {  "name": 'data',        "wave": 'x222...22x', "data": '0xC3 0x00 [ADDRESS] 0x04 0x00'   },
#             {  "name": 'data bits',   "wave": 'xxx2222xxx', "data": '7:0 15:8 23:16 31:24'},
#             {  "name": 'usb meaning', "wave": 'x222.2.2.x', "data": 'bReq bTyp wValue wIndex wLength' },
#             {  "name": 'usb byte',    "wave": 'x22222222x', "data": '1 2 3 4 5 6 7 8'                 }
#         ],
#         {},
#         ["Payload",
#             {  "name": 'data',        "wave": 'x5...x', "data": '[DATA]'},
#             {  "name": 'data bits',   "wave": 'x5555x', "data": '7:0 15:8 23:16 31:24'},
#             {  "name": 'usb meaning', "wave": 'x5...x', "data": 'IN'  },
#             {  "name": 'usb byte',    "wave": 'x5555x', "data": '1 2 3 4'}
#         ]
#     ]}

class USBWishboneBridge(Module):

    def __init__(self, usb_core, clk_freq=12000000, magic_packet=0x43, cdc=False):
        self.wishbone = WishboneInterface()

        byte_counter = Signal("byte_counter", 3, reset_less=True)
        byte_counter_reset = Signal("byte_counter_reset")
        byte_counter_ce = Signal("byte_counter_ce")
        self.sync.usb_12 += If(byte_counter_reset, byte_counter.eq(0)).Elif(byte_counter_ce, byte_counter.eq(byte_counter + 1))

        # Unlike the UART or Ethernet bridges, we explicitly only support two commands: reading and writing.
        # This gets integrated into the USB protocol, so it's not really a state. 1 is "USB Device to Host",
        # and is therefore a "read", while 0 is "USB Host to Device", and is therefore a "write".
        cmd = Signal("cmd", 1, reset_less=True)
        cmd_ce = Signal("cmd_ce")

        # Add a bridge to allow this module (in the usb_12 domain) to access the main Wishbone bridge (potentially in some other domain).
        # Ensure this bridge is placed in the "sys" domain.
        send_to_wishbone = Signal("send_to_wishbone")
        reply_from_wishbone = Signal("reply_from_wishbone")
        transfer_active = Signal("transfer_active")
        if cdc:
            self.submodules.wb_cd_bridge = wb_cd_bridge = FSM(reset_state="IDLE")
            self.submodules.usb_to_wb = usb_to_wb = PulseSynchronizer("usb_12", "sys")
            self.submodules.wb_to_uwb = wb_to_usb = PulseSynchronizer("sys", "usb_12")
            send_to_wishbone = usb_to_wb.i
            reply_from_wishbone = wb_to_usb.o
        else:
            self.comb += [
                If(send_to_wishbone | transfer_active, self.wishbone.stb.eq(1), self.wishbone.we.eq(~cmd), self.wishbone.cyc.eq(1)),
                reply_from_wishbone.eq(self.wishbone.ack | self.wishbone.err),
            ]

        # Instead of self.source and self.sink, we let the wrapping module handle packing and unpacking the data.
        self.sink_data = Signal("sink_data", 8)

        # True when the "sink" value has data
        self.sink_valid = Signal("sink_valid")

        self.send_ack = Signal("send_ack")

        # Indicates whether a "debug" packet is currently being processed
        self.n_debug_in_progress = Signal("n_debug_in_progress", reset=1)

        address = Signal("address", 32, reset_less=True)
        address_ce = Signal("address_ce")

        data = Signal("data", 32, reset_less=True)
        rd_data = Signal("rd_data", 32, reset_less=True)
        rx_data_ce = Signal("rx_data_ce")

        # wishbone_response = Signal("wishbone_response", 32, reset_less=True)
        self.sync.usb_12 += [
            If(cmd_ce, cmd.eq(usb_core.data_recv_payload[7:8])),
            If(address_ce, address.eq(Cat(address[8:32], usb_core.data_recv_payload))),
            If(rx_data_ce, data.eq(Cat(data[8:32], usb_core.data_recv_payload)))
        ]

        # The Litex Wishbone dat_r line is a shared medium, meaning the value changes often.
        # Capture our own copy of this data when a wishbone ACK occurs.
        self.sync.sys += [ If(self.wishbone.ack, rd_data.eq(self.wishbone.dat_r)) ]

        fsm = ResetInserter()(ClockDomainsRenamer("usb_12")(FSM(reset_state="IDLE")))
        self.submodules += fsm
        fsm.act("IDLE",
            self.n_debug_in_progress.eq(1),
            If(usb_core.data_recv_put,
                If(usb_core.tok == PID.SETUP,
                    If(usb_core.endp == 0,
                        # If we get a SETUP packet with a "Vendor" type going to this device, treat that as a DEBUG packet.
                        cmd_ce.eq(1),
                        byte_counter_reset.eq(1),
                        If(usb_core.data_recv_payload[0:7] == magic_packet,
                            NextState("RECEIVE_ADDRESS"),
                        ).Else(
                            # Wait for the end of the packet, to avoid messing with normal USB operation
                            NextState("WAIT_PKT_END"),
                        ),
                    )
                )
            )
        )

        # The target address comes as the wValue and wIndex in the SETUP packet. Once we get that data, we're ready to do the operation.
        fsm.act("RECEIVE_ADDRESS",
            self.n_debug_in_progress.eq(0),
            If(usb_core.data_recv_put,
                byte_counter_ce.eq(1),
                If((byte_counter >= 1),
                    If((byte_counter <= 4),
                        address_ce.eq(1),
                    ),
                ),
            ),
            # We don't need to explicitly ACK the SETUP packet, because they're always acknowledged implicitly.
            # Wait until the packet ends (i.e. until we've sent the ACK packet) before moving to the next state.
            If(usb_core.end,
                byte_counter_reset.eq(1),
                If(cmd,
                    send_to_wishbone.eq(1),
                    NextState("READ_DATA"),
                ).Else(
                    NextState("RECEIVE_DATA"),
                ),
            ),
        )

        fsm.act("RECEIVE_DATA",
            # Set the "ACK" bit to 1, so we acknowledge the packet once it comes in, and so that we're in a position to receive data.
            self.send_ack.eq(usb_core.endp == 0),
            self.n_debug_in_progress.eq(0),
            If(usb_core.endp == 0,
                If(usb_core.data_recv_put,
                    rx_data_ce.eq(1),
                    byte_counter_ce.eq(1),
                    If(byte_counter == 3,
                        NextState("WAIT_RECEIVE_DATA_END"),
                    ).Elif(usb_core.end,
                        send_to_wishbone.eq(1),
                        NextState("WRITE_DATA"),
                    )
                )
            )
        )

        fsm.act("WAIT_RECEIVE_DATA_END",
            self.n_debug_in_progress.eq(0),
            self.send_ack.eq(1),
            # Wait for the end of the USB packet, if it hasn't come already.
            If(usb_core.end,
                send_to_wishbone.eq(1),
                NextState("WRITE_DATA")
            )
        )

        if cdc:
            wb_cd_bridge.act("IDLE", If(usb_to_wb.o, NextState("DO_OP")))
            wb_cd_bridge.act("DO_OP",
                self.wishbone.stb.eq(1),
                self.wishbone.we.eq(~cmd),
                self.wishbone.cyc.eq(1),
                If(self.wishbone.ack | self.wishbone.err,
                    NextState("IDLE"),
                    wb_to_usb.i.eq(1),
                ),
            )

        self.comb += [
            # Trim off the last two bits of the address, because wishbone addresses are word-based, and a word is 32-bits.
            # Therefore, the last two bits should always be zero.
            self.wishbone.adr.eq(address[2:]),
            self.wishbone.dat_w.eq(data),
            self.wishbone.sel.eq(2**len(self.wishbone.sel) - 1)
        ]

        fsm.act("WRITE_DATA",
            self.n_debug_in_progress.eq(0),
            transfer_active.eq(1),
            If(reply_from_wishbone,
                NextState("WAIT_SEND_ACK_START"),
            )
        )

        fsm.act("READ_DATA",
            self.n_debug_in_progress.eq(0),
            transfer_active.eq(1),
            If(reply_from_wishbone,
                NextState("SEND_DATA_WAIT_START")
            )
        )

        fsm.act("SEND_DATA_WAIT_START",
            self.n_debug_in_progress.eq(0),
            byte_counter_reset.eq(1),
            If(usb_core.start,
                NextState("SEND_DATA"),
            ),
        )

        self.comb += chooser(rd_data, byte_counter, self.sink_data, n=4, reverse=False)

        fsm.act("SEND_DATA",
            self.n_debug_in_progress.eq(0),
            If(usb_core.endp != 0,
                NextState("SEND_DATA_WAIT_START"),
            ),

            # Keep sink_valid high during the packet, which indicates we have data to send.
            # This also causes an "ACK" to be transmitted.
            self.sink_valid.eq(usb_core.endp == 0),
            If(usb_core.data_send_get, byte_counter_ce.eq(1)),
            If(byte_counter == 4,
                NextState("WAIT_SEND_ACK_START")
            ),
            If(usb_core.end,
                NextState("WAIT_SEND_ACK_START")
            )
        )

        # To validate the transaction was successful, the host will now send an "IN" request.
        # Acknowledge that by setting self.send_ack, without putting anything in self.sink_data.
        fsm.act("WAIT_SEND_ACK_START",
            self.n_debug_in_progress.eq(0),
            If(usb_core.start,
                NextState("SEND_ACK")
            ),
        )

        # Send the ACK. If the endpoint number is incorrect, go back and wait again.
        fsm.act("SEND_ACK",
            self.n_debug_in_progress.eq(0),
            If(usb_core.endp != 0,
                NextState("WAIT_SEND_ACK_START")
            ),
            # If(usb_core.retry,
            #     If(cmd,
            #         byte_counter_reset.eq(1),
            #         NextState("SEND_DATA"),
            #     ),
            # ),
            self.send_ack.eq(usb_core.endp == 0),
            If(usb_core.end,
                NextState("IDLE"),
            )
        )

        fsm.act("WAIT_PKT_END",
            self.n_debug_in_progress.eq(1),
            If(usb_core.end,
                NextState("IDLE"),
            )
        )

# Register Interface:
#
# pullup_out_read: Read the status of the USB "FS" pullup.
# pullup_out_write: Write the USB "FS" pullup state
#
# SETUP - Responding to a SETUP packet from the host
# setup_read: Read the contents of the last SETUP transaction
# setup_ack: Write a "1" here to advance the data_read fifo
# setup_empty: "0" if there is no SETUP data.
# setup_epno: The endpoint the SETUP packet was destined for
#
# EPOUT - Data from the host to this device
# epout_data_read: Read the contents of the last transaction on the EP0
# epout_data_ack: Write a "1" here to advance the data_read fifo
# epout_last_tok: Bits 2 and 3 of the last token, from the following table:
#     USB_PID_OUT   = 0
#     USB_PID_SOF   = 1
#     USB_PID_IN    = 2
#     USB_PID_SETUP = 3
# epout_epno: Which endpoint contained the last data
# epout_queued: A response is queued and has yet to be acknowledged by the host
#
# EPIN - Requests from the host to read data from this device
# epin_data_write: Write 8 bits to the EP0 queue
# epin_data_empty: Return 1 if the queue is empty
# epin_epno: Which endpoint the data is for. You must write this byte to indicate data is ready to be sent.
# epin_queued: A response is queued and has yet to be acknowledged by the host
#
# ep_stall: a 32-bit field representing endpoitns to respond with STALL.

class TriEndpointInterface(Module, AutoCSR):

    # Implements a CPU interface with three FIFOs: SETUP, IN, OUT
    #
    # Each of the three FIFOs has a relatively similar register set.
    #
    # iobuf (:obj:io.IoBuf): PHY interface to the raw pins.
    #     This object encapsulate the pin interface to the outside world so that TriEndpointInterface does not need to have platform-specific IO handling.
    #
    # cdc (bool, optional): By default, eptri assumes that the CSR bus is in the same 12 MHz clock domain as the USB stack.
    #     If cdc is set to True, then additional buffers will be placed on the .we and .re lines to handle this difference.
    #
    # This is a three-FIFO USB device. It presents one FIFO each for IN, OUT and SETUP data.
    # This allows for up to 16 IN and 16 OUT endpoints without sacrificing many FPGA resources.
    #
    # USB supports four types of transfers: control, bulk, interrupt, and isochronous.
    # This device does not yet support isochronous transfers, however it supports the other types of transfers.
    #
    # Interrupt and bulk transfers are similar from an implementation standpoint -- they differ only in terms of how often they are transmitted.
    #
    # These transfers can be made to any endpoint, and may even be interleaved. However, due to the nature of TriEndpointInterface any attempt by
    # the host to interleave transfers will result in a NAK, and the host will retry later when the buffer is empty.
    #
    # To make an IN transfer (i.e. to send data to the host), write the data to IN_DATA. This is a FIFO, and each write to this endpoint will
    # advance the FIFO pointer automatically. This FIFO is 64 bytes deep. USB DATA packets contain a CRC16 checksum, which is automatically added
    # to any IN transfers.
    #
    # TriEndpointInterface will continue to respond NAK until you arm the buffer. Do this by writing the endpoint number to IN_CTRL.EPNO.
    # This will tell the device that it should send the data the next time the host asks for it.
    #
    # Once the data has been transferred, the device will raise an interrupt and you can begin re-filling the buffer, or fill it with data for a different endpoint.
    #
    # To send an empty packet, avoid writing any data to IN_DATA and simply write the endpoint number to IN_CTRL.EPNO.
    #
    # The CRC16 will be automatically appended to the end of the transfer.
    #
    # To respond to an OUT transfer (i.e. to receive data from the host), enable a particular endpoint by writing to OUT_CTRL.EPNO with the OUT_CTRL.ENABLE bit set.
    # This will tell the device to stop responding NAK to that particular endpoint and to accept any incoming data into a 66-byte FIFO, provided the FIFO is empty.
    #
    # Once the host sends data, an interrupt will be raised and that particular endpoint's ENABLE will be set to 0. This prevents any additional data from entering
    # the FIFO while the device examines the data.
    #
    # The FIFO will contain two extra bytes, which are the two-byte CRC16 of the packet.
    # You can safely discard these bytes. Because of this, a zero-byte transfer will be two-bytes, and a full 64-byte transfer will be 66 bytes.
    #
    # To determine which endpoint the OUT packet was sent to, refer to OUT_STATUS.EPNO.
    # This field is only updated when a successful packet is received, and will not change until the OUT FIFO is re-armed.
    #
    # The OUT FIFO will continue to respond to the host with with NAK until the OUT_EV_PENDING.DONE bit is cleared.
    #
    # Additionally, to continue receiving data on that particular endpoint, you will need to re-enable it by writing the endpoint
    # number, along with the OUT_CTRL.ENABLE to OUT_CTRL.
    #
    # Control transfers are complicated, and are the first sort of transfer that the host uses. Such transfers have three distinct phases.
    #
    # The first phase is the SETUP phase, where the host sends an 8-byte SETUP packet. These SETUP packets must always be acknowledged,
    # so any such packet from the host will get loaded into the SETUP FIFO immediately, and an interrupt event raised. If, for some reason,
    # the device hasn't drained this SETUP FIFO from a previous transaction, the FIFO will be cleared automatically.
    #
    # Once the SETUP packet is handled, the host will send an IN or OUT packet. If the host sends an OUT packet, then the OUT buffer
    # must be cleared, the OUT.DONE interrupt handled, and the OUT_CTRL.ENABLE bit must be set for the appropriate endpoint, usually EP0.
    # The device will not accept any data as long as these three conditions are not met.
    #
    # If the host sends an IN packet, the device will respond with NAK if no data has queued.
    # To queue data, fill the IN_DATA buffer, then write 0 to IN_CTRL.
    #
    # You can continue to fill the buffer (for IN packets) or drain the buffer and re-enable the endpoint (for OUT packets)
    # until the host has finished the transfer.
    #
    # When the host has finished, it will send the opposite packet type. If it is making IN transfers, it will send a single OUT packet,
    # or if it is making OUT transfers it will send a single IN packet. You must handle this transaction yourself.
    #
    # When the host sends a request that cannot be processed -- for example requesting a descriptor that does not exist -- the device must respond with STALL.
    #
    # Each endpoint keeps track of its own STALL state, though a SETUP packet will clear the STALL state for the specified endpoint (usually EP0).
    #
    # To set or clear the STALL bit of an IN endpoint, write its endpoint number to IN_CTRL.EPNO with the IN_CTRL.STALL bit either set or clear.
    # If this bit is set, then the device will respond to the next IN packet from the host to that particular endpoint with STALL. If the bit is clear,
    # then the next IN packet will be responded to with ACK and the contents of the IN FIFO.
    #
    # To stall an OUT endpoint, write to OUT_CTRL.EPNO with the OUT_CTRL.STALL bit set.
    # To unstall, write to OUT_CTRL.EPNO with the OUT_CTRL.STALL bit cleared.
    # Note that OUT_CTRL.ENABLE should not be set at the same time as OUT_CTRL.STALL, as this will cause a conflict.

    def __init__(self, iobuf, cdc=False):

        self.submodules.usb_core = usb_core = UsbTransfer(iobuf)

        self.submodules.pullup = GPIOOut(usb_core.iobuf.usb_pullup)
        self.iobuf = usb_core.iobuf

        ems = []

        # When the USB host sends a USB reset, set our address back to 0.
        self.address = ResetInserter()(CSRStorage("address",
            fields=[CSRField("addr", 7)], # Write the USB address from USB SET_ADDRESS packets
          )) # Sets the USB device address, in order to ignore packets going to other devices on the bus. This value is reset when the host issues a USB Device Reset condition.
        self.comb += self.address.reset.eq(usb_core.usb_reset)

        # In eptri, there are three endpoints. It is possible for an IRQ to fire and have all three bits set. Under these circumstances it can be difficult to know which event
        # to process first. Use this register to determine which event needs to be processed first. Only one bit will ever be set at a time.
        self.next_ev = CSRStatus("next_ev",
            fields=[
                CSRField("in", 1),
                CSRField("out", 1),
                CSRField("setup", 1),
                CSRField("reset", 1),
            ],
        )

        # Handlers
        self.submodules.setup = setup_handler = ClockDomainsRenamer("usb_12")(SetupHandler(usb_core))
        self.comb += setup_handler.usb_reset.eq(usb_core.usb_reset)
        ems.append(setup_handler.ev)

        in_handler = ClockDomainsRenamer("usb_12")(InHandler(usb_core))
        self.submodules.__setattr__("in", in_handler)
        ems.append(in_handler.ev)

        self.submodules.out = out_handler = ClockDomainsRenamer("usb_12")(OutHandler(usb_core))
        ems.append(out_handler.ev)

        self.submodules.ev = SharedIRQ(*ems)

        in_next = Signal("in_next")
        out_next = Signal("out_next")
        self.sync += [
            If(usb_core.usb_reset,
                in_next.eq(0),
                out_next.eq(0),
            # If the in_handler is set but not the out_handler, that one is next
            ).Elif(in_handler.ev.packet.pending & ~out_handler.ev.packet.pending,
                in_next.eq(1),
                out_next.eq(0),
            # If the out_handler is set first, mark that as next
            ).Elif(~in_handler.ev.packet.pending & out_handler.ev.packet.pending,
                in_next.eq(0),
                out_next.eq(1),
            # If neither is set, then clear the bits
            ).Elif(~in_handler.ev.packet.pending & ~out_handler.ev.packet.pending,
                in_next.eq(0),
                out_next.eq(0),
            ),
            # If both are set, don't do anything
        ]
        self.comb += [
            If(setup_handler.ev.reset.pending,
                self.next_ev.fields.reset.eq(1),
            ).Elif(in_next,
                getattr(self.next_ev.fields, "in").eq(1),
            ).Elif(out_next,
                self.next_ev.fields.out.eq(out_next),
            ).Elif(setup_handler.ev.packet.pending,
                self.next_ev.fields.setup.eq(1),
            )
        ]

        self.comb += usb_core.dtb.eq(in_handler.dtb)
        usb_core_reset = Signal("usb_core_reset")

        self.submodules.stage = stage = ClockDomainsRenamer("usb_12")(ResetInserter()(FSM(reset_state="IDLE")))
        self.comb += stage.reset.eq(usb_core.usb_reset)

        stage.act("IDLE",
            NextValue(usb_core.addr, self.address.storage),

            If(usb_core.start, NextState("CHECK_TOK"))
        )

        stage.act("CHECK_TOK",
            If(usb_core.idle,
                NextState("IDLE"),
            ).Elif(usb_core.tok == PID.SETUP,
                NextState("SETUP"),
                setup_handler.begin.eq(1),
                in_handler.dtb_reset.eq(1),
                # SETUP packets must be ACKed unconditionally
                usb_core.sta.eq(0),
                usb_core.arm.eq(1),
            ).Elif(usb_core.tok == PID.IN,
                NextState("IN"),
                usb_core.sta.eq(in_handler.stalled),
                usb_core.arm.eq(in_handler.response),
            ).Elif(usb_core.tok == PID.OUT,
                NextState("OUT"),
                usb_core.sta.eq(out_handler.stalled),
                usb_core.arm.eq(out_handler.response),
            ).Else(
                NextState("IDLE"),
            )
        )

        stage.act("SETUP",
            # SETUP packet
            setup_handler.data_recv_payload.eq(usb_core.data_recv_payload),
            setup_handler.data_recv_put.eq(usb_core.data_recv_put),

            # We aren't allowed to STALL a SETUP packet
            usb_core.sta.eq(0),

            # Always ACK a SETUP packet
            usb_core.arm.eq(1),

            If(usb_core.end, NextState("IDLE")),
        )

        stage.act("IN",
            If(usb_core.tok == PID.IN,
                # IN packet (device-to-host)
                usb_core.data_send_have.eq(in_handler.data_out_have),
                usb_core.data_send_payload.eq(in_handler.data_out),
                in_handler.data_out_advance.eq(usb_core.data_send_get),

                usb_core.sta.eq(in_handler.stalled),
                usb_core.arm.eq(in_handler.response),

                # After an IN transfer, the host sends an OUT packet. We must ACK this and then return to IDLE.
                If(usb_core.end, NextState("IDLE")),
            ),
        )

        stage.act("OUT",
            If(usb_core.tok == PID.OUT,
                # OUT packet (host-to-device)
                out_handler.data_recv_payload.eq(usb_core.data_recv_payload),
                out_handler.data_recv_put.eq(usb_core.data_recv_put),

                usb_core.sta.eq(out_handler.stalled),
                usb_core.arm.eq(out_handler.response),

                # After an OUT transfer, the host sends an IN packet. We must ACK this and then return to IDLE.
                If(usb_core.end, NextState("IDLE")),
            ),
        )

        self.comb += usb_core.reset.eq(usb_core.error | usb_core_reset)

# Handle SETUP packets
#
# SETUP packets must always respond with ACK. They are followed by a DATA0 packet, and may be followed by additional DATA stages.
#
# Since SETUP packets must always be handled, there is a separate FIFO that handles this data. Hence the name eptri.
#
# The device must always acknowledge the SETUP packet right away, but need not send the acknowledgement stage right away.
# You can use this to parse the data at a leisurely pace.
#
# When the device receives a SETUP transaction, an interrupt will fire and the SETUP_STATUS register will have SETUP_STATUS.HAVE set to 1.
# Drain the FIFO by reading from SETUP_DATA, then setting SETUP_CTRL.ADVANCE.
#
# reset : Signal
#     Asserting this resets the entire SetupHandler object. You should do this at boot, or if you're switching applications.
#
# begin : Signal
#     Assert this when a SETUP token is received. This will clear out the current buffer (if any) and prepare the endpoint to receive data.
#
# epno : Signal("...", 4)
#     The endpoint number the SETUP packet came in on (probably is always 0)
#
# is_in : Signal
#     This is a 1 if the SETUP packet will be followed by an IN stage.
#
# usb_reset : Signal
#     This signal feeds into the EventManager, which is used to indicate to the device that a USB reset has occurred.

class SetupHandler(Module, AutoCSR):
    def __init__(self, usb_core):

        self.reset = Signal("reset")
        self.begin = Signal("begin")
        self.epno = epno = Signal("epno")
        self.usb_reset = Signal("usb_reset")

        # Register Interface
        self.data = data = CSRStatus("data",
            fields=[CSRField("data", 8)], # The next byte of SETUP data
            # Data from the last SETUP transactions. It will be 10 bytes long, because it will include the CRC16. This is a FIFO, and the queue is advanced automatically.
        )

        # Controls for managing how to handle SETUP transactions
        self.ctrl = ctrl = CSRStorage("ctrl",
            fields=[
                CSRField("reset", offset=5, pulse=True), # Write a 1 here to reset the SETUP handler
            ],
        )

       # Status about the most recent SETUP transactions, and the state of the FIFO
        self.status = status = CSRStatus("status",
            fields=[
                CSRField("epno", 4), # The destination endpoint for the most recent SETUP token.
                CSRField("have"),    # 1 if there is data in the FIFO.
                CSRField("pend"),    # 1 if there is an IRQ pending.
                CSRField("is_in"),   # 1 if an IN stage was detected.
                CSRField("data"),    # 1 if a DATA stage is expected.
            ],
        )

        self.submodules.ev = EventManager()
        self.ev.submodules.packet = EventSourcePulse(name="ready")  # Indicates a SETUP packet has arrived and is waiting in the SETUP FIFO
        self.ev.submodules.reset = EventSourceProcess(name="reset") # Indicates a USB RESET condition has occurred, and the ADDRESS is now 0
        self.ev.finalize()
        self.trigger = trigger = self.ev.packet.trigger
        self.pending = pending = self.ev.packet.pending
        self.comb += self.ev.reset.trigger.eq(~self.usb_reset)

        self.data_recv_payload = data_recv_payload = Signal("data_recv_payload", 8)
        self.data_recv_put = data_recv_put = Signal("data_recv_put")

        # Since we must always ACK a SETUP packet, set this to 0.
        self.response = Signal("response")

        class SetupHandlerInner(Module):
            def __init__(self):
                self.submodules.data = buf = _SyncFIFOBuffered(width=8, depth=10)

                # Indicates which byte of SETUP data we're currently on.
                data_byte = Signal("data_byte", 4)

                # If the incoming SETUP token indicates there will be a DATA stage, this will be set to 1.
                self.have_data_stage = have_data_stage = Signal("have_data_stage")

                # If the incoming SETUP token is an OUT packet, this will be 1.
                self.is_in = is_in = Signal("is_in")

                self.empty = Signal("empty")
                self.comb += self.empty.eq(~buf.readable)

                # Wire up the STATUS register
                self.comb += [
                    status.fields.have.eq(buf.readable),
                    status.fields.is_in.eq(is_in),
                    status.fields.epno.eq(epno),
                    status.fields.pend.eq(pending),
                    status.fields.data.eq(have_data_stage),
                ]

                # Wire up the "SETUP" endpoint.
                self.comb += [
                    # Set the FIFO output to be the current buffer HEAD
                    data.fields.data.eq(buf.dout),

                    # Advance the FIFO when a byte is read
                    buf.re.eq(data.we),

                    If(usb_core.tok == PID.SETUP, buf.din.eq(data_recv_payload), buf.we.eq(data_recv_put)),

                    # Tie the trigger to the STATUS.HAVE bit
                    trigger.eq(buf.readable & usb_core.setup),
                ]

                self.sync += [
                    # The 6th and 7th bytes of SETUP data are the wLength field.
                    # If these are nonzero, then there will be a Data stage following this Setup stage.
                    If(data_recv_put,
                        If(data_byte == 0,
                            epno.eq(usb_core.endp),
                            is_in.eq(data_recv_payload[7]),
                        ).Elif(data_byte == 6,
                            If(data_recv_payload,
                                have_data_stage.eq(1),
                            ),
                        ).Elif(data_byte == 7,
                            If(data_recv_payload,
                                have_data_stage.eq(1),
                            ),
                        ),
                        data_byte.eq(data_byte + 1),
                    )
                ]

        self.submodules.inner = inner = ResetInserter()(SetupHandlerInner())
        self.comb += [
            inner.reset.eq(self.reset | self.begin | ctrl.fields.reset),
            self.ev.packet.clear.eq(self.begin),
        ]

        # Expose relevant Inner signals to the top
        self.have_data_stage = inner.have_data_stage
        self.is_in = inner.is_in
        self.empty = inner.empty

# Endpoint for Device->Host transactions
#
# When a host requests data from a device, it sends an IN token. The device should then respond with DATA0, DATA1, or NAK.
# This handler is responsible for managing this response, as well as supplying the USB system with data.
#
# To send data, fill the FIFO by writing bytes to IN_DATA. When you're ready to transmit, write the destination endpoint number to IN_CTRL.

class InHandler(Module, AutoCSR):
    def __init__(self, usb_core):
        self.dtb = Signal("dtb")

        # Keep track of the current DTB for each of the 16 endpoints
        dtbs = Signal("dtbs", 16, reset=0x0001)

        # A list of endpoints that are stalled
        stall_status = Signal("stall_status", 16)

        self.submodules.data_buf = buf = ResetInserter()(_SyncFIFOBuffered(width=8, depth=64))

        self.data = CSRStorage("data",
            fields=[
                CSRField("data", 8), # The next byte to add to the queue
            ],
            # Each byte written into this register gets added to an outgoing FIFO.
            # Any bytes that are written here will be transmitted in the order in which they were added.
            # The FIFO queue is automatically advanced with each write.
            # The FIFO queue is 64 bytes deep.
            # If you exceed this amount, the result is undefined.
        )

        # Enables transmission of data in response to IN tokens, or resets the contents of the FIFO
        self.ctrl = ctrl = CSRStorage("ctrl",
            fields=[
                CSRField("epno", 4),                     # The endpoint number for the transaction that is queued in the FIFO
                CSRField("reset", offset=5, pulse=True), # Write a 1 here to clear the contents of the FIFO
                CSRField("stall", pulse=True),           # Write a 1 here to stall the EP written in EP
            ],
        )

        # Status about the IN handler. As soon as you write to IN_DATA, IN_STATUS.HAVE should go to 1
        self.status = CSRStatus("status",
            fields=[
                CSRField("idle"),           # This value is 1 if the packet has finished transmitting
                CSRField("have", offset=4), # This value is 0 if the FIFO is empty
                CSRField("pend", offset=5), # 1 if there is an IRQ pending
            ],
        )

        self.submodules.ev = EventManager()
        self.ev.submodules.packet = EventSourcePulse(name="done") # Indicates that the host has successfully transferred an IN packet, and that the FIFO is now empty
        self.ev.finalize()

        # Control bits
        ep_stall_mask = Signal("ep_stall_mask", 16)
        self.comb += [
            ep_stall_mask.eq(1 << ctrl.fields.epno),
        ]

        # Keep track of which endpoints are currently stalled
        self.stalled = Signal("stalled")
        self.comb += self.stalled.eq(stall_status >> usb_core.endp)
        self.sync += [
            If(ctrl.fields.reset,
                stall_status.eq(0),
            ).Elif(usb_core.setup | (ctrl.re & ~ctrl.fields.stall),
                # If a SETUP packet comes in, clear the STALL bit.
                stall_status.eq(stall_status & ~ep_stall_mask),
            ).Elif(ctrl.re,
                stall_status.eq(stall_status | ep_stall_mask),
            ),
        ]

        # How to respond to requests:
        #  - 0 - ACK
        #  - 1 - NAK
        self.response = Signal("response")

        # This value goes "1" when data is pending, and returns to "0" when it's done.
        queued = Signal("queued")
        was_queued = Signal("was_queued")

        # This goes to "1" when "queued" is 1 when a "start" occurs. It is used
        # to avoid skipping packets when a packet is queued during a transmission.
        transmitted = Signal("transmitted")

        self.dtb_reset = Signal("dtb_reset")
        self.comb += [
            buf.reset.eq(ctrl.fields.reset | (usb_core.commit & transmitted & queued)),
        ]

        # Outgoing data will be placed on this signal
        self.data_out = Signal("data_out", 8)

        # This is "1" if data_out contains data
        self.data_out_have = Signal("data_out_have")

        # Pulse this to advance the data output
        self.data_out_advance = Signal("data_out_advance")

        # Used to detect when an IN packet finished
        is_our_packet = Signal("is_our_packet")
        is_in_packet = Signal("is_in_packet")

        self.comb += [
            # We will respond with "ACK" if the register matches the current endpoint number
            self.response.eq(queued & is_our_packet & is_in_packet),

            # Wire up the "status" register
            self.status.fields.have.eq(buf.readable),
            self.status.fields.idle.eq(~queued),
            self.status.fields.pend.eq(self.ev.packet.pending),

            # Cause a trigger event when the queued value goes to 0
            self.ev.packet.trigger.eq(~queued & was_queued),

            self.dtb.eq(dtbs >> usb_core.endp),

            self.data_out.eq(buf.dout),
            self.data_out_have.eq(buf.readable),
            buf.re.eq(self.data_out_advance & is_in_packet & is_our_packet),
            buf.we.eq(self.data.re),
            buf.din.eq(self.data.storage),
            is_our_packet.eq(usb_core.endp == ctrl.fields.epno),
            is_in_packet.eq(usb_core.tok == PID.IN),
        ]

        self.sync += [
            If(ctrl.fields.reset,
                queued.eq(0),
                was_queued.eq(0),
                transmitted.eq(0),
                dtbs.eq(0x0001),
            ).Elif(self.dtb_reset,
                dtbs.eq(dtbs | 1),
            )
            # When the user updates the ctrl register, enable writing.
            .Elif(ctrl.re & ~ctrl.fields.stall,
                queued.eq(1),
            )
            .Elif(usb_core.poll & self.response,
                transmitted.eq(1),
            )
            # When the USB core finishes operating on this packet, de-assert the queue flag
            .Elif(usb_core.commit & transmitted & self.response & ~self.stalled,
                queued.eq(0),
                transmitted.eq(0),
                # Toggle the "DTB" line if we transmitted data
                dtbs.eq(dtbs ^ (1 << ctrl.fields.epno)),
            ).Else(
                was_queued.eq(queued),
            ),
        ]

# Endpoint for Host->Device transactions
#
# When a host wants to send data to a device, it sends an OUT token. The device should then respond with ACK, or NAK.
# This handler is responsible for managing this response, as well as reading data from the USB subsystem.
#
# To enable receiving data, write a 1 to the OUT_CTRL.ENABLE bit.
#
# To drain the FIFO, read from OUT.DATA. Don't forget to re-enable the FIFO by ensuring OUT_CTRL.ENABLE is set after advancing the FIFO!

class OutHandler(Module, AutoCSR):
    def __init__(self, usb_core):

        self.submodules.data_buf = buf = ResetInserter()(_SyncFIFOBuffered(width=8, depth=66))

        # Data received from the host will go into a FIFO.
        # This register reflects the contents of the top byte in that FIFO.
        # Reading from this register advances the FIFO pointer.
        self.data = data = CSRStatus("data",
            fields=[
                CSRField("data", 8), # The top byte of the receive FIFO
            ],
        )

        # Controls for receiving packet data. To enable an endpoint, write its value to epno,
        # with the enable bit set to 1 to enable an endpoint, or 0 to disable it.
        # Resetting the OutHandler will set all enable bits to 0.
        # Similarly, you can adjust the STALL state by setting or clearing the stall bit.
        self.ctrl = ctrl = CSRStorage("ctrl",
            fields=[
                CSRField("epno", 4),           # The endpoint number to update the enable and status bits for
                CSRField("enable"),            # Write a 1 here to enable receiving data
                CSRField("reset", pulse=True), # Write a 1 here to reset the OUT handler
                CSRField("stall"),             # Write a 1 here to stall an endpoint
            ],
        )

        # Status about the current state of the OUT endpoint
        self.status = CSRStatus("status",
            fields=[
                CSRField("epno", 4), # The destination endpoint for the most recent OUT packet.
                CSRField("have"),    # 1 if there is data in the FIFO.
                CSRField("pend"),    # 1 if there is an IRQ pending.
            ],
        )

        self.submodules.ev = EventManager()
        # Indicates that an OUT packet has successfully been transferred from the host. This bit must be cleared in order to receive additional packets.
        self.ev.submodules.packet = EventSourcePulse(name="done")
        self.ev.finalize()

        self.usb_reset = Signal("usb_reset")

        self.stalled = Signal("stalled")
        self.enabled = Signal("enabled")
        stall_status = Signal("stall_status", 16)
        enable_status = Signal("enable_status", 16)
        ep_mask = Signal("ep_mask", 16, reset=1)
        self.comb += [
            If(usb_core.setup | usb_core.commit,
                ep_mask.eq(1 << usb_core.endp),
            ).Else(
                ep_mask.eq(1 << ctrl.fields.epno),
            ),
            self.stalled.eq(stall_status >> usb_core.endp),
            self.enabled.eq(enable_status >> usb_core.endp),
        ]
        self.sync += [
            If(ctrl.fields.reset | self.usb_reset,
                stall_status.eq(0),
            ).Elif(usb_core.setup | (ctrl.re & ~ctrl.fields.stall),
                # If a SETUP packet comes in, clear the STALL bit.
                stall_status.eq(stall_status & ~ep_mask),
            ).Elif(ctrl.re,
                stall_status.eq(stall_status | ep_mask),
            ),
        ]

        # The endpoint number of the most recently received packet
        epno = Signal("epno", 4)

        # How to respond to requests:
        #  - 1 - ACK
        #  - 0 - NAK
        # Send a NAK if the buffer contains data, or if "ENABLE" has not been set.
        self.response = Signal("response")
        responding = Signal("responding")
        is_out_packet = Signal("is_out_packet")

        # Keep track of whether we're currently responding.
        self.comb += is_out_packet.eq(usb_core.tok == PID.OUT)
        self.comb += self.response.eq(self.enabled & is_out_packet & ~self.ev.packet.pending)
        self.sync += If(usb_core.poll, responding.eq(self.response))

        # Connect the buffer to the USB system
        self.data_recv_payload = Signal("data_recv_payload", 8)
        self.data_recv_put = Signal("data_recv_put")
        self.comb += [
            buf.din.eq(self.data_recv_payload),
            buf.we.eq(self.data_recv_put & responding),
            buf.reset.eq(ctrl.fields.reset),
            self.data.fields.data.eq(buf.dout),

            # When data is read, advance the FIFO
            buf.re.eq(data.we),

            self.status.fields.epno.eq(epno),
            self.status.fields.have.eq(buf.readable),
            self.status.fields.pend.eq(self.ev.packet.pending),

            # When data is successfully transferred, the buffer becomes full.
            # This is true even if "no" data was transferred, because the buffer will then contain two bytes of CRC16 data.
            # Therefore, if the FIFO is readable, an interrupt must be triggered.
            self.ev.packet.trigger.eq(responding & usb_core.commit),
        ]

        # If we get a packet, turn off the "IDLE" flag and keep it off until the packet has finished.
        self.sync += [
            If(ctrl.fields.reset,
                enable_status.eq(0),
            ).Elif(usb_core.commit & responding,
                epno.eq(usb_core.endp),
                # Disable this EP when a transfer finishes
                enable_status.eq(enable_status & ~ep_mask),
                responding.eq(0),
            ).Elif(ctrl.re,
                # Enable or disable the EP as necessary
                If(ctrl.fields.enable,
                    enable_status.eq(enable_status | ep_mask),
                ).Else(
                    enable_status.eq(enable_status & ~ep_mask),
                ),
            ),
        ]

# Hack the AutoCSR objects to enable access only via Module attributes.
class CSRTransform(ModuleTransformer):
    def __init__(self, parent):
        self.parent = parent

    def transform_instance(self, i):
        # Capture all the available CSRs, then burn the bridge.
        v = i.get_csrs()
        i.get_csrs = None

        for c in v:
            # Attach csr as module attribute
            setattr(i, c.name, c)

            if isinstance(c, CSR):
                ...
            else:
                # Clear the finalise function so these aren't altered further.
                # Maybe not required?
                def _null(*kwargs):
                    ...
                c.finalize = _null

                # Attach these to our modules submodules, needed to ensure the objects are elaborated?
                self.parent.submodules += c

            # create extra bindings to support dev writing
            if isinstance(c, CSRStorage):
                # .re is used to determine when .storage has been updated.
                # so we need to create delayed re signal, we'll rename this to re0
                setattr(c, "re0", c.re)
                setattr(c.re0, "name", c.name + "_re0")

                # Our personal .re signal will then update .re0 alongside .storage
                setattr(c, "re", Signal(c.name + "_re"))
                c.sync += c.re0.eq(c.re)

                if hasattr(c, "fields"):
                    setattr(c, "dat_w", Record("dat_w", []))
                    for a in c.fields.fields:
                        s = Signal(c.name + "_" + a.name + "0", a.size)

                        c.sync += If(c.re, c.storage[a.offset:a.offset + a.size].eq(s))
                        setattr(c.dat_w, a.name, s)
                else:
                    # if the CSRStorage doesn't have any fields, just provide .dat_w
                    setattr(c, "dat_w", Signal("dat_w", c.size))
                    c.sync += If(c.re, c.storage.eq(c.dat_w))

class CDCUsb(Module, AutoCSR):
    def __init__(self, iobuf, vid=0x1209, pid=0x5bf2, product="OrangeCrab CDC", manufacturer="GsD"):

        self.submodules.phy = phy = ClockDomainsRenamer("usb_12")(CDCUsbPHY(iobuf, vid=vid, pid=pid, product=product, manufacturer=manufacturer))

        # create interface for UART
        self._rxtx = CSR("rxtx", 8)
        self._txfull = CSRStatus("txfull")
        self._rxempty = CSRStatus("rxempty")

        self.submodules.ev = EventManager()
        self.ev.tx = EventSourceProcess()
        self.ev.rx = EventSourceProcess()
        self.ev.finalize()

        self._tuning_word = CSRStorage("tuning_word", 32, reset=0)

        self._configured = CSR("configured")

        self.sink   = Endpoint("sink", [("data", 8)])
        self.source = Endpoint("source", [("data", 8)])

        self.rts = Signal("rts")
        self.dtr = Signal("dtr")

        self.async_rst = Signal("async_rst")

        self.specials += MultiReg(phy.rts, self.rts)
        self.specials += MultiReg(phy.dtr, self.dtr)

        self.submodules.configure_pulse = PulseSynchronizer("sys", "usb_12")

        self.comb += [
                #phy.source.connect(self.source),
                #self.sink.connect(phy.sink),

                self.source.connect(phy.source),
                phy.sink.connect(self.sink),

                self.async_rst.eq(phy.dtr),

                self.configure_pulse.i.eq(self._configured.re),
                self.phy.configure_set.eq(self.configure_pulse.o),
            ]

        # TX
        tx_fifo = ClockDomainsRenamer({"write":"sys", "read":"usb_12"})(AsyncFIFO([("data", 8)], 4, buffered=False))
        self.submodules += tx_fifo

        self.comb += [
            tx_fifo.sink.valid.eq(self._rxtx.re),
            tx_fifo.sink.data.eq(self._rxtx.r),
            self._txfull.status.eq(~tx_fifo.sink.ready),
            tx_fifo.source.connect(self.source),
            # Generate TX IRQ when tx_fifo becomes non-full
            self.ev.tx.trigger.eq(~tx_fifo.sink.ready)
        ]

        # RX
        rx_fifo = ClockDomainsRenamer({"write":"usb_12", "read":"sys"})(AsyncFIFO([("data", 8)], 4, buffered=False))
        self.submodules += rx_fifo

        self.comb += [
            self.sink.connect(rx_fifo.sink),
            self._rxempty.status.eq(~rx_fifo.source.valid),
            self._rxtx.w.eq(rx_fifo.source.data),
            rx_fifo.source.ready.eq(self.ev.rx.clear | (False & self._rxtx.we)),
            # Generate RX IRQ when tx_fifo becomes non-empty
            self.ev.rx.trigger.eq(~rx_fifo.source.valid)
        ]

class CDCUsbPHY(Module):
    def __init__(self, iobuf, vid, pid, product, manufacturer):

        # Create the eptri USB interface
        usb = TriEndpointInterface(iobuf)
        #usb.finalize()
        self.submodules.eptri = usb = CSRTransform(self)(usb)

        self.sink   = Endpoint("sink", [("data", 8)])
        self.source = Endpoint("source", [("data", 8)])

        self.rts = Signal("rts")
        self.dtr = Signal("dtr")

        # Ato attach on power up
        self.comb += [
            usb.pullup_out.dat_w.eq(~ResetSignal()),
            usb.pullup_out.re.eq(1),
        ]

        def make_usbstr(s):
            usbstr = bytearray(2)
            # The first byte is the number of characters in the string.
            # Because strings are utf_16_le, each character is two-bytes.
            # That leaves 126 bytes as the maximum length
            usbstr[0] = (len(s) * 2) + 2
            usbstr[1] = 3
            usbstr.extend(bytes(s, 'utf_16_le'))
            return list(usbstr)

        # Start with 0x8006
        descriptors = {
            # Config descriptor
            # 80 06 00 02
            0x0002: [
                0x09, # bLength
                0x02, # bDescriptorType
                62, 0x00, # wTotalLength
                0x02, # bNumInterfaces
                0x01, # bConfigurationValue
                0x00, # iConfiguration
                0x80, # bmAttributes
                0x32, # bMaxPower

                # Interface descriptor
                0x09, # bLength
                0x04, # bDescriptorType
                0x00, # bInterfaceNumber
                0x00, # bAlternateSetting
                0x01, # bNumEndpoints
                0x02, # bInterfaceClass (2: Communications Interface)
                0x02, # bInterfaceSubClass (2: Abstract Control Model)
                0x00, # bInterfacePrototcol
                0x00, # iInterface

                # Header Functional Descriptor
                0x05, # bFunctionLength
                0x24, # bDescriptorType (24: CS_INTERFACE)
                0x00, # bDescriptorSubtype
                0x10, 0x01, # bcdCDC

                # ACM Functional Descriptor
                0x04, # bFunctionLength
                0x24, # bDescriptorType
                0x02, # bDescriptorSubtype
                0x02, # bmCapabilities

                # Union Functional Description
                0x05, # bLength
                0x24, # bDescriptorType
                0x06, # bDescriptorSubtype
                0x00, # bControlInterfoce
                0x01, # bSubordinateInterface0

                # Control Endpoint Descriptior
                0x07, # bLength
                0x05, # bDescriptorType (5: ENDPOINT)
                0x81, # bEndpointAddress
                0x03, # bmAttributes (XFER_INTERRUPT)
                0x08, 0x00, # wMaxPacketSize
                0x40, # bInterval

                0x09, # bLength            = sizeof(tusb_desc_interface_t),
                0x04, # bDescriptorType    = TUSB_DESC_TYPE_INTERFACE,
                0x01, # bInterfaceNumber   = 5,
                0x00, # bAlternateSetting  = 0x00,
                0x02, # bNumEndpoints      = 2,
                0x0A, # bInterfaceClass    = TUSB_CLASS_CDC_DATA,
                0x00, # bInterfaceSubClass = 0,
                0x00, # bInterfaceProtocol = 0,
                0x00, # iInterface         = 0x00

                0x07, # bLength          = sizeof(tusb_desc_endpoint_t),
                0x05, # bDescriptorType  = TUSB_DESC_TYPE_ENDPOINT,
                0x02, # bEndpointAddress = 5,
                0x02, # bmAttributes     = { .xfer = TUSB_XFER_BULK },
                0x40, 0x00, # wMaxPacketSize   = 64,
                0x00, # bInterval        = 0

                0x07, # bLength          = sizeof(tusb_desc_endpoint_t),
                0x05, # bDescriptorType  = TUSB_DESC_TYPE_ENDPOINT,
                0x82, # bEndpointAddress = 0x85,
                0x02, # bmAttributes     = { .xfer = TUSB_XFER_BULK },
                0x40, 0x00, # wMaxPacketSize   = 64,
                0x00, # bInterval        = 0
            ],

            # Device descriptor
            # 80 06 00 01
            0x0001: [
                0x12, # Length
                0x01, # bDescriptorType
                0x00, 0x02, # bcdUSB
                0x02, # bDeviceClass
                0x00, # bDeviceSubClass
                0x00, # bDeviceProtocol
                0x40, # bMaxPacketSize0
                (vid>>0)&0xff, (vid>>8)&0xff, # idVendor
                (pid>>0)&0xff, (pid>>8)&0xff, # idProduct
                0x01, 0x01, # bcdDevice
                0x01, # iManufacture
                0x02, # iProduct
                0x00, # iSerialNumber
                0x01, # bNumConfigurations
            ],

            # String 0
            0x0003: [
                0x04, 0x03, 0x09, 0x04,
            ],

            # String 1 (manufacturer)
            0x0103: make_usbstr(manufacturer),

            # String 2 (Product)
            0x0203: make_usbstr(product),

            # BOS descriptor
            0x000f: [
                0x05, 0x0f, 0x1d, 0x00, 0x01, 0x18, 0x10, 0x05,
                0x00, 0x38, 0xb6, 0x08, 0x34, 0xa9, 0x09, 0xa0,
                0x47, 0x8b, 0xfd, 0xa0, 0x76, 0x88, 0x15, 0xb6,
                0x65, 0x00, 0x01, 0x02, 0x01,
            ],

            0xee03: [
                0x12, 0x03, 0x4d, 0x53, 0x46, 0x54, 0x31, 0x30,
                0x30, 0x7e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00,
            ],
        }

        # Starts with 0xc07e or 0xc17e
        usb_ms_compat_id_descriptor = [
            0x28, 0x00, 0x00, 0x00, 0x00, 0x01, 0x04, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x01, 0x57, 0x49, 0x4e, 0x55, 0x53, 0x42,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]

        class MemoryContents:
            def __init__(self):
                self.contents = [0x00]
                self.offsets = {}
                self.lengths = {}

            def add(self, wRequestAndType, wValue, mem):
                self.offsets[wRequestAndType << 16 | wValue] = len(self.contents)
                self.lengths[wRequestAndType << 16 | wValue] = len(mem)
                self.contents = self.contents + mem

        mem = MemoryContents()
        for key, value in descriptors.items():
            mem.add(0x8006, key, value)

        mem.add(0xc07e, 0x0000, usb_ms_compat_id_descriptor)
        mem.add(0x8000, 0x0000, [0, 0]) # Get device status
        mem.add(0x0009, 0x0100, []) # Set configuration 1

        mem.add(0xA121, 0x0000, [0x00, 0xC2, 0x01, 0x00, 0x00, 0x00, 0x08]) # Get line_coding
        #mem.add(0xA120, 0x0000, [0x00, 0x00]) # SerialState

        out_buffer = self.specials.out_buffer = Memory("out_buffer", 8, len(mem.contents), mem.contents)
        self.specials.out_buffer_rd = out_buffer_rd = out_buffer.get_port(write_capable=False, clock_domain="usb_12")
        self.autocsr_exclude = ['out_buffer']

        # Needs to be able to index Memory
        response_addr = Signal("response_addr", 9)
        response_len = Signal("response_len", 6)
        response_ack = Signal("response_ack")
        bytes_remaining = Signal("bytes_remaining", 6)
        bytes_addr = Signal("bytes_addr", 9)

        new_address = Signal("new_address", 7)

        configured = Signal("configured")
        configured_delay = Signal("configured_delay", 16, reset=2**16 - 1)

        self.configure_set = Signal("configure_set")

        self.sync += [
            If(self.dtr & (configured_delay > 0),
                configured_delay.eq(configured_delay - 1)
            ).Elif(self.configure_set,
                configured_delay.eq(0)
            )
        ]
        self.comb += configured.eq(configured_delay == 0)

        # SETUP packets contain a DATA segment that is always 8 bytes.
        # However, we're only ever interested in the first 4 bytes, plus the last byte.
        usbPacket = Signal("usbPacket", 32)
        wRequestAndType = Signal("wRequestAndType", 16)
        wValue = Signal("wValue", 16)
        wLength = Signal("wLength", 8)
        self.comb += [
            wRequestAndType.eq(usbPacket[16:32]),
            wValue.eq(usbPacket[0:16]),
        ]
        setup_index = Signal("setup_index", 4)

        # Respond to various descriptor requests
        cases = {}
        for key in mem.offsets:
            cases[key] = [
                response_len.eq(mem.lengths[key]),
                response_addr.eq(mem.offsets[key]),
            ]
        self.comb += Case(usbPacket, cases)

        self.submodules.config = config = FSM(reset_state="IDLE")

        toggle = Signal("toggle")

        config.act("IDLE",
            #usb.address.dat_w.eq(new_address),
            usb.address.dat_w.addr.eq(new_address),
            usb.address.re.eq(1),

            usb.out_ctrl.dat_w.epno.eq(2),
            usb.out_ctrl.dat_w.enable.eq(1),
            usb.out_ctrl.re.eq(1),

            NextState("WAIT"),
        )

        config.act("WAIT",
            #usb.in_ctrl.dat_w.epno.eq(0),
            #usb.in_ctrl.re.eq(1),

            usb.out_ctrl.dat_w.epno.eq(0),
            usb.out_ctrl.dat_w.enable.eq(1),
            usb.out_ctrl.re.eq(1),

            If(usb.setup_status.fields.have,
                NextState("SETUP"),
                NextValue(setup_index, 0),
                usb.out_ev_pending.r.eq(1),
                usb.out_ev_pending.re.eq(1),

            ),

            # Data RX?
            If(usb.out_ev_pending.w,
                usb.out_ev_pending.r.eq(1),
                usb.out_ev_pending.re.eq(1),

                If((usb.out_status.fields.epno == 2) & usb.out_status.fields.pend,
                    NextState("DRAIN-RX")
                )
            ),

            # UART_FIFO data?
            If(self.source.valid & configured,
                NextState("FILL-TX"),
            )
        )

        delayed_re = Signal("delayed_re")
        config.act("FILL-TX",
            usb.in_data.dat_w.data.eq(self.source.data),

            usb.in_data.re.eq(delayed_re & self.source.valid),
            NextValue(delayed_re, 0),

            self.source.ready.eq(delayed_re & self.source.valid),

            If(self.source.valid,
                NextValue(delayed_re, self.source.valid),
            ).Else(
                usb.in_ctrl.dat_w.epno.eq(2),
                usb.in_ctrl.re.eq(1),
                NextState("WAIT-TRANSACTION"),
            )
        )

        # OUT data always captures 2 extra bytes from CRC
        # Since we don't know in advance how long the transaction was we need to account for this now
        data_d1 = Signal("data_d1", 8)
        re_d1 = Signal("re_d1")

        data_d2 = Signal("data_d2", 8)
        re_d2 = Signal("re_d2")

        config.act("DRAIN-RX",
            self.sink.data.eq(data_d2),

            usb.out_data.we.eq(delayed_re & usb.out_status.fields.have & self.sink.ready),
            NextValue(delayed_re, 0),

            self.sink.valid.eq(re_d2 & usb.out_status.fields.have & self.sink.ready),

            If(usb.out_status.fields.have,
                NextValue(delayed_re, usb.out_status.fields.have),

                If(self.sink.ready,
                    NextValue(data_d1, usb.out_data.fields.data),
                    NextValue(data_d2, data_d1),

                    NextValue(re_d1, delayed_re),
                    NextValue(re_d2, re_d1),
                )
            ).Else(
                    NextValue(data_d1, 0),
                    NextValue(data_d2, 0),

                    NextValue(re_d1, 0),
                    NextValue(re_d2, 0),
                    NextValue(delayed_re, 0),

                    NextState("IDLE"),
            )
        )

        config.act("SETUP",
           # read out setup packets to determine what to do
           If(usb.setup_status.fields.have,
                NextValue(setup_index, setup_index + 1),
                Case(setup_index, {
                    0: NextValue(usbPacket, Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    1: NextValue(usbPacket, Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    2: NextValue(usbPacket, Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    3: NextValue(usbPacket, Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    # 4: wIndex.eq(data_recv_payload_delayed),
                    # 5: wIndex.eq(Cat(wIndex[0:8], data_recv_payload_delayed)),
                    6: NextValue(wLength, usb.setup_data.fields.data),
                    # 7: wLength.eq(Cat(wLength[0:8], data_recv_payload_delayed)),
                }),
                usb.setup_data.we.eq(1)
            ),

            # Determine which state next
            If(setup_index == 0xA,
                # Ack with a blank IN packet
                usb.in_ctrl.dat_w.epno.eq(0),
                usb.in_ctrl.re.eq(1),

                NextState("WAIT-TRANSACTION"),
                If(wRequestAndType == 0x0005,
                    # Set Address
                    NextValue(new_address, wValue[8:15]),
                    NextState("WAIT-TRANSACTION"),
                ).Elif(wRequestAndType == 0x2122,
                    # Set Address
                    NextValue(self.rts, wValue[9]),
                    NextValue(self.dtr, wValue[8]),
                    NextState("WAIT-TRANSACTION"),
                ).Elif((usb.setup_status.fields.is_in) & (response_len > 0),
                    NextState("SETUP-IN"),
                    If(response_len > wLength,
                        NextValue(bytes_remaining, wLength),
                    ).Else(
                        NextValue(bytes_remaining, response_len),
                    ),
                    NextValue(bytes_addr, response_addr),
                ),
            )
        )

        config.act("SETUP-IN",
            usb.in_data.dat_w.data.eq(out_buffer_rd.dat_r),

            usb.in_data.re.eq(delayed_re),
            NextValue(delayed_re, 0),

            If(bytes_remaining,
                NextValue(delayed_re, 1),
                NextValue(bytes_addr, bytes_addr + 1),
                NextValue(bytes_remaining, bytes_remaining - 1),
            ).Elif(usb.in_ev_pending.w,
                NextState("WAIT-TRANSACTION"),
            )
        ),

        config.act("WAIT-TRANSACTION",
            usb.out_data.we.eq(1),
            If(usb.in_ev_pending.w,
                usb.in_ev_pending.r.eq(1),
                usb.in_ev_pending.re.eq(1),

                NextState("IDLE"),
            )
        )

        config.act("WAIT-OUT",
            If(usb.in_ev_pending.w & usb.out_ev_pending.w,
                usb.in_ev_pending.r.eq(1),
                usb.in_ev_pending.re.eq(1),

                usb.out_ev_pending.r.eq(1),
                usb.out_ev_pending.re.eq(1),

                NextState("IDLE"),
            )
        )

        self.comb += [ out_buffer_rd.adr.eq(bytes_addr), ]

class PicoRV32(Module):
    name                 = "picorv32"
    data_width           = 32
    endianness           = "little"
    linker_output_format = "elf32-littleriscv"
    io_regions           = {0x80000000: 0x80000000} # origin, length
    gcc_flags            = None

    @property
    def gcc_flags(self):
        return "-mno-save-restore -march=rv32i -mabi=ilp32 -D__picorv32__ "

    def __init__(self, platform):
        self.platform     = platform
        self.trap         = Signal("trap")
        self.reset        = Signal("reset")
        self.idbus        = idbus = WishboneInterface()
        self.periph_buses = [idbus]
        self.memory_buses = []

        mem_valid = Signal("mem_valid")
        mem_instr = Signal("mem_instr")
        mem_ready = Signal("mem_ready")
        mem_addr  = Signal("mem_addr", 32)
        mem_wdata = Signal("mem_wdata", 32)
        mem_wstrb = Signal("mem_wstrb", 4)
        mem_rdata = Signal("mem_rdata", 32)

        self.cpu_params = dict(
            i_clk    = ClockSignal(),
            i_resetn = ~(ResetSignal() | self.reset),

            o_trap = self.trap,

            # memory interface
            o_mem_valid = mem_valid,
            o_mem_instr = mem_instr,
            i_mem_ready = mem_ready,

            o_mem_addr  = mem_addr,
            o_mem_wdata = mem_wdata,
            o_mem_wstrb = mem_wstrb,
            i_mem_rdata = mem_rdata,
        )

        # adapt memory interface to wishbone
        self.comb += [
            idbus.adr.eq(mem_addr[2:]),
            idbus.dat_w.eq(mem_wdata),
            idbus.we.eq(mem_wstrb != 0),
            idbus.sel.eq(mem_wstrb),
            idbus.cyc.eq(mem_valid),
            idbus.stb.eq(mem_valid),
            idbus.cti.eq(0),
            idbus.bte.eq(0),
            mem_ready.eq(idbus.ack),
            mem_rdata.eq(idbus.dat_r),
        ]

        # add verilog sources
        self.add_sources(platform)

    @staticmethod
    def add_sources(platform):
        platform.add_source(os.path.abspath(os.path.join(os.path.dirname(__file__), "picorv32.v")))

    def do_finalize(self):
        self.specials += Instance("picorv32", **self.cpu_params)

def SoCConstant(value):
    return value

class SoCRegion:
    def __init__(self, origin=None, size=None, mode="rw", cached=True, linker=False):
        self.origin    = origin
        self.size      = size
        self.size_pow2 = 2**log2_int(size, False)
        self.mode      = mode
        self.cached    = cached
        self.linker    = linker

    def decoder(self, bus):
        origin = self.origin
        size   = self.size_pow2
        if (origin & (size - 1)) != 0:
            raise
        origin >>= int(math.log2(bus.data_width // 8)) # bytes to words aligned
        size   >>= int(math.log2(bus.data_width // 8)) # bytes to words aligned
        return lambda a: (a[log2_int(size):] == (origin >> log2_int(size)))

class SoCIORegion(SoCRegion): pass

class SoCCSRRegion:
    def __init__(self, origin, busword, obj):
        self.origin  = origin
        self.busword = busword
        self.obj     = obj

class SoCBusHandler(Module):
    def __init__(self, standard, data_width=32, address_width=32, timeout=1e6, reserved_regions={}):

        # Create Bus
        self.standard      = standard
        self.data_width    = data_width
        self.address_width = address_width
        self.masters       = {}
        self.slaves        = {}
        self.regions       = {}
        self.io_regions    = {}
        self.timeout       = timeout

        # Adding reserved regions
        for name, region in reserved_regions.items():
            if isinstance(region, int):
                region = SoCRegion(origin=region, size=0x1000000)
            self.add_region(name, region)

    def add_region(self, name, region):
        allocated = False
        if name in self.regions.keys() or name in self.io_regions.keys():
            raise
        # Check if SoCIORegion
        if isinstance(region, SoCIORegion):
            self.io_regions[name] = region
            overlap = self.check_regions_overlap(self.io_regions)
            if overlap is not None:
                raise
        # Check if SoCRegion
        elif isinstance(region, SoCRegion):
            # If no origin specified, allocate region.
            if region.origin is None:
                allocated = True
                region    = self.alloc_region(name, region.size, region.cached)
                self.regions[name] = region
            # Else add region and check for overlaps.
            else:
                if not region.cached:
                    if not self.check_region_is_io(region):
                        raise
                self.regions[name] = region
                overlap = self.check_regions_overlap(self.regions)
                if overlap is not None:
                    raise
        else:
            raise

    def alloc_region(self, name, size, cached=True):

        # Limit Search Regions
        if cached == False:
            search_regions = self.io_regions
        else:
            search_regions = {"main": SoCRegion(origin=0x00000000, size=2**self.address_width - 1)}

        # Iterate on Search_Regions to find a Candidate
        for _, search_region in search_regions.items():
            origin = search_region.origin
            while (origin + size) < (search_region.origin + search_region.size_pow2):
                # Create a Candicate.
                candidate = SoCRegion(origin=origin, size=size, cached=cached)
                overlap   = False
                # Check Candidate does not overlap with allocated existing regions
                for _, allocated in self.regions.items():
                    if self.check_regions_overlap({"0": allocated, "1": candidate}) is not None:
                        origin  = allocated.origin + allocated.size_pow2
                        overlap = True
                        break
                if not overlap:
                    # If no overlap, the Candidate is selected
                    return candidate

        raise

    def check_regions_overlap(self, regions, check_linker=False):
        i = 0
        while i < len(regions):
            n0 =  list(regions.keys())[i]
            r0 = regions[n0]
            for n1 in list(regions.keys())[i + 1:]:
                r1 = regions[n1]
                if r0.linker or r1.linker:
                    if not check_linker:
                        continue
                if r0.origin >= (r1.origin + r1.size_pow2):
                    continue
                if r1.origin >= (r0.origin + r0.size_pow2):
                    continue
                return (n0, n1)
            i += 1
        return None

    def check_region_is_in(self, region, container):
        is_in = True
        if not (region.origin >= container.origin):
            is_in = False
        if not ((region.origin + region.size) < (container.origin + container.size)):
            is_in = False
        return is_in

    def check_region_is_io(self, region):
        is_io = False
        for _, io_region in self.io_regions.items():
            if self.check_region_is_in(region, io_region):
                is_io = True
        return is_io

    def add_adapter(self, name, interface, direction="m2s"):
        if isinstance(interface, WishboneInterface):
            new_interface = WishboneInterface(data_width=self.data_width)
            if direction == "m2s":
                converter = WishboneConverter(master=interface, slave=new_interface)
            if direction == "s2m":
                converter = WishboneConverter(master=new_interface, slave=interface)
            self.submodules += converter
        else:
            raise TypeError(interface)

        return new_interface

    def add_master(self, name=None, master=None):
        if name is None:
            name = "master{:d}".format(len(self.masters))
        if name in self.masters.keys():
            raise
        master = self.add_adapter(name, master, "m2s")
        self.masters[name] = master

    def add_slave(self, name=None, slave=None, region=None):
        no_name   = name is None
        no_region = region is None
        if no_name and no_region:
            raise
        if no_name:
            name = "slave{:d}".format(len(self.slaves))
        if no_region:
            region = self.regions.get(name, None)
            if region is None:
                raise
        else:
             self.add_region(name, region)
        if name in self.slaves.keys():
            raise
        slave = self.add_adapter(name, slave, "s2m")
        self.slaves[name] = slave

class SoCLocHandler(Module):
    def __init__(self, name, n_locs):
        self.name   = name
        self.locs   = {}
        self.n_locs = n_locs

    def add(self, name, n=None, use_loc_if_exists=False):
        allocated = False
        if not (use_loc_if_exists and name in self.locs.keys()):
            if name in self.locs.keys():
                raise
            if n in self.locs.values():
                raise
            if n is None:
                allocated = True
                n = self.alloc(name)
            else:
                if n < 0:
                    raise
                if n > self.n_locs:
                    raise
            self.locs[name] = n
        else:
            n = self.locs[name]

    def alloc(self, name):
        for n in range(self.n_locs):
            if n not in self.locs.values():
                return n
        raise

class SoCCSRHandler(SoCLocHandler):
    def __init__(self, data_width=32, address_width=14, alignment=32, paging=0x800, reserved_csrs={}):
        SoCLocHandler.__init__(self, "CSR", n_locs=alignment // 8 * (2**address_width) // paging)

        # Create CSR Handler
        self.data_width    = data_width
        self.address_width = address_width
        self.alignment     = alignment
        self.paging        = paging
        self.masters       = {}
        self.regions       = {}

        # Adding reserved CSRs
        for name, n in reserved_csrs.items():
            self.add(name, n)

    def add_master(self, name=None, master=None):
        if name is None:
            name = "master{:d}".format(len(self.masters))
        if name in self.masters.keys():
            raise
        if master.data_width != self.data_width:
            raise
        self.masters[name] = master

    def add_region(self, name, region):
        self.regions[name] = region

    def address_map(self, name, memory):
        if memory is not None:
            name = name + "_" + memory.name
        if self.locs.get(name, None) is None:
            raise
        return self.locs[name]

class SoCController(Module, AutoCSR):
    def __init__(self, with_reset = True, with_scratch = True, with_errors = True):

        if with_reset:
            self._reset = CSRStorage("reset", 1) # Write a 1 to this register to reset the SoC
        if with_scratch:
            # Use this register as a scratch space to verify that software read/write accesses to the Wishbone/CSR bus are working correctly.
            # The initial reset value of 0x1234578 can be used to verify endianness.
            self._scratch = CSRStorage("scratch", 32, reset=0x12345678)
        if with_errors:
            self._bus_errors = CSRStatus("bus_errors", 32) # Total number of Wishbone bus errors (timeouts) since start

        # Reset
        if with_reset:
            self.reset = Signal("reset")
            self.comb += self.reset.eq(self._reset.re)

        # Errors
        if with_errors:
            self.bus_error = Signal("bus_error")
            bus_errors     = Signal("bus_errors", 32)
            self.sync += [
                If(bus_errors != (2**len(bus_errors) - 1),
                    If(self.bus_error, bus_errors.eq(bus_errors + 1))
                )
            ]
            self.comb += self._bus_errors.status.eq(bus_errors)

class ConstraintError(Exception):
    pass

class Pins:
    def __init__(self, *identifiers):
        self.identifiers = []
        for i in identifiers:
            if isinstance(i, int):
                self.identifiers += ["X"]*i
            else:
                self.identifiers += i.split()

class IOStandard:
    def __init__(self, name):
        self.name = name

class Misc:
    def __init__(self, misc):
        self.misc = misc

class Subsignal:
    def __init__(self, name, *constraints):
        self.name = name
        self.constraints = list(constraints)

def _format_constraint(c):
    if isinstance(c, Pins):
        return ("LOCATE COMP ", " SITE " + "\"" + c.identifiers[0] + "\"")
    elif isinstance(c, IOStandard):
        return ("IOBUF PORT ", " IO_TYPE=" + c.name)
    elif isinstance(c, Misc):
        return ("IOBUF PORT ", " " + c.misc)

def _format_lpf(signame, pin, others, resname):
    fmt_c = [_format_constraint(c) for c in ([Pins(pin)] + others)]
    lpf = []
    for pre, suf in fmt_c:
        lpf.append(pre + "\"" + signame + "\"" + suf + ";")
    return "\n".join(lpf)

def _build_lpf(named_sc, named_pc, build_name):
    lpf = []
    lpf.append("BLOCK RESETPATHS;")
    lpf.append("BLOCK ASYNCPATHS;")
    for sig, pins, others, resname in named_sc:
        if len(pins) > 1:
            for i, p in enumerate(pins):
                lpf.append(_format_lpf(sig + "[" + str(i) + "]", p, others, resname))
        else:
            lpf.append(_format_lpf(sig, pins[0], others, resname))
    if named_pc:
        lpf.append("\n\n".join(named_pc))
    write_file(build_name + ".lpf", "\n".join(lpf))

_yosys_template = [
    "verilog_defaults -push",
    "verilog_defaults -add -defer",
    "{read_files}",
    "verilog_defaults -pop",
    "attrmap -tocase keep -imap keep=\"true\" keep=1 -imap keep=\"false\" keep=0 -remove keep=0",
    "synth_ecp5 -abc9 -json {build_name}.json -top {build_name}",
]

def _yosys_import_sources(platform):
    reads = []
    for filename in platform.sources:
        reads.append("read_verilog {}".format(filename))
    return "\n".join(reads)

def _build_yosys(template, platform, build_name):
    ys = []
    for l in template:
        ys.append(l.format(build_name = build_name, read_files = _yosys_import_sources(platform)))
    write_file(build_name + ".ys", "\n".join(ys))

def nextpnr_ecp5_parse_device(device):
    device      = device.lower()
    family      = device.split("-")[0]
    size        = device.split("-")[1]
    speed_grade = device.split("-")[2][0]
    if speed_grade not in ["6", "7", "8"]:
       raise ValueError("Invalid speed grade {}".format(speed_grade))
    package     = device.split("-")[2][1:]
    if "256" in package:
        package = "CABGA256"
    elif "285" in package:
        package = "CSFBGA285"
    elif "381" in package:
        package = "CABGA381"
    elif "554" in package:
        package = "CABGA554"
    elif "756" in package:
        package = "CABGA756"
    else:
       raise ValueError("Invalid package {}".format(package))
    return (family, size, speed_grade, package)

nextpnr_ecp5_architectures = {
    "lfe5u-12f"    : "12k",
    "lfe5u-25f"    : "25k",
    "lfe5u-45f"    : "45k",
    "lfe5u-85f"    : "85k",
    "lfe5um-25f"   : "um-25k",
    "lfe5um-45f"   : "um-45k",
    "lfe5um-85f"   : "um-85k",
    "lfe5um5g-25f" : "um5g-25k",
    "lfe5um5g-45f" : "um5g-45k",
    "lfe5um5g-85f" : "um5g-85k",
}

_build_template = [
    "yosys {build_name}.ys",
    "nextpnr-ecp5 --json {build_name}.json --lpf {build_name}.lpf --textcfg {build_name}.config  \
    --{architecture} --package {package} --speed {speed_grade} --timing-allow-fail",
    "ecppack {build_name}.config --bit {build_name}.bit --bootaddr {bootaddr}"
]

def _build_script(source, build_template, build_name, architecture, package, speed_grade, bootaddr):
    s = "set -e\n"

    for line in build_template:
        s += (line + "\n").format(
            build_name   = build_name,
            architecture = architecture,
            package      = package,
            speed_grade  = speed_grade,
            bootaddr     = bootaddr)

    script_file = "build.sh"
    write_file(script_file, s)

    return script_file

class LatticeECP5AsyncResetSynchronizerImpl(Module):
    def __init__(self, cd, async_reset):
        rst1 = Signal("rst1")
        self.specials += [
            Instance("FD1S3BX",
                i_D  = 0,
                i_PD = async_reset,
                i_CK = cd.clk,
                o_Q  = rst1),
            Instance("FD1S3BX",
                i_D  = rst1,
                i_PD = async_reset,
                i_CK = cd.clk,
                o_Q  = cd.rst)
        ]

class LatticeECP5AsyncResetSynchronizer:
    @staticmethod
    def lower(dr):
        return LatticeECP5AsyncResetSynchronizerImpl(dr.cd, dr.async_reset)

class LatticeECP5TrellisTristateImpl(Module):
    def __init__(self, io, o, oe, i):
        nbits, _ = value_bits_sign(io)
        for bit in range(nbits):
            self.specials += Instance("TRELLIS_IO",
                p_DIR = "BIDIR",
                i_B   = io[bit] if nbits > 1 else io,
                i_I   = o[bit]  if nbits > 1 else o,
                o_O   = i[bit]  if nbits > 1 else i,
                i_T   = ~oe
            )

class LatticeECP5TrellisTristate(Module):
    @staticmethod
    def lower(dr):
        return LatticeECP5TrellisTristateImpl(dr.target, dr.o, dr.oe, dr.i)

lattice_ecp5_trellis_special_overrides = {
    AsyncResetSynchronizer: LatticeECP5AsyncResetSynchronizer,
    Tristate:               LatticeECP5TrellisTristate,
}

class LatticeTrellisToolchain:
    attr_translate = {
        "keep": ("keep", "true"),
        "no_retiming":      None,
        "async_reg":        None,
        "mr_ff":            None,
        "mr_false_path":    None,
        "ars_ff1":          None,
        "ars_ff2":          None,
        "ars_false_path":   None,
        "no_shreg_extract": None
    }

    special_overrides = lattice_ecp5_trellis_special_overrides

    def __init__(self):
        self.yosys_template = _yosys_template
        self.build_template = _build_template

    def build(self, platform, fragment, build_dir, build_name, run, bootaddr=0):

        os.makedirs(build_dir, exist_ok=True)
        cwd = os.getcwd()
        os.chdir(build_dir)

        if not isinstance(fragment, _Fragment):
            fragment = fragment.get_fragment()
        platform.finalize(fragment)

        v_output = platform.get_verilog(fragment, build_name)
        named_sc, named_pc = platform.resolve_signals(v_output.ns)
        top_file = build_name + ".v"
        v_output.write(top_file)
        platform.add_source(top_file)

        _build_lpf(named_sc, named_pc, build_name)

        _build_yosys(self.yosys_template, platform, build_name)

        (family, size, speed_grade, package) = nextpnr_ecp5_parse_device(platform.device)
        architecture = nextpnr_ecp5_architectures[(family + "-" + size)]

        script = _build_script(False, self.build_template, build_name, architecture, package, speed_grade, bootaddr)
        if run:
            if subprocess.call(["bash"] + [script]) != 0:
                raise OSError("Subprocess failed")

        os.chdir(cwd)

        return v_output.ns

    def add_period_constraint(self, platform, clk, period):
        platform.add_platform_command("""FREQUENCY PORT "{clk}" {freq} MHz;""".format(freq=str(float(1 / period) * 1000), clk="{clk}"), clk=clk)

def _resource_type(resource):
    t = None
    i = None
    for element in resource[2:]:
        if isinstance(element, Pins):
            t = len(element.identifiers)
        elif isinstance(element, Subsignal):
            if t is None:
                t = []
            if i is None:
                i = []

            n_bits = None
            inverted = False
            for c in element.constraints:
                if isinstance(c, Pins):
                    n_bits = len(c.identifiers)

            t.append((element.name, n_bits))
            i.append((element.name, inverted))

    return t, i

class ConnectorManager:
    def __init__(self, connectors):
        self.connector_table = dict()
        for connector in connectors:
            cit = iter(connector)
            conn_name = next(cit)
            if isinstance(connector[1], str):
                pin_list = []
                for pins in cit:
                    pin_list += pins.split()
                pin_list = [None if pin == "None" else pin for pin in pin_list]
            elif isinstance(connector[1], dict):
                pin_list = connector[1]
            else:
                raise ValueError("Unsupported pin list type {} for connector {}".format(type(connector[1]), conn_name))
            if conn_name in self.connector_table:
                raise ValueError("Connector specified more than once: {}".format(conn_name))

            self.connector_table[conn_name] = pin_list

    def resolve_identifiers(self, identifiers):
        r = []
        for identifier in identifiers:
            if ":" in identifier:
                conn, pn = identifier.split(":")
                if pn.isdigit():
                    pn = int(pn)

                r.append(self.connector_table[conn][pn])
            else:
                r.append(identifier)

        return r

def _separate_pins(constraints):
    pins = None
    others = []
    for c in constraints:
        if isinstance(c, Pins):
            pins = c.identifiers
        else:
            others.append(c)

    return pins, others

def _lookup(description, name):
    for resource in description:
        if resource[0] == name:
            return resource
    raise ConstraintError("Resource not found: {}".format(name))

class ConstraintManager:
    def __init__(self, io, connectors):
        self.available = list(io)
        self.matched = []
        self.platform_commands = []
        self.connector_manager = ConnectorManager(connectors)

    def request(self, name):
        resource = _lookup(self.available, name)
        rt, ri = _resource_type(resource)
        if isinstance(rt, int):
            obj = Signal(name, rt)
        else:
            obj = Record(name, rt)
            for name, inverted in ri:
                if inverted:
                    getattr(obj, name).inverted = True

        self.available.remove(resource)
        self.matched.append((resource, obj))
        return obj

    def lookup_request(self, name):
        for resource, obj in self.matched:
            if resource[0] == name:
                return obj

        return None

    def add_platform_command(self, command, **signals):
        self.platform_commands.append((command, signals))

    def get_io_signals(self):
        r = set()
        for resource, obj in self.matched:
            if isinstance(obj, Signal):
                r.add(obj)
            else:
                r.update(obj.flatten())

        return r

    def get_sig_constraints(self):
        r = []
        for resource, obj in self.matched:
            name = resource[0]
            number = resource[1]
            has_subsignals = False
            top_constraints = []
            for element in resource[2:]:
                if isinstance(element, Subsignal):
                    has_subsignals = True
                else:
                    top_constraints.append(element)

            if has_subsignals:
                for element in resource[2:]:
                    if isinstance(element, Subsignal):
                        sig = getattr(obj, element.name)
                        pins, others = _separate_pins(top_constraints + element.constraints)
                        pins = self.connector_manager.resolve_identifiers(pins)
                        r.append((sig, pins, others, (name, number, element.name)))
            else:
                pins, others = _separate_pins(top_constraints)
                pins = self.connector_manager.resolve_identifiers(pins)
                r.append((obj, pins, others, (name, number, None)))

        return r

    def get_platform_commands(self):
        return self.platform_commands

_io_r0_2 = [
    ("clk48", 0, Pins("A9"),  IOStandard("LVCMOS33")),
    ("rst_n", 0, Pins("V17"), IOStandard("LVCMOS33")),

    ("usr_btn", 0, Pins("J17"), IOStandard("SSTL135_I")),

    ("usb", 0,
        Subsignal("d_p",    Pins("N1")),
        Subsignal("d_n",    Pins("M2")),
        Subsignal("pullup", Pins("N2")),
        IOStandard("LVCMOS33")
    ),
]

class ECP5PLL(Module):
    nclkouts_max    = 3
    clki_div_range  = (1, 128+1)
    clkfb_div_range = (1, 128+1)
    clko_div_range  = (1, 128+1)
    clki_freq_range = (    8e6,  400e6)
    clko_freq_range = (3.125e6,  400e6)
    vco_freq_range  = (  400e6,  800e6)

    def __init__(self):
        self.reset      = Signal("reset")
        self.locked     = Signal("locked")
        self.clkin_freq = None
        self.vcxo_freq  = None
        self.nclkouts   = 0
        self.clkouts    = {}
        self.config     = {}
        self.params     = {}

    def register_clkin(self, clkin, freq):
        (clki_freq_min, clki_freq_max) = self.clki_freq_range
        self.clkin = Signal("clkin")
        if isinstance(clkin, (Signal, ClockSignal)):
            self.comb += self.clkin.eq(clkin)
        else:
            raise ValueError
        self.clkin_freq = freq

    def create_clkout(self, cd, freq, phase=0, margin=1e-2):
        (clko_freq_min, clko_freq_max) = self.clko_freq_range
        clkout = Signal("clkout")
        self.clkouts[self.nclkouts] = (clkout, freq, phase, margin)
        self.comb += cd.clk.eq(clkout)
        self.nclkouts += 1

    def compute_config(self):
        config = {}
        for clki_div in range(*self.clki_div_range):
            config["clki_div"] = clki_div
            for clkfb_div in range(*self.clkfb_div_range):
                all_valid = True
                vco_freq = self.clkin_freq / clki_div * clkfb_div * 1 # clkos3_div=1
                (vco_freq_min, vco_freq_max) = self.vco_freq_range
                if vco_freq >= vco_freq_min and vco_freq <= vco_freq_max:
                    for n, (clk, f, p, m) in sorted(self.clkouts.items()):
                        valid = False
                        for d in range(*self.clko_div_range):
                            clk_freq = vco_freq/d
                            if abs(clk_freq - f) <= f * m:
                                config["clko{}_freq".format(n)]  = clk_freq
                                config["clko{}_div".format(n)]   = d
                                config["clko{}_phase".format(n)] = p
                                valid = True
                                break
                        if not valid:
                            all_valid = False
                else:
                    all_valid = False
                if all_valid:
                    config["vco"] = vco_freq
                    config["clkfb_div"] = clkfb_div
                    return config
        raise ValueError("No PLL config found")

    def do_finalize(self):
        config = self.compute_config()
        clkfb  = Signal("clkfb")
        self.params.update(
            attr=[
                ("FREQUENCY_PIN_CLKI",     str(self.clkin_freq/1e6)),
                ("ICP_CURRENT",            "6"),
                ("LPF_RESISTOR",          "16"),
                ("MFG_ENABLE_FILTEROPAMP", "1"),
                ("MFG_GMCREF_SEL",         "2")],
            i_RST           = self.reset,
            i_CLKI          = self.clkin,
            o_LOCK          = self.locked,
            p_FEEDBK_PATH   = "INT_OS3", # CLKOS3 reserved for feedback with div=1.
            p_CLKOS3_ENABLE = "ENABLED",
            p_CLKOS3_DIV    = 1,
            p_CLKFB_DIV     = config["clkfb_div"],
            p_CLKI_DIV      = config["clki_div"],
        )
        for n, (clk, f, p, m) in sorted(self.clkouts.items()):
            n_to_l = {0: "P", 1: "S", 2: "S2"}
            div    = config["clko{}_div".format(n)]
            cphase = int(p*(div + 1)/360 + div)
            self.params["p_CLKO{}_ENABLE".format(n_to_l[n])] = "ENABLED"
            self.params["p_CLKO{}_DIV".format(n_to_l[n])]    = div
            self.params["p_CLKO{}_FPHASE".format(n_to_l[n])] = 0
            self.params["p_CLKO{}_CPHASE".format(n_to_l[n])] = cphase
            self.params["o_CLKO{}".format(n_to_l[n])]        = clk
        self.specials += Instance("EHXPLLL", **self.params)

class CRG(Module):
    def __init__(self, platform, sys_clk_freq):
        self.clock_domains.cd_init     = ClockDomain("cd_init")
        self.clock_domains.cd_por      = ClockDomain("cd_por", reset_less=True)
        self.clock_domains.cd_sys      = ClockDomain("cd_sys")
        self.clock_domains.cd_sys2x    = ClockDomain("cd_sys2x")
        self.clock_domains.cd_sys2x_i  = ClockDomain("cd_sys2x_i", reset_less=True)

        self.stop  = Signal("stop")
        self.reset = Signal("reset")

        clk48 = platform.request("clk48")
        rst_n = platform.request("usr_btn")

        por_count = Signal("por_count", 16, reset=2**16 - 1)
        por_done  = Signal("por_done")
        self.comb += self.cd_por.clk.eq(clk48)
        self.comb += por_done.eq(por_count == 0)
        self.sync.por += If(~por_done, por_count.eq(por_count - 1))

        sys2x_clk_ecsout = Signal("sys2x_clk_ecsout")

        self.submodules.pll = pll = ECP5PLL()
        pll.register_clkin(clk48, 48e6)
        pll.create_clkout(self.cd_sys2x_i, 2 * sys_clk_freq)
        pll.create_clkout(self.cd_init, 24e6)

        self.specials += [
            Instance("ECLKBRIDGECS",
                i_CLK0   = self.cd_sys2x_i.clk,
                i_SEL    = 0,
                o_ECSOUT = sys2x_clk_ecsout),
            Instance("ECLKSYNCB",
                i_ECLKI = sys2x_clk_ecsout,
                i_STOP  = self.stop,
                o_ECLKO = self.cd_sys2x.clk),
            Instance("CLKDIVF",
                p_DIV     = "2.0",
                i_ALIGNWD = 0,
                i_CLKI    = self.cd_sys2x.clk,
                i_RST     = self.reset,
                o_CDIVX   = self.cd_sys.clk),
            AsyncResetSynchronizer(self.cd_init,  ~por_done | ~pll.locked | ~rst_n),
            AsyncResetSynchronizer(self.cd_sys,   ~por_done | ~pll.locked | ~rst_n | self.reset),
            AsyncResetSynchronizer(self.cd_sys2x, ~por_done | ~pll.locked | ~rst_n | self.reset),
        ]

        self.clock_domains.cd_usb_48 = ClockDomain("cd_usb_48")
        self.clock_domains.cd_usb_12 = ClockDomain("cd_usb_12")

        self.submodules.usb_pll = usb_pll = ECP5PLL()
        usb_pll.register_clkin(clk48, 48e6)
        usb_pll.create_clkout(self.cd_usb_48, 48e6)
        usb_pll.create_clkout(self.cd_usb_12, 12e6)

class OrangeCrab:
    revision = "0.2"

    def __init__(self):
        self.device = "LFE5U-25F-8MG285C"
        self.constraint_manager = ConstraintManager(_io_r0_2, [])
        self.sources = []
        self.output_dir = None
        self.finalized = False
        self.toolchain = LatticeTrellisToolchain()

    def request(self, name):
        return self.constraint_manager.request(name)

    def lookup_request(self, name):
        return self.constraint_manager.lookup_request(name)

    def add_period_constraint(self, clk, period):
        if clk is not None:
            if hasattr(clk, "p"):
                clk = clk.p
            self.toolchain.add_period_constraint(self, clk, period)

    def add_platform_command(self, *args, **kwargs):
        return self.constraint_manager.add_platform_command(*args, **kwargs)

    def finalize(self, fragment):
        if self.finalized:
            raise ConstraintError("Already finalized")

        self.add_period_constraint(self.lookup_request("clk48"), 1e9 / 48e6)

        self.finalized = True

    def add_source(self, filename):
        for f in self.sources:
            if f == filename:
                return
        self.sources.append(os.path.abspath(filename))

    def resolve_signals(self, vns):
        # resolve signal names in constraints
        sc = self.constraint_manager.get_sig_constraints()
        named_sc = [(vns.get_name(sig), pins, others, resource) for sig, pins, others, resource in sc]
        # resolve signal names in platform commands
        pc = self.constraint_manager.get_platform_commands()
        named_pc = []
        for template, args in pc:
            name_dict = dict((k, vns.get_name(sig)) for k, sig in args.items())
            named_pc.append(template.format(**name_dict))

        return named_sc, named_pc

    def get_verilog(self, fragment, name):
        return to_verilog(fragment, name, self.constraint_manager.get_io_signals(), self.toolchain.special_overrides, self.toolchain.attr_translate)

    def build(self, fragment, build_dir, build_name, run):
        return self.toolchain.build(self, fragment, build_dir, build_name, run)

class Waltraud(Module):

    def __init__(self,
        sys_clk_freq         = 64e6,
        # Bus parameters
        bus_standard         = "wishbone",
        bus_data_width       = 32,
        bus_address_width    = 32,
        bus_timeout          = 1e6,
        bus_reserved_regions = {},
        # CSR parameters
        csr_data_width       = 8,
        csr_address_width    = 14,
        csr_paging           = 0x800,
        csr_reserved_csrs    = {
            "ctrl":   0,
            "uart":   2,
        }):

        self.platform     = OrangeCrab()
        self.sys_clk_freq = sys_clk_freq

        self.submodules.bus = SoCBusHandler(
            standard         = bus_standard,
            data_width       = bus_data_width,
            address_width    = bus_address_width,
            timeout          = bus_timeout,
            reserved_regions = bus_reserved_regions,
        )

        self.submodules.csr = SoCCSRHandler(
            data_width    = csr_data_width,
            address_width = csr_address_width,
            alignment     = 32,
            paging        = csr_paging,
            reserved_csrs = csr_reserved_csrs,
        )

        self.constants = {}
        self.add_config("CLOCK_FREQUENCY", int(self.sys_clk_freq))

        # Add SoCController
        self.submodules.ctrl = SoCController()
        self.csr.add("ctrl", use_loc_if_exists=True)

        # Add CPU
        self.submodules.cpu = PicoRV32(self.platform)
        for n, (origin, size) in enumerate(self.cpu.io_regions.items()):
            self.bus.add_region("io{}".format(n), SoCIORegion(origin=origin, size=size, cached=False))
        for n, cpu_bus in enumerate(self.cpu.periph_buses):
            self.bus.add_master(name="cpu_bus{}".format(n), master=cpu_bus)
        self.csr.add("cpu", use_loc_if_exists=True)
        if hasattr(self.ctrl, "reset"):
            self.comb += self.cpu.reset.eq(self.ctrl.reset)

        # Add SRAM
        self.add_ram("sram", 0x00000000, 0x1c000)

        # Add UART
        usb_pads = self.platform.request("usb")
        usb_iobuf = IoBuf(usb_pads.d_p, usb_pads.d_n, usb_pads.pullup)
        self.submodules.uart = CDCUsb(usb_iobuf)
        self.csr.add("uart_phy", use_loc_if_exists=True)
        self.csr.add("uart", use_loc_if_exists=True)

        # Add CSR bridge
        self.add_csr_bridge()

        # Add CRG
        self.submodules.crg = CRG(self.platform, self.sys_clk_freq)

    def add_constant(self, name, value=None):
        name = name.upper()
        if name in self.constants.keys():
            raise
        self.constants[name] = SoCConstant(value)

    def add_config(self, name, value=None):
        name = "CONFIG_" + name
        if isinstance(value, str):
            self.add_constant(name + "_" + value)
        else:
            self.add_constant(name, value)

    def add_ram(self, name, origin, size, contents=[], mode="rw"):
        ram_bus = WishboneInterface(data_width=self.bus.data_width)
        ram     = WishboneSRAM(size, bus=ram_bus, init=contents, read_only=(mode == "r"))
        self.bus.add_slave(name, ram.bus, SoCRegion(origin=origin, size=size, mode=mode))
        setattr(self.submodules, name, ram)

    def set_firmware(self, data):
        self.sram.mem.init = data

    def add_csr_bridge(self, origin=0xf0000000):
        self.submodules.csr_bridge = Wishbone2CSR(
            bus_csr       = CSRBusInterface(
            address_width = self.csr.address_width,
            data_width    = self.csr.data_width),
        )
        csr_size   = 2**(self.csr.address_width + 2)
        csr_region = SoCRegion(origin=origin, size=csr_size, cached=False)
        self.bus.add_slave("csr", self.csr_bridge.wishbone, csr_region)
        self.csr.add_master(name="bridge", master=self.csr_bridge.csr)
        self.add_config("CSR_DATA_WIDTH", self.csr.data_width)
        self.add_config("CSR_ALIGNMENT",  self.csr.alignment)

    def do_finalize(self):
        if len(self.bus.masters) and len(self.bus.slaves):
            # If 1 bus_master, 1 bus_slave and no address translation, use InterconnectPointToPoint.
            if ((len(self.bus.masters) == 1) and (len(self.bus.slaves) == 1) and (next(iter(self.bus.regions.values())).origin == 0)):
                self.submodules.bus_interconnect = WishboneInterconnect(
                    master = next(iter(self.bus.masters.values())),
                    slave  = next(iter(self.bus.slaves.values())),
                )
            # Otherwise, use InterconnectShared.
            else:
                self.submodules.bus_interconnect = WishboneInterconnectShared(
                    masters        = self.bus.masters.values(),
                    slaves         = [(self.bus.regions[n].decoder(self.bus), s) for n, s in self.bus.slaves.items()],
                    register       = True,
                    timeout_cycles = self.bus.timeout,
                )
                if hasattr(self, "ctrl") and self.bus.timeout is not None:
                    if hasattr(self.ctrl, "bus_error"):
                        self.comb += self.ctrl.bus_error.eq(self.bus_interconnect.timeout.error)

        self.submodules.csr_bankarray = CSRBankArray(self,
            address_map        = self.csr.address_map,
            data_width         = self.csr.data_width,
            address_width      = self.csr.address_width,
            alignment          = self.csr.alignment,
            paging             = self.csr.paging,
            soc_bus_data_width = self.bus.data_width)
        if len(self.csr.masters):
            self.submodules.csr_interconnect = CSRBusInterconnectShared(
                masters = list(self.csr.masters.values()),
                slaves  = self.csr_bankarray.get_buses(),
            )

        # Add CSRs regions
        for name, csrs, mapaddr, rmap in self.csr_bankarray.banks:
            self.csr.add_region(name, SoCCSRRegion(
                origin  = (self.bus.regions["csr"].origin + self.csr.paging * mapaddr),
                busword = self.csr.data_width,
                obj     = csrs,
            ))

        # Add Memory regions
        for name, memory, mapaddr, mmap in self.csr_bankarray.srams:
            self.csr.add_region(name + "_" + memory.name, SoCCSRRegion(
                origin  = (self.bus.regions["csr"].origin + self.csr.paging * mapaddr),
                busword = self.csr.data_width,
                obj     = memory,
            ))

        # Sort CSR regions by origin
        self.csr.regions = {k: v for k, v in sorted(self.csr.regions.items(), key=lambda item: item[1].origin)}

        # Retro-compatibility
        for region in self.bus.regions.values():
            region.length = region.size
            region.type   = "cached" if region.cached else "io"
            if region.linker:
                region.type += "+linker"

    def build(self, build_dir, build_name, run):
        return self.platform.build(self, build_dir, build_name or self.platform.name, run)

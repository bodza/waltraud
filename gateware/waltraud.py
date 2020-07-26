import builtins, logging, math, operator, os, subprocess
from collections import defaultdict, Iterable, OrderedDict
from copy import copy
from enum import IntEnum
from functools import reduce
from itertools import combinations
from operator import itemgetter, or_
import re as _re

logging.basicConfig(level=logging.INFO)

def colorer(s, color="bright"):
    header  = {
        "bright": "\x1b[1m",
        "green":  "\x1b[32m",
        "cyan":   "\x1b[36m",
        "red":    "\x1b[31m",
        "yellow": "\x1b[33m",
        "underline": "\x1b[4m"}[color]
    trailer = "\x1b[0m"
    return header + str(s) + trailer

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

def xdir(obj, return_values=False):
    for attr in dir(obj):
        if attr[:2] != "__" and attr[-2:] != "__":
            if return_values:
                yield attr, getattr(obj, attr)
            else:
                yield attr

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

def value_bits_sign(v):
    """Bit length and signedness of a value.

    Parameters
    ----------
    v : Value

    Returns
    -------
    int, bool
        Number of bits required to store `v` or available in `v`, followed by
        whether `v` has a sign bit (included in the bit count).

    Examples
    --------
    >>> value_bits_sign(Signal(8))
    8, False
    >>> value_bits_sign(C(0xaa))
    8, False
    """
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
        return (value_bits_sign(v.v)[0])*v.n, False
    elif isinstance(v, _ArrayProxy):
        bsc = list(map(value_bits_sign, v.choices))
        return max(bs[0] for bs in bsc), any(bs[1] for bs in bsc)
    else:
        raise TypeError("Can not calculate bit length of {} {}".format(type(v), v))

class DUID:
    """Deterministic Unique IDentifier"""
    __next_uid = 0
    def __init__(self):
        self.duid = DUID.__next_uid
        DUID.__next_uid += 1

class _Value(DUID):
    """Base class for operands

    Instances of `_Value` or its subclasses can be operands to
    arithmetic, comparison, bitwise, and logic operators.
    They can be assigned (:meth:`eq`) or indexed/sliced (using the usual
    Python indexing and slicing notation).

    Values created from integers have the minimum bit width to necessary to
    represent the integer.
    """
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

    def __invert__(self):
        return _Operator("~", [self])
    def __neg__(self):
        return _Operator("-", [self])

    def __add__(self, other):
        return _Operator("+", [self, other])
    def __radd__(self, other):
        return _Operator("+", [other, self])
    def __sub__(self, other):
        return _Operator("-", [self, other])
    def __rsub__(self, other):
        return _Operator("-", [other, self])
    def __mul__(self, other):
        return _Operator("*", [self, other])
    def __rmul__(self, other):
        return _Operator("*", [other, self])
    def __lshift__(self, other):
        return _Operator("<<<", [self, other])
    def __rlshift__(self, other):
        return _Operator("<<<", [other, self])
    def __rshift__(self, other):
        return _Operator(">>>", [self, other])
    def __rrshift__(self, other):
        return _Operator(">>>", [other, self])
    def __and__(self, other):
        return _Operator("&", [self, other])
    def __rand__(self, other):
        return _Operator("&", [other, self])
    def __xor__(self, other):
        return _Operator("^", [self, other])
    def __rxor__(self, other):
        return _Operator("^", [other, self])
    def __or__(self, other):
        return _Operator("|", [self, other])
    def __ror__(self, other):
        return _Operator("|", [other, self])

    def __lt__(self, other):
        return _Operator("<", [self, other])
    def __le__(self, other):
        return _Operator("<=", [self, other])
    def __eq__(self, other):
        return _Operator("==", [self, other])
    def __ne__(self, other):
        return _Operator("!=", [self, other])
    def __gt__(self, other):
        return _Operator(">", [self, other])
    def __ge__(self, other):
        return _Operator(">=", [self, other])

    def __len__(self):
        return value_bits_sign(self)[0]

    def __getitem__(self, key):
        n = len(self)
        if isinstance(key, int):
            if key >= n:
                raise IndexError
            if key < 0:
                key += n
            return _Slice(self, key, key+1)
        elif isinstance(key, slice):
            start, stop, step = key.indices(n)
            if step != 1:
                return Cat(self[i] for i in range(start, stop, step))
            return _Slice(self, start, stop)
        else:
            raise TypeError("Cannot use type {} ({}) as key".format(type(key), repr(key)))

    def eq(self, r):
        """Assignment

        Parameters
        ----------
        r : _Value, in
            Value to be assigned.

        Returns
        -------
        _Assign
            Assignment statement that can be used in combinatorial or
            synchronous context.
        """
        return _Assign(self, r)

    def part(self, offset, width):
        """Indexed part-select
        Selects a constant width but variable offset part of a ``_Value``

        Parameters
        ----------
        offset : _Value, in
            start point of the selected bits
        width : Constant, in
            number of selected bits

        Returns
        -------
        _Part
            Selected part of the ``_Value``
        """
        offset = wrap(offset)
        return _Part(self, offset, width)

    def __hash__(self):
        raise TypeError("unhashable type: '{}'".format(type(self).__name__))

def wrap(value):
    """Ensures that the passed object is a Eigen value. Booleans and integers are automatically wrapped into ``Constant``."""
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

def Mux(sel, val1, val0):
    """Multiplex between two values

    Parameters
    ----------
    sel : _Value(1), in
        Selector.
    val1 : _Value(N), in
    val0 : _Value(N), in
        Input values.

    Returns
    -------
    _Value(N), out
        Output `_Value`. If `sel` is asserted, the Mux returns
        `val1`, else `val0`.
    """
    return _Operator("m", [sel, val1, val0])

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

class Cat(_Value):
    """Concatenate values

    Form a compound `_Value` from several smaller ones by concatenation.
    The first argument occupies the lower bits of the result.
    The return value can be used on either side of an assignment, that
    is, the concatenated value can be used as an argument on the RHS or
    as a target on the LHS. If it is used on the LHS, it must solely
    consist of `Signal` s, slices of `Signal` s, and other concatenations
    meeting these properties. The bit length of the return value is the sum of
    the bit lengths of the arguments::

        len(Cat(args)) == sum(len(arg) for arg in args)

    Parameters
    ----------
    *args : _Values or iterables of _Values, inout
        `_Value` s to be concatenated.

    Returns
    -------
    Cat, inout
        Resulting `_Value` obtained by concatentation.
    """
    def __init__(self, *args):
        _Value.__init__(self)
        self.l = [wrap(v) for v in flat_iteration(args)]

class Replicate(_Value):
    """Replicate a value

    An input value is replicated (repeated) several times
    to be used on the RHS of assignments::

        len(Replicate(s, n)) == len(s)*n

    Parameters
    ----------
    v : _Value, in
        Input value to be replicated.
    n : int
        Number of replications.

    Returns
    -------
    Replicate, out
        Replicated value.
    """
    def __init__(self, v, n):
        _Value.__init__(self)
        if not isinstance(n, int) or n < 0:
            raise TypeError("Replication count must be a positive integer")
        self.v = wrap(v)
        self.n = n

class Constant(_Value):
    """A constant, HDL-literal integer `_Value`

    Parameters
    ----------
    value : int
    bits_sign : int or tuple or None
        Either an integer `bits` or a tuple `(bits, signed)`
        specifying the number of bits in this `Constant` and whether it is
        signed (can represent negative values). `bits_sign` defaults
        to the minimum width and signedness of `value`.
    """
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

C = Constant  # shorthand

class Signal(_Value):
    """A `_Value` that can change

    The `Signal` object represents a value that is expected to change
    in the circuit. It does exactly what Verilog's `wire` and
    `reg` and VHDL's `signal` do.

    A `Signal` can be indexed to access a subset of its bits. Negative
    indices (`signal[-1]`) and the extended Python slicing notation
    (`signal[start:stop:step]`) are supported.
    The indices 0 and -1 are the least and most significant bits
    respectively.

    Parameters
    ----------
    bits_sign : int or tuple
        Either an integer `bits` or a tuple `(bits, signed)`
        specifying the number of bits in this `Signal` and whether it is
        signed (can represent negative values). `signed` defaults to
        `False`.
    name : str or None
        Name hint for this signal. If `None` (default) the name is
        inferred from the variable name this `Signal` is assigned to.
        Name collisions are automatically resolved by prepending
        names of objects that contain this `Signal` and by
        appending integer sequences.
    variable : bool
        Deprecated.
    reset : int
        Reset (synchronous) or default (combinatorial) value.
        When this `Signal` is assigned to in synchronous context and the
        corresponding clock domain is reset, the `Signal` assumes the
        given value. When this `Signal` is unassigned in combinatorial
        context (due to conditional assignments not being taken),
        the `Signal` assumes its `reset` value. Defaults to 0.
    reset_less : bool
        If `True`, do not generate reset logic for this `Signal` in
        synchronous statements. The `reset` value is only used as a
        combinatorial default or as the initial value. Defaults to `False`.
    name_override : str or None
        Do not use the inferred name but the given one.
    min : int or None
    max : int or None
        If `bits_sign` is `None`, the signal bit width and signedness are
        determined by the integer range given by `min` (inclusive,
        defaults to 0) and `max` (exclusive, defaults to 2).
    related : Signal or None
    attr : set of synthesis attributes
    """
    _name_re = _re.compile(r"^[a-zA-Z_][a-zA-Z0-9_]*$")

    def __init__(self, bits_sign=None, name=None, variable=False, reset=0, reset_less=False, name_override=None, min=None, max=None, related=None, attr=None):
        _Value.__init__(self)

        for n in [name, name_override]:
            if n is not None and not self._name_re.match(n):
                raise ValueError("Signal name {} is not a valid Python identifier".format(repr(n)))

        # determine number of bits and signedness
        if bits_sign is None:
            if min is None:
                min = 0
            if max is None:
                max = 2
            max -= 1  # make both bounds inclusive
            assert(min < max)
            self.signed = min < 0 or max < 0
            self.nbits = builtins.max(bits_for(min, self.signed), bits_for(max, self.signed))
        else:
            assert(min is None and max is None)
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

        self.name = name
        self.variable = variable  # deprecated
        self.reset = reset
        self.reset_less = reset_less
        self.name_override = name_override
        self.related = related
        self.attr = attr

    def __setattr__(self, k, v):
        if k == "reset":
            v = wrap(v)
        _Value.__setattr__(self, k, v)

    def __repr__(self):
        return "<Signal " + (self.name_override or self.name or "anonymous") + " at " + hex(id(self)) + ">"

    @classmethod
    def like(cls, other, **kwargs):
        """Create Signal based on another.

        Parameters
        ----------
        other : _Value
            Object to base this Signal on.
        """
        kw = dict(bits_sign=value_bits_sign(other))
        if isinstance(other, cls):
            kw.update(variable=other.variable, reset=other.reset.value, reset_less=other.reset_less, related=other.related, attr=set(other.attr))
        kw.update(kwargs)
        return cls(**kw)

    def __hash__(self):
        return self.duid

class ClockSignal(_Value):
    """Clock signal for a given clock domain

    `ClockSignal` s for a given clock domain can be retrieved multiple
    times. They all ultimately refer to the same signal.

    Parameters
    ----------
    cd : str
        Clock domain to obtain a clock signal for. Defaults to `"sys"`.
    """
    def __init__(self, cd="sys"):
        _Value.__init__(self)
        if not isinstance(cd, str):
            raise TypeError("Argument of ClockSignal must be a string")
        self.cd = cd

class ResetSignal(_Value):
    """Reset signal for a given clock domain

    `ResetSignal` s for a given clock domain can be retrieved multiple
    times. They all ultimately refer to the same signal.

    Parameters
    ----------
    cd : str
        Clock domain to obtain a reset signal for. Defaults to `"sys"`.
    allow_reset_less : bool
        If the clock domain is resetless, return 0 instead of reporting an
        error.
    """
    def __init__(self, cd="sys", allow_reset_less=False):
        _Value.__init__(self)
        if not isinstance(cd, str):
            raise TypeError("Argument of ResetSignal must be a string")
        self.cd = cd
        self.allow_reset_less = allow_reset_less

# statements

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
    """Conditional execution of statements

    Parameters
    ----------
    cond : _Value(1), in
        Condition
    *t : Statements
        Statements to execute if `cond` is asserted.

    Examples
    --------
    >>> a = Signal()
    >>> b = Signal()
    >>> c = Signal()
    >>> d = Signal()
    >>> If(a,
    ...     b.eq(1)
    ... ).Elif(c,
    ...     b.eq(0)
    ... ).Else(
    ...     b.eq(d)
    ... )
    """
    def __init__(self, cond, *t):
        if not _check_statement(t):
            raise TypeError("Not all test body objects are Eigen statements")
        self.cond = wrap(cond)
        self.t = list(t)
        self.f = []

    def Else(self, *f):
        """Add an `else` conditional block

        Parameters
        ----------
        *f : Statements
            Statements to execute if all previous conditions fail.
        """
        if not _check_statement(f):
            raise TypeError("Not all test body objects are Eigen statements")
        _insert_else(self, list(f))
        return self

    def Elif(self, cond, *t):
        """Add an `else if` conditional block

        Parameters
        ----------
        cond : _Value(1), in
            Condition
        *t : Statements
            Statements to execute if previous conditions fail and `cond`
            is asserted.
        """
        _insert_else(self, [If(cond, *t)])
        return self

def _insert_else(obj, clause):
    o = obj
    while o.f:
        assert(len(o.f) == 1)
        assert(isinstance(o.f[0], If))
        o = o.f[0]
    o.f = clause

class Case(_Statement):
    """Case/Switch statement

    Parameters
    ----------
    test : _Value, in
        Selector value used to decide which block to execute
    cases : dict
        Dictionary of cases. The keys are numeric constants to compare
        with `test`. The values are statements to be executed the
        corresponding key matches `test`. The dictionary may contain a
        string key `"default"` to mark a fall-through case that is
        executed if no other key matches.

    Examples
    --------
    >>> a = Signal()
    >>> b = Signal()
    >>> Case(a, {
    ...     0:         b.eq(1),
    ...     1:         b.eq(0),
    ...     "default": b.eq(0),
    ... })
    """
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

    def makedefault(self, key=None):
        """Mark a key as the default case

        Deletes/substitutes any previously existing default case.

        Parameters
        ----------
        key : int, Constant or None
            Key to use as default case if no other key matches.
            By default, the largest key is the default key.
        """
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

# arrays

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

class Array(list):
    """Addressable multiplexer

    An array is created from an iterable of values and indexed using the
    usual Python simple indexing notation (no negative indices or
    slices). It can be indexed by numeric constants, `_Value` s, or
    `Signal` s.

    The result of indexing the array is a proxy for the entry at the
    given index that can be used on either RHS or LHS of assignments.

    An array can be indexed multiple times.

    Multidimensional arrays are supported by packing inner arrays into
    outer arrays.

    Parameters
    ----------
    values : iterable of ints, _Values, Signals
        Entries of the array. Each entry can be a numeric constant, a
        `Signal` or a `Record`.

    Examples
    --------
    >>> a = Array(range(10))
    >>> b = Signal(max=10)
    >>> c = Signal(max=10)
    >>> b.eq(a[9 - c])
    """
    def __getitem__(self, key):
        if isinstance(key, Constant):
            return list.__getitem__(self, key.value)
        elif isinstance(key, _Value):
            return _ArrayProxy(self, key)
        else:
            return list.__getitem__(self, key)

# clock domains

class ClockDomain:
    """Synchronous domain

    Parameters
    ----------
    name : str or None
        Domain name. If None (the default) the name is inferred from the
        variable name this `ClockDomain` is assigned to (stripping any
        `"cd_"` prefix).
    reset_less : bool
        The domain does not use a reset signal. Registers within this
        domain are still all initialized to their reset state once, e.g.
        through Verilog `"initial"` statements.

    Attributes
    ----------
    clk : Signal, inout
        The clock for this domain. Can be driven or used to drive other
        signals (preferably in combinatorial context).
    rst : Signal or None, inout
        Reset signal for this domain. Can be driven or used to drive.
    """
    def __init__(self, name, reset_less=False):
        self.name = name
        if self.name is None:
            raise ValueError("Cannot extract clock domain name from code, need to specify.")
        if self.name.startswith("cd_"):
            self.name = self.name[3:]
        if self.name[0].isdigit():
            raise ValueError("Clock domain name cannot start with a number.")
        self.clk = Signal(name_override=self.name + "_clk")
        if reset_less:
            self.rst = None
        else:
            self.rst = Signal(name_override=self.name + "_rst")

    def rename(self, new_name):
        """Rename the clock domain

        Parameters
        ----------
        new_name : str
            New name
        """
        self.name = new_name
        self.clk.name_override = new_name + "_clk"
        if self.rst is not None:
            self.rst.name_override = new_name + "_rst"

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

# specials

(SPECIAL_INPUT, SPECIAL_OUTPUT, SPECIAL_INOUT) = range(3)

# simulation

class Display(_Statement):
    def __init__(self, s, *args):
        self.s = s
        self.args = args

class Finish(_Statement):
    pass

# fragment

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
        if isinstance(node, Constant):
            self.visit_Constant(node)
        elif isinstance(node, Signal):
            self.visit_Signal(node)
        elif isinstance(node, ClockSignal):
            self.visit_ClockSignal(node)
        elif isinstance(node, ResetSignal):
            self.visit_ResetSignal(node)
        elif isinstance(node, _Operator):
            self.visit_Operator(node)
        elif isinstance(node, _Slice):
            self.visit_Slice(node)
        elif isinstance(node, Cat):
            self.visit_Cat(node)
        elif isinstance(node, Replicate):
            self.visit_Replicate(node)
        elif isinstance(node, _Assign):
            self.visit_Assign(node)
        elif isinstance(node, If):
            self.visit_If(node)
        elif isinstance(node, Case):
            self.visit_Case(node)
        elif isinstance(node, _Fragment):
            self.visit_Fragment(node)
        elif isinstance(node, (list, tuple)):
            self.visit_statements(node)
        elif isinstance(node, dict):
            self.visit_clock_domains(node)
        elif isinstance(node, _ArrayProxy):
            self.visit_ArrayProxy(node)
        else:
            self.visit_unknown(node)

    def visit_Constant(self, node):
        pass

    def visit_Signal(self, node):
        pass

    def visit_ClockSignal(self, node):
        pass

    def visit_ResetSignal(self, node):
        pass

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
        for clockname, statements in sorted(node.items(), key=itemgetter(0)):
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
        if isinstance(node, Constant):
            return self.visit_Constant(node)
        elif isinstance(node, Signal):
            return self.visit_Signal(node)
        elif isinstance(node, ClockSignal):
            return self.visit_ClockSignal(node)
        elif isinstance(node, ResetSignal):
            return self.visit_ResetSignal(node)
        elif isinstance(node, _Operator):
            return self.visit_Operator(node)
        elif isinstance(node, _Slice):
            return self.visit_Slice(node)
        elif isinstance(node, _Part):
            return self.visit_Part(node)
        elif isinstance(node, Cat):
            return self.visit_Cat(node)
        elif isinstance(node, Replicate):
            return self.visit_Replicate(node)
        elif isinstance(node, _Assign):
            return self.visit_Assign(node)
        elif isinstance(node, If):
            return self.visit_If(node)
        elif isinstance(node, Case):
            return self.visit_Case(node)
        elif isinstance(node, _Fragment):
            return self.visit_Fragment(node)
        elif isinstance(node, (list, tuple)):
            return self.visit_statements(node)
        elif isinstance(node, dict):
            return self.visit_clock_domains(node)
        elif isinstance(node, _ArrayProxy):
            return self.visit_ArrayProxy(node)
        else:
            return self.visit_unknown(node)

    def visit_Constant(self, node):
        return node

    def visit_Signal(self, node):
        return node

    def visit_ClockSignal(self, node):
        return node

    def visit_ResetSignal(self, node):
        return node

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
        return {clockname: self.visit(statements) for clockname, statements in sorted(node.items(), key=itemgetter(0))}

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
    return [(targets, _resort_statements(stmts))
        for targets, stmts in groups]

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
        array_muxed = Signal(value_bits_sign(node), variable=True)
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
            slice_proxy = Signal(value_bits_sign(node.value))
            if self.target_context:
                a = _Assign(node.value, slice_proxy)
            else:
                a = _Assign(slice_proxy, node.value)
            self.comb.append(self.visit_Assign(a))
            node = _Slice(slice_proxy, node.start, node.stop)
        return NodeTransformer.visit_Slice(self, node)

class _ComplexPartLowerer(_Lowerer):
    def visit_Part(self, node):
        value_proxy = node.value
        offset_proxy = node.offset
        if not isinstance(node.value, Signal):
            value_proxy = Signal(value_bits_sign(node.value))
            if self.target_context:
                a = _Assign(node.value, value_proxy)
            else:
                a = _Assign(value_proxy, node.value)
            self.comb.append(self.visit_Assign(a))
        if not isinstance(node.offset, Signal):
            offset_proxy = Signal(value_bits_sign(node.offset))
            if self.target_context:
                a = _Assign(node.offset, offset_proxy)
            else:
                a = _Assign(offset_proxy, node.offset)
            self.comb.append(self.visit_Assign(a))
        node = _Part(value_proxy, offset_proxy, node.width)
        return NodeTransformer.visit_Part(self, node)

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

def lower_complex_parts(f):
    return _apply_lowerer(_ComplexPartLowerer(), f)

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
    cdr = _ClockDomainRenamer(old, new)
    cdr.visit(f)

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

# _ModuleForwardAttr enables user classes to do e.g.:
# self.subm.foobar = SomeModule()
# and then access the submodule with self.foobar.

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
        assert(not self.get_fragment_called)
        self.get_fragment_called = True
        self.finalize()
        return self._fragment

    def __getattr__(self, name):
        if name == "comb":
            return _ModuleComb(self)
        elif name == "sync":
            return _ModuleSync(self)
        elif name == "specials":
            return _ModuleSpecials(self)
        elif name == "submodules":
            return _ModuleSubmodules(self)
        elif name == "clock_domains":
            return _ModuleClockDomains(self)

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
            ctl = Signal(name=self.control_name)
            assert not hasattr(i, self.control_name)
            setattr(i, self.control_name, ctl)
        else:
            for cd in self.clock_domains:
                name = self.control_name + "_" + cd
                ctl = Signal(name=name)
                assert not hasattr(i, name)
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
        assert(not tristate._isrecord)
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
        self.o = Signal(bits_sign, min=min, max=max, reset=reset_o, name=None if name is None else name + "_o")
        self.oe = Signal(reset=reset_oe, name=None if name is None else name + "_oe")
        self.i = Signal(bits_sign, min=min, max=max, reset=reset_i, name=None if name is None else name + "_i")

    def get_tristate(self, target):
        return Tristate(target, self.o, self.oe, self.i)

    def __len__(self):
        return len(self.o)

class Instance(Special):
    class _IO:
        def __init__(self, name, expr=None):
            self.name = name
            if expr is None:
                expr = Signal()
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
            self.name_override = name
        else:
            self.name_override = of
        self.items = list(items)
        self.synthesis_directive = synthesis_directive
        if attr is None:
            attr = set()
        self.attr = attr
        for k, v in sorted(kwargs.items(), key=itemgetter(0)):
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

class _MemoryLocation(_Value):
    def __init__(self, memory, index):
        _Value.__init__(self)
        self.memory = memory
        self.index = wrap(index)

class Memory(Special):
    def __init__(self, name, width, depth, init=None):
        Special.__init__(self)
        self.width = width
        self.depth = depth
        self.ports = []
        self.init = init
        self.name_override = name or "mem"

    def __getitem__(self, index):
        # simulation only
        return _MemoryLocation(self, index)

    def get_port(self, write_capable=False, async_read=False, has_re=False, we_granularity=0, mode=WRITE_FIRST, clock_domain="sys"):
        if we_granularity >= self.width:
            we_granularity = 0
        adr = Signal(max=self.depth)
        dat_r = Signal(self.width)
        if write_capable:
            if we_granularity:
                we = Signal(self.width//we_granularity)
            else:
                we = Signal()
            dat_w = Signal(self.width)
        else:
            we = None
            dat_w = None
        if has_re:
            re = Signal()
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
        adrbits = bits_for(memory.depth-1)

        r += "reg [" + str(memory.width-1) + ":0] " + gn(memory) + "[0:" + str(memory.depth-1) + "];\n"

        adr_regs = {}
        data_regs = {}
        for port in memory.ports:
            if not port.async_read:
                if port.mode == WRITE_FIRST:
                    adr_reg = Signal(name_override="memadr")
                    r += "reg [" + str(adrbits-1) + ":0] " + gn(adr_reg) + ";\n"
                    adr_regs[id(port)] = adr_reg
                else:
                    data_reg = Signal(name_override="memdat")
                    r += "reg [" + str(memory.width-1) + ":0] " + gn(data_reg) + ";\n"
                    data_regs[id(port)] = data_reg

        for port in memory.ports:
            r += "always @(posedge " + gn(port.clock) + ") begin\n"
            if port.we is not None:
                if port.we_granularity:
                    n = memory.width//port.we_granularity
                    for i in range(n):
                        m = i*port.we_granularity
                        M = (i+1)*port.we_granularity-1
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

class FullMemoryWE(ModuleTransformer):
    def __init__(self):
        self.replacements = dict()

    def transform_fragment(self, i, f):
        newspecials = set()

        for orig in f.specials:
            if not isinstance(orig, Memory):
                newspecials.add(orig)
                continue
            global_granularity = gcd_multiple([p.we_granularity if p.we_granularity else orig.width for p in orig.ports])
            if global_granularity == orig.width:
                newspecials.add(orig)  # nothing to do
            else:
                newmems = []
                for i in range(orig.width//global_granularity):
                    if orig.init is None:
                        newinit = None
                    else:
                        newinit = [(v >> i*global_granularity) & (2**global_granularity - 1) for v in orig.init]
                    newmem = Memory(orig.name_override + "_grain" + str(i), global_granularity, orig.depth, newinit)
                    newspecials.add(newmem)
                    newmems.append(newmem)
                    for port in orig.ports:
                        port_granularity = port.we_granularity if port.we_granularity else orig.width
                        newport = _MemoryPort(
                            adr=port.adr,

                            dat_r=port.dat_r[i*global_granularity:(i+1)*global_granularity] if port.dat_r is not None else None,
                            we=port.we[i*global_granularity//port_granularity] if port.we is not None else None,
                            dat_w=port.dat_w[i*global_granularity:(i+1)*global_granularity] if port.dat_w is not None else None,

                            async_read=port.async_read,
                            re=port.re,
                            we_granularity=0,
                            mode=port.mode,
                            clock_domain=port.clock.cd)
                        newmem.ports.append(newport)
                        newspecials.add(newport)
                self.replacements[orig] = newmems

        f.specials = newspecials
        for oldmem in self.replacements.keys():
            f.specials -= set(oldmem.ports)

class MemoryToArray(ModuleTransformer):
    def __init__(self):
        self.replacements = dict()

    def transform_fragment(self, i, f):
        newspecials = set()
        processed_ports = set()

        for mem in f.specials:
            if not isinstance(mem, Memory):
                newspecials.add(mem)
                continue

            storage = Array()
            self.replacements[mem] = storage
            init = []
            if mem.init is not None:
                init = mem.init
            storage_name = lambda: "%s_data_%d" % (mem.name_override, len(storage))
            for d in init:
                mem_storage = Signal(mem.width, reset=d, name_override=storage_name())
                storage.append(mem_storage)
            for _ in range(mem.depth-len(init)):
                mem_storage = Signal(mem.width, name_override=storage_name())
                storage.append(mem_storage)

            for port in mem.ports:
                try:
                    sync = f.sync[port.clock.cd]
                except KeyError:
                    sync = f.sync[port.clock.cd] = []

                # read
                if port.async_read:
                    f.comb.append(port.dat_r.eq(storage[port.adr]))
                else:
                    if port.mode == WRITE_FIRST:
                        adr_reg = Signal.like(port.adr)
                        rd_stmt = adr_reg.eq(port.adr)
                        f.comb.append(port.dat_r.eq(storage[adr_reg]))
                    elif port.mode == NO_CHANGE and port.we is not None:
                        rd_stmt = If(~port.we, port.dat_r.eq(storage[port.adr]))
                    else: # NO_CHANGE without write capability reduces to READ_FIRST
                        rd_stmt = port.dat_r.eq(storage[port.adr])
                    if port.re is None:
                        sync.append(rd_stmt)
                    else:
                        sync.append(If(port.re, rd_stmt))

                # write
                if port.we is not None:
                    if port.we_granularity:
                        n = mem.width//port.we_granularity
                        for i in range(n):
                            m = i*port.we_granularity
                            M = (i+1)*port.we_granularity
                            sync.append(If(port.we[i], storage[port.adr][m:M].eq(port.dat_w[m:M])))
                    else:
                        sync.append(If(port.we, storage[port.adr].eq(port.dat_w)))

                processed_ports.add(port)

        newspecials -= processed_ports
        f.specials = newspecials

class SplitMemory(ModuleTransformer):
    """Split memories with depths that are not powers of two into smaller
    power-of-two memories.

    This prevents toolchains from rounding up and wasting resources."""

    def transform_fragment(self, i, f):
        old_specials, f.specials = f.specials, set()
        old_ports = set()

        for old in old_specials:
            if not isinstance(old, Memory):
                f.specials.add(old)
                continue
            try:
                log2_int(old.depth, need_pow2=True)
                f.specials.add(old)
            except ValueError:
                new, comb, sync = self._split_mem(old)
                old_ports |= set(old.ports)
                f.specials.update(new)
                f.comb += comb
                for cd, sy in sync.items():
                    s = f.sync.setdefault(cd, [])
                    s += sy
        f.specials -= old_ports

    def _split_mem(self, mem):
        depths = [1 << i for i in range(log2_int(mem.depth, need_pow2=False)) if mem.depth & (1 << i)]
        depths.reverse()
        inits = None
        if mem.init is not None:
            inits = list(mem.init)
        mems = []
        for i, depth in enumerate(depths):
            init = None
            if inits is not None:
                init = inits[:depth]
                del inits[:depth]
            name = "{}_part{}".format(mem.name_override, i)
            mems.append(Memory(name, mem.width, depth, init))
        ports = []
        comb = []
        sync = {}
        for port in mem.ports:
            p, c, s = self._split_port(port, mems)
            ports += p
            comb += c
            sy = sync.setdefault(port.clock.cd, [])
            sy += s
        return mems + ports, comb, sync

    def _split_port(self, port, mems):
        ports = [mem.get_port(write_capable=port.we is not None,
                              async_read=port.async_read,
                              has_re=port.re is not None,
                              we_granularity=port.we_granularity,
                              mode=port.mode,
                              clock_domain=port.clock.cd)
                 for mem in mems]

        sel = Signal(max=len(ports), reset=len(ports) - 1)
        sel_r = Signal.like(sel)
        eq = sel_r.eq(sel)
        if port.re is not None:
            eq = If(port.re, eq)
        comb, sync = [], []
        if port.async_read:
            comb += [eq]
        else:
            sync += [eq]
        comb += reversed([If(~port.adr[len(p.adr)], sel.eq(i)) for i, p in enumerate(ports)])
        comb += [p.adr.eq(port.adr) for p in ports]
        comb.append(port.dat_r.eq(Array([p.dat_r for p in ports])[sel_r]))
        if port.we is not None:
            comb.append(Array([p.we for p in ports])[sel].eq(port.we))
            comb += [p.dat_w.eq(port.dat_w) for p in ports]
        if port.re is not None:
            comb += [p.re.eq(port.re) for p in ports]
        return ports, comb, sync

def split(v, *counts):
    r = []
    offset = 0
    for n in counts:
        if n != 0:
            r.append(v[offset:offset+n])
        else:
            r.append(None)
        offset += n
    return tuple(r)

def displacer(signal, shift, output, n=None, reverse=False):
    if shift is None:
        return output.eq(signal)
    if n is None:
        n = 2**len(shift)
    w = len(signal)
    if reverse:
        r = reversed(range(n))
    else:
        r = range(n)
    l = [Replicate(shift == i, w) & signal for i in r]
    return output.eq(Cat(*l))

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
        cases[i] = [output.eq(signal[s*w:(s+1)*w])]
    return Case(shift, cases).makedefault()

def timeline(trigger, events):
    lastevent = max([e[0] for e in events])
    counter = Signal(max=lastevent+1)

    counterlogic = If(counter != 0,
        counter.eq(counter + 1)
    ).Elif(trigger,
        counter.eq(1)
    )
    # insert counter reset if it doesn't naturally overflow (test if lastevent+1 is a power of 2)
    if (lastevent & (lastevent + 1)) != 0:
        counterlogic = If(counter == lastevent,
            counter.eq(0)
        ).Else(
            counterlogic
        )

    def get_cond(e):
        if e[0] == 0:
            return trigger & (counter == 0)
        else:
            return counter == e[0]
    sync = [If(get_cond(e), *e[1]) for e in events]
    sync.append(counterlogic)
    return sync

class WaitTimer(Module):
    def __init__(self, t):
        self.wait = Signal()
        self.done = Signal()

        count = Signal(bits_for(t), reset=t)
        self.comb += self.done.eq(count == 0)
        self.sync += \
            If(self.wait,
                If(~self.done, count.eq(count - 1))
            ).Else(count.eq(count.reset))

class Encoder(Module):
    """Encode one-hot to binary

    If `n` is low, the `o` th bit in `i` is asserted, else none or
    multiple bits are asserted.

    Parameters
    ----------
    width : int
        Bit width of the input

    Attributes
    ----------
    i : Signal(width), in
        One-hot input
    o : Signal(max=width), out
        Encoded binary
    n : Signal(1), out
        Invalid, either none or multiple input bits are asserted
    """
    def __init__(self, width):
        self.i = Signal(width)  # one-hot
        self.o = Signal(max=max(2, width))  # binary
        self.n = Signal()  # invalid: none or multiple
        act = dict((1<<j, self.o.eq(j)) for j in range(width))
        act["default"] = self.n.eq(1)
        self.comb += Case(self.i, act)

class PriorityEncoder(Module):
    """Priority encode requests to binary

    If `n` is low, the `o` th bit in `i` is asserted and the bits below `o` are unasserted, else `o == 0`.
    The LSB has priority.

    Parameters
    ----------
    width : int
        Bit width of the input

    Attributes
    ----------
    i : Signal(width), in
        Input requests
    o : Signal(max=width), out
        Encoded binary
    n : Signal(1), out
        Invalid, no input bits are asserted
    """
    def __init__(self, width):
        self.i = Signal(width)  # one-hot, lsb has priority
        self.o = Signal(max=max(2, width))  # binary
        self.n = Signal()  # none
        for j in range(width)[::-1]:  # last has priority
            self.comb += If(self.i[j], self.o.eq(j))
        self.comb += self.n.eq(self.i == 0)

class Decoder(Module):
    """Decode binary to one-hot

    If `n` is low, the `i` th bit in `o` is asserted, the others are not, else `o == 0`.

    Parameters
    ----------
    width : int
        Bit width of the output

    Attributes
    ----------
    i : Signal(max=width), in
        Input binary
    o : Signal(width), out
        Decoded one-hot
    n : Signal(1), in
        Invalid, no output bits are to be asserted
    """
    def __init__(self, width):
        self.i = Signal(max=max(2, width))  # binary
        self.n = Signal()  # none/invalid
        self.o = Signal(width)  # one-hot
        act = dict((j, self.o.eq(1<<j)) for j in range(width))
        self.comb += Case(self.i, act)
        self.comb += If(self.n, self.o.eq(0))

class PriorityDecoder(Decoder):
    pass  # same

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

def layout_get(layout, name):
    for f in layout:
        if f[0] == name:
            return f
    raise KeyError(name)

def layout_partial(layout, *elements):
    r = []
    for path in elements:
        path_s = path.split("/")
        last = path_s.pop()
        copy_ref = layout
        insert_ref = r
        for hop in path_s:
            name, copy_ref = layout_get(copy_ref, hop)
            try:
                name, insert_ref = layout_get(insert_ref, hop)
            except KeyError:
                new_insert_ref = []
                insert_ref.append((hop, new_insert_ref))
                insert_ref = new_insert_ref
        insert_ref.append(layout_get(copy_ref, last))
    return r

class Record:
    def __init__(self, layout, name=None, **kwargs):
        self.name = name or "rec"
        self.layout = layout

        if self.name:
            prefix = self.name + "_"
        else:
            prefix = ""
        for f in self.layout:
            if isinstance(f[1], (int, tuple)):  # cases 1/2
                if(len(f) == 3):
                    fname, fsize, fdirection = f
                else:
                    fname, fsize = f
                finst = Signal(fsize, name=prefix + fname, **kwargs)
            elif isinstance(f[1], list):  # case 3
                fname, fsublayout = f
                finst = Record(fsublayout, prefix + fname, **kwargs)
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
                        r.append(self_e.eq(reduce(or_, [getattr(slave, field) for slave in slaves])))
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
                    assert(s_direction == DIR_M_TO_S)
                    r.append(s_signal.eq(m_signal))
            elif m_direction == DIR_S_TO_M:
                s_signals = []
                for iter_slave in iter_slaves:
                    s_signal, s_direction = next(iter_slave)
                    assert(s_direction == DIR_S_TO_M)
                    s_signals.append(s_signal)
                r.append(m_signal.eq(reduce(or_, s_signals)))
            else:
                raise TypeError
        return r

    def __len__(self):
        return layout_len(self.layout)

    def __repr__(self):
        return "<Record " + ":".join(f[0] for f in self.layout) + " at " + hex(id(self)) + ">"

class AnonymousState:
    pass

# do not use namedtuple here as it inherits tuple and the latter is used elsewhere in FHDL
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
                next_value = Signal(bits_sign=value_bits_sign(node.target), related=related)
                next_value_ce = Signal(related=related)
                self.registers.append((node.target, next_value_ce, next_value))
            return next_value.eq(node.value), next_value_ce.eq(1)
        else:
            return node

class FSM(Module):
    """
    Finite state machine

    Any Python objects can be used as states, e.g. strings.

    Parameters
    ----------
    reset_state
        Reset state. Defaults to the first added state.

    Examples
    --------

    >>> self.active = Signal()
    >>> self.bitno = Signal(3)
    >>>
    >>> fsm = FSM(reset_state="START")
    >>> self.submodules += fsm
    >>>
    >>> fsm.act("START",
    ...     self.active.eq(1),
    ...     If(strobe,
    ...         NextState("DATA")
    ...     )
    ... )
    >>> fsm.act("DATA",
    ...     self.active.eq(1),
    ...     If(strobe,
    ...         NextValue(self.bitno, self.bitno + 1),
    ...         If(self.bitno == 7,
    ...             NextState("END")
    ...         )
    ...     )
    ... )
    >>> fsm.act("END",
    ...     self.active.eq(0),
    ...     NextState("STOP")
    ... )

    """
    def __init__(self, reset_state=None):
        self.actions = OrderedDict()
        self.state_aliases = dict()
        self.reset_state = reset_state

        self.before_entering_signals = OrderedDict()
        self.before_leaving_signals = OrderedDict()
        self.after_entering_signals = OrderedDict()
        self.after_leaving_signals = OrderedDict()

    def act(self, state, *statements):
        """
        Schedules `statements` to be executed in `state`. Statements may include:

            * combinatorial statements of form `a.eq(b)`, equivalent to
              `self.comb += a.eq(b)` when the FSM is in the given `state`;
            * synchronous statements of form `NextValue(a, b)`, equivalent to
              `self.sync += a.eq(b)` when the FSM is in the given `state`;
            * a statement of form `NextState(new_state)`, selecting the next state;
            * `If`, `Case`, etc.
        """
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

    def ongoing(self, state):
        """Returns a signal that has the value 1 when the FSM is in the given `state`, and 0 otherwise."""
        is_ongoing = Signal()
        self.act(state, is_ongoing.eq(1))
        return is_ongoing

    def _get_signal(self, d, state):
        if state not in self.actions:
            self.actions[state] = []
        try:
            return d[state]
        except KeyError:
            is_el = Signal()
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

        self.state = Signal(max=nstates, reset=self.encoding[self.reset_state])
        self.state._enumeration = self.decoding
        self.next_state = Signal(max=nstates)
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
        self.request = Signal(n)
        self.grant = Signal(max=max(2, n))
        self.switch_policy = switch_policy
        if self.switch_policy == SP_CE:
            self.ce = Signal()

        if n > 1:
            cases = {}
            for i in range(n):
                switch = []
                for j in reversed(range(i+1, i+n)):
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

"""
Clock domain crossing module
"""

class MultiRegImpl(Module):
    def __init__(self, i, o, odomain, n, reset=0):
        self.i = i
        self.o = o
        self.odomain = odomain

        w, signed = value_bits_sign(self.i)
        self.regs = [Signal((w, signed), reset=reset, reset_less=True) for i in range(n)]

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
        self.i = Signal()
        self.o = Signal()

        toggle_i = Signal(reset_less=True)
        toggle_o = Signal()  # registered reset_less by MultiReg
        toggle_o_r = Signal(reset_less=True)

        sync_i = getattr(self.sync, idomain)
        sync_o = getattr(self.sync, odomain)

        sync_i += If(self.i, toggle_i.eq(~toggle_i))
        self.specials += MultiReg(toggle_i, toggle_o, odomain)
        sync_o += toggle_o_r.eq(toggle_o)
        self.comb += self.o.eq(toggle_o ^ toggle_o_r)

class BusSynchronizer(Module):
    """Clock domain transfer of several bits at once.

    Ensures that all the bits form a single word that was present
    synchronously in the input clock domain (unlike direct use of
    ``MultiReg``)."""
    def __init__(self, width, idomain, odomain, timeout=128):
        self.i = Signal(width)
        self.o = Signal(width, reset_less=True)

        if width == 1:
            self.specials += MultiReg(self.i, self.o, odomain)
        else:
            sync_i = getattr(self.sync, idomain)
            sync_o = getattr(self.sync, odomain)

            starter = Signal(reset=1)
            sync_i += starter.eq(0)
            self.submodules._ping = PulseSynchronizer(idomain, odomain)
            # Extra flop on i->o to avoid race between data and request
            ping_o = Signal()
            sync_o += ping_o.eq(self._ping.o)
            self.submodules._pong = PulseSynchronizer(odomain, idomain)
            self.submodules._timeout = ClockDomainsRenamer(idomain)(
                WaitTimer(timeout))
            self.comb += [
                self._timeout.wait.eq(~self._ping.i),
                self._ping.i.eq(starter | self._pong.o | self._timeout.done),
                self._pong.i.eq(ping_o)
            ]

            ibuffer = Signal(width, reset_less=True)
            obuffer = Signal(width)  # registered reset_less by MultiReg
            sync_i += If(self._pong.o, ibuffer.eq(self.i))
            ibuffer.attr.add("no_retiming")
            self.specials += MultiReg(ibuffer, obuffer, odomain)
            sync_o += If(ping_o, self.o.eq(obuffer))

class GrayCounter(Module):
    def __init__(self, width):
        self.ce = Signal()
        self.q = Signal(width)
        self.q_next = Signal(width)
        self.q_binary = Signal(width)
        self.q_next_binary = Signal(width)

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

class GrayDecoder(Module):
    def __init__(self, width):
        self.i = Signal(width)
        self.o = Signal(width, reset_less=True)

        o_comb = Signal(width)
        self.comb += o_comb[-1].eq(self.i[-1])
        for i in reversed(range(width-1)):
            self.comb += o_comb[i].eq(o_comb[i+1] ^ self.i[i])
        self.sync += self.o.eq(o_comb)

def _inc(signal, modulo):
    if modulo == 2**len(signal):
        return signal.eq(signal + 1)
    else:
        return If(signal == (modulo - 1),
            signal.eq(0)
        ).Else(
            signal.eq(signal + 1)
        )

class _FIFOInterface:
    """
    Data written to the input interface (`din`, `we`, `writable`) is buffered and can be read at the output interface
    (`dout`, `re`, `readable`). The data entry written first to the input also appears first on the output.

    Parameters
    ----------
    width : int
        Bit width for the data.
    depth : int
        Depth of the FIFO.

    Attributes
    ----------
    din : in, width
        Input data
    writable : out
        There is space in the FIFO and `we` can be asserted to load new data.
    we : in
        Write enable signal to latch `din` into the FIFO. Does nothing if `writable` is not asserted.
    dout : out, width
        Output data. Only valid if `readable` is asserted.
    readable : out
        Output data `dout` valid, FIFO not empty.
    re : in
        Acknowledge `dout`. If asserted, the next entry will be available on the next cycle (if `readable` is high then).
    """
    def __init__(self, width, depth):
        self.we = Signal()
        self.writable = Signal()  # not full
        self.re = Signal()
        self.readable = Signal()  # not empty

        self.din = Signal(width, reset_less=True)
        self.dout = Signal(width, reset_less=True)
        self.width = width
        self.depth = depth

    def read(self):
        """Read method for simulation."""
        value = (yield self.dout)
        yield self.re.eq(1)
        yield
        yield self.re.eq(0)
        yield
        return value

    def write(self, data):
        """Write method for simulation."""
        yield self.din.eq(data)
        yield self.we.eq(1)
        yield
        yield self.we.eq(0)
        yield

class _SyncFIFO(Module, _FIFOInterface):
    """Synchronous FIFO (first in, first out)

    Read and write interfaces are accessed from the same clock domain.
    If different clock domains are needed, use :class:`_AsyncFIFO`.

    {interface}
    level : out
        Number of unread entries.
    replace : in
        Replaces the last entry written into the FIFO with `din`.
        Does nothing if that entry has already been read (i.e. the FIFO is empty).
        Assert in conjunction with `we`.
    """
    def __init__(self, width, depth, fwft=True):
        _FIFOInterface.__init__(self, width, depth)

        self.level = Signal(max=depth+1)
        self.replace = Signal()

        produce = Signal(max=depth)
        consume = Signal(max=depth)
        storage = Memory("storage", self.width, depth)
        self.specials += storage

        wrport = storage.get_port(write_capable=True, mode=READ_FIRST)
        self.specials += wrport
        self.comb += [
            If(self.replace,
                wrport.adr.eq(produce-1)
            ).Else(
                wrport.adr.eq(produce)
            ),
            wrport.dat_w.eq(self.din),
            wrport.we.eq(self.we & (self.writable | self.replace))
        ]
        self.sync += If(self.we & self.writable & ~self.replace, _inc(produce, depth))

        do_read = Signal()
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

class _SyncFIFOBuffered(Module, _FIFOInterface):
    """Has an interface compatible with _SyncFIFO with fwft=True,
    but does not use asynchronous RAM reads that are not compatible
    with block RAMs. Increases latency by one cycle."""
    def __init__(self, width, depth):
        _FIFOInterface.__init__(self, width, depth)
        self.submodules.fifo = fifo = _SyncFIFO(width, depth, False)

        self.writable = fifo.writable
        self.din = fifo.din
        self.we = fifo.we
        self.dout = fifo.dout
        self.level = Signal(max=depth+2)

        self.comb += fifo.re.eq(fifo.readable & (~self.readable | self.re))
        self.sync += \
            If(fifo.re,
                self.readable.eq(1),
            ).Elif(self.re,
                self.readable.eq(0),
            )
        self.comb += self.level.eq(fifo.level + self.readable)

class _AsyncFIFO(Module, _FIFOInterface):
    """Asynchronous FIFO (first in, first out)

    Read and write interfaces are accessed from different clock domains,
    named `read` and `write`. Use `ClockDomainsRenamer` to rename to
    other names.

    {interface}
    """
    def __init__(self, width, depth):
        _FIFOInterface.__init__(self, width, depth)

        depth_bits = log2_int(depth, True)

        produce = ClockDomainsRenamer("write")(GrayCounter(depth_bits+1))
        consume = ClockDomainsRenamer("read")(GrayCounter(depth_bits+1))
        self.submodules += produce, consume
        self.comb += [
            produce.ce.eq(self.writable & self.we),
            consume.ce.eq(self.readable & self.re)
        ]

        produce_rdomain = Signal(depth_bits+1)
        produce.q.attr.add("no_retiming")
        self.specials += MultiReg(produce.q, produce_rdomain, "read")
        consume_wdomain = Signal(depth_bits+1)
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

class _AsyncFIFOBuffered(Module, _FIFOInterface):
    """Improves timing when it breaks due to sluggish clock-to-output
    delay in e.g. Xilinx block RAMs. Increases latency by one cycle."""
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
    def __init__(self, description_or_layout=[], name=None, **kwargs):
        if isinstance(description_or_layout, EndpointDescription):
            self.description = description_or_layout
        else:
            self.description = EndpointDescription(description_or_layout)
        Record.__init__(self, self.description.get_full_layout(), name, **kwargs)
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
        self.sink   = sink   = Endpoint(layout)
        self.source = source = Endpoint(layout)

        description = sink.description
        fifo_layout = [
            ("payload", description.payload_layout),
            ("param",   description.param_layout),
            ("first",   1),
            ("last",    1)
        ]

        self.submodules.fifo = fifo = fifo_class(layout_len(fifo_layout), depth)
        fifo_in  = Record(fifo_layout)
        fifo_out = Record(fifo_layout)
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

class SyncFIFO(_FIFOWrapper):
    def __init__(self, layout, depth, buffered=False):
        assert depth >= 0
        if depth >= 2:
            _FIFOWrapper.__init__(self,
                fifo_class = _SyncFIFOBuffered if buffered else _SyncFIFO,
                layout     = layout,
                depth      = depth)
            self.depth = self.fifo.depth
            self.level = self.fifo.level
        elif depth == 1:
            buf = Buffer(layout)
            self.submodules += buf
            self.sink   = buf.sink
            self.source = buf.source
            self.depth  = 1
            self.level  = Signal()
        elif depth == 0:
            self.sink   = Endpoint(layout)
            self.source = Endpoint(layout)
            self.comb += self.sink.connect(self.source)
            self.depth = 0
            self.level = Signal()

class AsyncFIFO(_FIFOWrapper):
    def __init__(self, layout, depth=4, buffered=False):
        assert depth >= 4
        _FIFOWrapper.__init__(self,
            fifo_class = _AsyncFIFOBuffered if buffered else _AsyncFIFO,
            layout     = layout,
            depth      = depth)

class _UpConverter(Module):
    def __init__(self, nbits_from, nbits_to, ratio, reverse):
        self.sink   = sink   = Endpoint([("data", nbits_from)])
        self.source = source = Endpoint([("data", nbits_to), ("valid_token_count", bits_for(ratio))])
        self.latency = 1

        # Control path
        demux      = Signal(max=ratio)
        load_part  = Signal()
        strobe_all = Signal()
        self.comb += [
            sink.ready.eq(~strobe_all | source.ready),
            source.valid.eq(strobe_all),
            load_part.eq(sink.valid & sink.ready)
        ]

        demux_last = ((demux == (ratio - 1)) | sink.last)

        self.sync += [
            If(source.ready, strobe_all.eq(0)),
            If(load_part,
                If(demux_last,
                    demux.eq(0),
                    strobe_all.eq(1)
                ).Else(
                    demux.eq(demux + 1)
                )
            ),
            If(source.valid & source.ready,
                If(sink.valid & sink.ready,
                    source.first.eq(sink.first),
                    source.last.eq(sink.last)
                ).Else(
                    source.first.eq(0),
                    source.last.eq(0)
                )
            ).Elif(sink.valid & sink.ready,
                source.first.eq(sink.first | source.first),
                source.last.eq(sink.last | source.last)
            )
        ]

        # Data path
        cases = {}
        for i in range(ratio):
            n = ratio-i-1 if reverse else i
            cases[i] = source.data[n*nbits_from:(n+1)*nbits_from].eq(sink.data)
        self.sync += If(load_part, Case(demux, cases))

        # Valid token count
        self.sync += If(load_part, source.valid_token_count.eq(demux + 1))

class _DownConverter(Module):
    def __init__(self, nbits_from, nbits_to, ratio, reverse):
        self.sink   = sink   = Endpoint([("data", nbits_from)])
        self.source = source = Endpoint([("data", nbits_to), ("valid_token_count", 1)])
        self.latency = 0

        # Control path
        mux   = Signal(max=ratio)
        first = Signal()
        last  = Signal()
        self.comb += [
            first.eq(mux == 0),
            last.eq(mux == (ratio-1)),
            source.valid.eq(sink.valid),
            source.first.eq(sink.first & first),
            source.last.eq(sink.last & last),
            sink.ready.eq(last & source.ready)
        ]
        self.sync += \
            If(source.valid & source.ready,
                If(last,
                    mux.eq(0)
                ).Else(
                    mux.eq(mux + 1)
                )
            )

        # Data path
        cases = {}
        for i in range(ratio):
            n = ratio-i-1 if reverse else i
            cases[i] = source.data.eq(sink.data[n*nbits_to:(n+1)*nbits_to])
        self.comb += Case(mux, cases).makedefault()

        # Valid token count
        self.comb += source.valid_token_count.eq(last)

class _IdentityConverter(Module):
    def __init__(self, nbits_from, nbits_to, ratio, reverse):
        self.sink   = sink   = Endpoint([("data", nbits_from)])
        self.source = source = Endpoint([("data", nbits_to), ("valid_token_count", 1)])
        self.latency = 0

        self.comb += [
            sink.connect(source),
            source.valid_token_count.eq(1)
        ]

def _get_converter_ratio(nbits_from, nbits_to):
    if nbits_from > nbits_to:
        converter_cls = _DownConverter
        if nbits_from % nbits_to:
            raise ValueError("Ratio must be an int")
        ratio = nbits_from//nbits_to
    elif nbits_from < nbits_to:
        converter_cls = _UpConverter
        if nbits_to % nbits_from:
            raise ValueError("Ratio must be an int")
        ratio = nbits_to//nbits_from
    else:
        converter_cls = _IdentityConverter
        ratio = 1
    return converter_cls, ratio

class Converter(Module):
    def __init__(self, nbits_from, nbits_to,
        reverse                  = False,
        report_valid_token_count = False):
        self.cls, self.ratio = _get_converter_ratio(nbits_from, nbits_to)

        converter = self.cls(nbits_from, nbits_to, self.ratio, reverse)
        self.submodules += converter
        self.latency = converter.latency

        self.sink = converter.sink
        if report_valid_token_count:
            self.source = converter.source
        else:
            self.source = Endpoint([("data", nbits_to)])
            self.comb += converter.source.connect(self.source, omit=set(["valid_token_count"]))

class StrideConverter(Module):
    def __init__(self, description_from, description_to, reverse=False):
        self.sink   = sink   = Endpoint(description_from)
        self.source = source = Endpoint(description_to)

        nbits_from = len(sink.payload.raw_bits())
        nbits_to   = len(source.payload.raw_bits())

        converter = Converter(nbits_from, nbits_to, reverse)
        self.submodules += converter

        # Cast sink to converter.sink (user fields --> raw bits)
        self.comb += [
            converter.sink.valid.eq(sink.valid),
            converter.sink.first.eq(sink.first),
            converter.sink.last.eq(sink.last),
            sink.ready.eq(converter.sink.ready)
        ]
        if converter.cls == _DownConverter:
            ratio = converter.ratio
            for i in range(ratio):
                j = 0
                for name, width in source.description.payload_layout:
                    src = getattr(sink, name)[i*width:(i+1)*width]
                    dst = converter.sink.data[i*nbits_to+j:i*nbits_to+j+width]
                    self.comb += dst.eq(src)
                    j += width
        else:
            self.comb += converter.sink.data.eq(sink.payload.raw_bits())

        # Cast converter.source to source (raw bits --> user fields)
        self.comb += [
            source.valid.eq(converter.source.valid),
            source.first.eq(converter.source.first),
            source.last.eq(converter.source.last),
            converter.source.ready.eq(source.ready)
        ]
        if converter.cls == _UpConverter:
            ratio = converter.ratio
            for i in range(ratio):
                j = 0
                for name, width in sink.description.payload_layout:
                    src = converter.source.data[i*nbits_from+j:i*nbits_from+j+width]
                    dst = getattr(source, name)[i*width:(i+1)*width]
                    self.comb += dst.eq(src)
                    j += width
        else:
            self.comb += source.payload.raw_bits().eq(converter.source.data)

        # Connect params
        if converter.latency == 0:
            self.comb += source.param.eq(sink.param)
        elif converter.latency == 1:
            self.sync += source.param.eq(sink.param)
        else:
            raise ValueError

class PipeValid(Module):
    """Pipe valid/payload to cut timing path"""
    def __init__(self, layout):
        self.sink   = sink   = Endpoint(layout)
        self.source = source = Endpoint(layout)

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

class Buffer(PipeValid): pass # FIXME: Replace Buffer with PipeValid in codebase?

class Pipeline(Module):
    def __init__(self, *modules):
        n = len(modules)
        m = modules[0]
        # expose sink of first module
        # if available
        if hasattr(m, "sink"):
            self.sink = m.sink
        for i in range(1, n):
            m_n = modules[i]
            if isinstance(m, Endpoint):
                source = m
            else:
                source = m.source
            if isinstance(m_n, Endpoint):
                sink = m_n
            else:
                sink = m_n.sink
            if m is not m_n:
                self.comb += source.connect(sink)
            m = m_n
        # expose source of last module if available
        if hasattr(m, "source"):
            self.source = m.source

"""
Configuration and Status Registers
**********************************

The lowest-level description of a register is provided by the ``CSR`` class,
which maps to the value at a single address on the target bus. Also provided
are helper classes for dealing with values larger than the CSR buses data
width.

 * ``CSRConstant``, for constant values.
 * ``CSRStatus``,   for providing information to the CPU.
 * ``CSRStorage``,  for allowing control via the CPU.

Generating register banks
=========================
A module can provide bus-independent CSRs by implementing a ``get_csrs`` method
that returns a list of instances of the classes described above.

Similarly, bus-independent memories can be returned as a list by a
``get_memories`` method.

To avoid listing those manually, a module can inherit from the ``AutoCSR``
class, which provides ``get_csrs`` and ``get_memories`` methods that scan for
CSR and memory attributes and return their list.
"""

class _CSRBase(DUID):
    def __init__(self, name, size):
        DUID.__init__(self)
        self.name = name
        if self.name is None:
            raise ValueError("Cannot extract CSR name from code, need to specify.")
        self.size = size

class CSRConstant(DUID):
    """Register which contains a constant value.

    Useful for providing information on how a HDL was instantiated to firmware
    running on the device.
    """

    def __init__(self, value, bits_sign=None, name=None):
        DUID.__init__(self)
        self.value = Constant(value, bits_sign)
        self.name = name
        if self.name is None:
            raise ValueError("Cannot extract CSR name from code, need to specify.")

    def read(self):
        """Read method for simulation."""
        return self.value.value

class CSR(_CSRBase):
    """Basic CSR register.

    Parameters
    ----------
    size : int
        Size of the CSR register in bits.
        Must be less than CSR bus width!

    name : string
        Provide (or override the name) of the CSR register.

    Attributes
    ----------
    r : Signal(size), out
        Contains the data written from the bus interface.
        ``r`` is only valid when ``re`` is high.

    re : Signal(), out
        The strobe signal for ``r``.
        It is active for one cycle, after or during a write from the bus.

    w : Signal(size), in
        The value to be read from the bus.
        Must be provided at all times.

    we : Signal(), out
        The strobe signal for ``w``.
        It is active for one cycle, after or during a read from the bus.
    """

    def __init__(self, name, size=1):
        _CSRBase.__init__(self, name, size)
        self.re = Signal(name=self.name + "_re")
        self.r  = Signal(self.size, name=self.name + "_r")
        self.we = Signal(name=self.name + "_we")
        self.w  = Signal(self.size, name=self.name + "_w")

    def read(self):
        """Read method for simulation."""
        yield self.we.eq(1)
        value = (yield self.w)
        yield
        yield self.we.eq(0)
        return value

    def write(self, value):
        """Write method for simulation."""
        yield self.r.eq(value)
        yield self.re.eq(1)
        yield
        yield self.re.eq(0)

class _CompoundCSR(_CSRBase, Module):
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

class CSRField(Signal):
    """CSR Field.

    Parameters / Attributes
    -----------------------
    name : string
        Name of the CSR field.

    size : int
        Size of the CSR field in bits.

    offset : int (optional)
        Offset of the CSR field on the CSR register in bits.

    reset: int (optional)
        Reset value of the CSR field.

    description: string (optional)
        Description of the CSR Field (can be used to document the code and/or to be reused by tools
        to create the documentation).

    pulse: boolean (optional)
        Field value is only valid for one cycle when set to True. Only valid for 1-bit fields.

    access: enum (optional)
        Access type of the CSR field.

    values: list (optional)
        A list of supported values.
        If this is specified, a table will be generated containing the values in the specified order.
        The `value` must be an integer in order to allow for automatic constant generation in an IDE,
        except "do not care" bits are allowed.
        In the three-tuple variation, the middle value represents an enum value that can be displayed
        instead of the value.
                    [
                        ("0b0000", "disable the timer"),
                        ("0b0001", "slow", "slow timer"),
                        ("0b1xxx", "fast timer"),
                    ]
    """

    def __init__(self, name, size=1, offset=None, reset=0, description=None, pulse=False, access=None, values=None):
        assert access is None or (access in CSRAccess.values())
        self.name        = name
        self.size        = size
        self.offset      = offset
        self.reset_value = reset
        self.description = description
        self.access      = access
        self.pulse       = pulse
        self.values      = values
        Signal.__init__(self, size, name=name, reset=reset)

class CSRFieldAggregate:
    """CSR Field Aggregate."""

    def __init__(self, fields, access):
        self.check_names(fields)
        self.check_ordering_overlap(fields)
        self.fields = fields
        for field in fields:
            if field.access is None:
                field.access = access
            elif field.access == CSRAccess.ReadOnly:
                assert not field.pulse
                assert field.access == CSRAccess.ReadOnly
            elif field.access == CSRAccess.ReadWrite:
                assert field.access in [CSRAccess.ReadWrite, CSRAccess.WriteOnly]
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

class CSRStatus(_CompoundCSR):
    """Status Register.

    The ``CSRStatus`` class is meant to be used as a status register that is read-only from the CPU.

    The user design is expected to drive its ``status`` signal.

    The advantage of using ``CSRStatus`` instead of using ``CSR`` and driving ``w`` is that the
    width of ``CSRStatus`` can be arbitrary.

    Status registers larger than the bus word width are automatically broken down into several
    ``CSR`` registers to span several addresses.

    *Be careful, though:* the atomicity of reads is not guaranteed.

    Parameters
    ----------
    size : int
        Size of the CSR register in bits.
        Can be bigger than the CSR bus width.

    reset : string
        Value of the register after reset.

    name : string
        Provide (or override the name) of the ``CSRStatus`` register.

    Attributes
    ----------
    status : Signal(size), in
        The value of the CSRStatus register.
    """

    def __init__(self, name, size=1, reset=0, fields=[], description=None):
        if fields != []:
            self.fields = CSRFieldAggregate(fields, CSRAccess.ReadOnly)
            size  = self.fields.get_size()
            reset = self.fields.get_reset()
        _CompoundCSR.__init__(self, name, size)
        self.description = description
        self.status = Signal(self.size, reset=reset)
        self.we = Signal()
        for field in fields:
            self.comb += self.status[field.offset:field.offset + field.size].eq(getattr(self.fields, field.name))

    def do_finalize(self, busword):
        nwords = (self.size + busword - 1)//busword
        for i in reversed(range(nwords)):
            nbits = min(self.size - i*busword, busword)
            sc = CSR(self.name + str(i) if nwords > 1 else self.name, nbits)
            self.comb += sc.w.eq(self.status[i*busword:i*busword+nbits])
            self.simple_csrs.append(sc)
        self.comb += self.we.eq(sc.we)

    def read(self):
        """Read method for simulation."""
        yield self.we.eq(1)
        value = (yield self.status)
        yield
        yield self.we.eq(0)
        return value

class CSRStorage(_CompoundCSR):
    """Control Register.

    The ``CSRStorage`` class provides a memory location that can be read and written by the CPU, and read and optionally written by the design.

    It can span several CSR addresses.

    Parameters
    ----------
    size : int
        Size of the CSR register in bits. Can be bigger than the CSR bus width.

    reset : string
        Value of the register after reset.

    reset_less : bool
        If `True`, do not generate reset logic for CSRStorage.

    atomic_write : bool
        Provide an mechanism for atomic CPU writes is provided. When enabled, writes to the first
        CSR addresses go to a back-buffer whose contents are atomically copied to the main buffer
        when the last address is written.

    write_from_dev : bool
        Allow the design to update the CSRStorage value. *Warning*: The atomicity of reads by the
         CPU is not guaranteed.

    name : string
        Provide (or override the name) of the ``CSRStatus`` register.

    Attributes
    ----------
    storage : Signal(size), out
        Signal providing the value of the ``CSRStorage`` object.

    re : Signal(), in
        The strobe signal indicating a write to the ``CSRStorage`` register from the CPU. It is active
        for one cycle, after or during a write from the bus.

    we : Signal(), out
        The strobe signal to write to the ``CSRStorage`` register from the logic. Only available when
        ``write_from_dev == True``

    dat_w : Signal(), out
        The write data to write to the ``CSRStorage`` register from the logic. Only available when
        ``write_from_dev == True``
    """

    def __init__(self, name, size=1, reset=0, reset_less=False, fields=[], atomic_write=False, write_from_dev=False, description=None):
        if fields != []:
            self.fields = CSRFieldAggregate(fields, CSRAccess.ReadWrite)
            size  = self.fields.get_size()
            reset = self.fields.get_reset()
        _CompoundCSR.__init__(self, name, size)
        self.description = description
        self.storage = Signal(self.size, reset=reset, reset_less=reset_less)
        self.atomic_write = atomic_write
        self.re = Signal()
        if write_from_dev:
            self.we = Signal()
            self.dat_w = Signal(self.size)
            self.sync += If(self.we, self.storage.eq(self.dat_w))
        for field in [*fields]:
            field_assign = getattr(self.fields, field.name).eq(self.storage[field.offset:field.offset + field.size])
            if field.pulse:
                self.comb += If(self.re, field_assign)
            else:
                self.comb += field_assign

    def do_finalize(self, busword):
        nwords = (self.size + busword - 1)//busword
        if nwords > 1 and self.atomic_write:
            backstore = Signal(self.size - busword, name=self.name + "_backstore")
        for i in reversed(range(nwords)):
            nbits = min(self.size - i*busword, busword)
            sc = CSR(self.name + str(i) if nwords else self.name, nbits)
            self.simple_csrs.append(sc)
            lo = i*busword
            hi = lo+nbits
            # read
            self.comb += sc.w.eq(self.storage[lo:hi])
            # write
            if nwords > 1 and self.atomic_write:
                if i:
                    self.sync += If(sc.re, backstore[lo-busword:hi-busword].eq(sc.r))
                else:
                    self.sync += If(sc.re, self.storage.eq(Cat(sc.r, backstore)))
            else:
                self.sync += If(sc.re, self.storage[lo:hi].eq(sc.r))
        self.sync += self.re.eq(sc.re)

    def read(self):
        """Read method for simulation."""
        return (yield self.storage)

    def write(self, value):
        """Write method for simulation."""
        yield self.storage.eq(value)
        yield self.re.eq(1)
        if hasattr(self, "fields"):
            for field in [*self.fields.fields]:
                yield getattr(self.fields, field.name).eq((value >> field.offset) & (2**field.size -1))
        yield
        yield self.re.eq(0)
        if hasattr(self, "fields"):
            for field in [*self.fields.fields]:
                if field.pulse:
                    yield getattr(self.fields, field.name).eq(0)

def csrprefix(prefix, csrs, done):
    for csr in csrs:
        if csr.duid not in done:
            csr.name = prefix + csr.name
            done.add(csr.duid)

def memprefix(prefix, memories, done):
    for memory in memories:
        if memory.duid not in done:
            memory.name_override = prefix + memory.name_override
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
        for k, v in xdir(self, True):
            if k not in exclude:
                if isinstance(v, cls):
                    r.append(v)
                elif hasattr(v, method) and callable(getattr(v, method)):
                    items = getattr(v, method)()
                    prefix_cb(k + "_", items, prefixed)
                    r += items
        return sorted(r, key=lambda x: x.duid)
    return gatherer

class AutoCSR:
    """MixIn to provide bus independent access to CSR registers.

    A module can inherit from the ``AutoCSR`` class, which provides ``get_csrs``, ``get_memories``
    and ``get_constants`` methods that scan for CSR and memory attributes and return their list.

    If the module has child objects that implement ``get_csrs``, ``get_memories`` or ``get_constants``,
    they will be called by the``AutoCSR`` methods and their CSR and memories added to the lists returned,
    with the child objects' names as prefixes.
    """
    get_memories = _make_gatherer("get_memories", Memory, memprefix)
    get_csrs = _make_gatherer("get_csrs", _CSRBase, csrprefix)
    get_constants = _make_gatherer("get_constants", CSRConstant, csrprefix)

class GenericBank(Module):
    def __init__(self, description, busword):
        # Turn description into simple CSRs and claim ownership of compound CSR modules
        self.simple_csrs = []
        for c in description:
            if isinstance(c, CSR):
                assert c.size <= busword
                self.simple_csrs.append(c)
            else:
                c.finalize(busword)
                self.simple_csrs += c.get_simple_csrs()
                self.submodules += c
        self.decode_bits = bits_for(len(self.simple_csrs)-1)

"""
CSR-2 bus
=========

The CSR-2 bus is a low-bandwidth, resource-sensitive bus designed for accessing
the configuration and status registers of cores from software.
"""

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
        Record.__init__(self, set_layout_parameters(_csr_bus_layout, data_width=data_width, address_width=address_width))
        self.adr.reset_less   = True
        self.dat_w.reset_less = True
        self.dat_r.reset_less = True

    @classmethod
    def like(self, other):
        return CSRBusInterface(len(other.dat_w), len(other.adr))

    def write(self, adr, dat):
        yield self.adr.eq(adr)
        yield self.dat_w.eq(dat)
        yield self.we.eq(1)
        yield
        yield self.we.eq(0)

    def read(self, adr):
        yield self.adr.eq(adr)
        yield
        yield
        return (yield self.dat_r)

class CSRBusInterconnect(Module):
    def __init__(self, master, slaves):
        self.comb += master.connect(*slaves)

class CSRBusInterconnectShared(Module):
    def __init__(self, masters, slaves):
        intermediate = CSRBusInterface.like(masters[0])
        self.comb += [
            intermediate.adr.eq(reduce(or_, [masters[i].adr for i in range(len(masters))])),
            intermediate.we.eq(reduce(or_, [masters[i].we for i in range(len(masters))])),
            intermediate.dat_w.eq(reduce(or_, [masters[i].dat_w for i in range(len(masters))]))
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
        page_bits = log2_int((mem.depth*csrw_per_memw + aligned_paging - 1) // aligned_paging, False)
        if page_bits:
            self._page = CSRStorage(mem.name_override + "_page", page_bits)
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

        sel = Signal()
        sel_r = Signal()
        self.sync += sel_r.eq(sel)
        self.comb += sel.eq(self.bus.adr[log2_int(aligned_paging):] == address)

        if word_bits:
            word_index    = Signal(word_bits, reset_less=True)
            word_expanded = Signal(csrw_per_memw*data_width)
            self.sync += word_index.eq(self.bus.adr[:word_bits])
            self.comb += [
                word_expanded.eq(port.dat_r),
                If(sel_r, chooser(word_expanded, word_index, self.bus.dat_r, n=csrw_per_memw, reverse=True))
            ]
            if not read_only:
                wregs = []
                for i in range(csrw_per_memw-1):
                    wreg = Signal(data_width, reset_less=True)
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
            self.comb += port.adr.eq(self.bus.adr[word_bits:word_bits+len(port.adr)])
        else:
            pv = self._page.storage
            self.comb += port.adr.eq(Cat(self.bus.adr[word_bits:word_bits+len(port.adr)-len(pv)], pv))

    def get_csrs(self):
        if self._page is None:
            return []
        else:
            return [self._page]

class CSRBank(GenericBank):
    def __init__(self, description, address=0, bus=None, paging=0x800, soc_bus_data_width=32):
        if bus is None:
            bus = CSRBusInterface()
        self.bus = bus
        aligned_paging = paging // (soc_bus_data_width // 8)

        GenericBank.__init__(self, description, len(self.bus.dat_w))

        sel = Signal()
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
        self.scan(ifargs, ifkwargs)

    def scan(self, ifargs, ifkwargs):
        self.banks = []
        self.srams = []
        self.constants = []
        for name, obj in xdir(self.source, True):
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
            if hasattr(obj, "get_constants"):
                for constant in obj.get_constants():
                    self.constants.append((name, constant))
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

class _EventSource(DUID):
    """Base class for EventSources.

    Attributes
    ----------
    trigger : Signal(), in
        Signal which interfaces with the user design.

    status : Signal(), out
        Contains the current level of the trigger signal.
        This value ends up in the ``status`` register.

    pending : Signal(), out
        A trigger event has occurred and not yet cleared.
        This value ends up in the ``pending`` register.

    clear : Signal(), in
        Clear after a trigger event.
        Ignored by some event sources.

    name : str
        A short name for this EventSource, usable as a Python identifier

    description: str
        A formatted description of this EventSource, including when
        it will fire and how it behaves.
    """

    def __init__(self, name=None, description=None):
        DUID.__init__(self)
        self.status = Signal()
        self.pending = Signal()
        self.trigger = Signal()
        self.clear = Signal()
        self.name = name or "evs"
        self.description = description

class EventSourcePulse(Module, _EventSource):
    """EventSource which triggers on a pulse.

    The event stays asserted after the ``trigger`` signal goes low, and until
    software acknowledges it.

    An example use is to pulse ``trigger`` high for 1 cycle after the reception
    of a character in a UART.
    """

    def __init__(self, name=None, description=None):
        _EventSource.__init__(self, name, description)
        self.comb += self.status.eq(0)
        self.sync += [
            If(self.clear, self.pending.eq(0)),
            If(self.trigger, self.pending.eq(1))
        ]

class EventSourceProcess(Module, _EventSource):
    """EventSource which triggers on a falling edge.

    The purpose of this event source is to monitor the status of processes and
    generate an interrupt on their completion.
    """

    def __init__(self, name=None, description=None):
        _EventSource.__init__(self, name, description)
        self.comb += self.status.eq(self.trigger)
        old_trigger = Signal()
        self.sync += [
            If(self.clear, self.pending.eq(0)),
            old_trigger.eq(self.trigger),
            If(~self.trigger & old_trigger, self.pending.eq(1))
        ]

class EventManager(Module, AutoCSR):
    """Provide an IRQ and CSR registers for a set of event sources.

    Each event source is assigned one bit in each of those registers.

    Attributes
    ----------
    irq : Signal(), out
        A signal which is driven high whenever there is a pending and unmasked
        event.
        It is typically connected to an interrupt line of a CPU.

    status : CSR(n), read-only
        Contains the current level of the trigger line of
        ``EventSourceProcess`` and ``EventSourceLevel`` sources.
        It is always 0 for ``EventSourcePulse``

    pending : CSR(n), read-write
        Contains the currently asserted events. Writing 1 to the bit assigned
        to an event clears it.

    enable : CSR(n), read-write
        Defines which asserted events will cause the ``irq`` line to be
        asserted.
    """

    def __init__(self):
        self.irq = Signal()

    def do_finalize(self):
        sources_u = [v for k, v in xdir(self, True) if isinstance(v, _EventSource)]
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
        self.comb += self.irq.eq(reduce(or_, irqs))

    def __setattr__(self, name, value):
        object.__setattr__(self, name, value)
        if isinstance(value, _EventSource):
            if self.finalized:
                raise FinalizeError
            self.submodules += value

class SharedIRQ(Module):
    """Allow an IRQ signal to be shared between multiple EventManager objects."""

    def __init__(self, *event_managers):
        self.irq = Signal()
        self.comb += self.irq.eq(reduce(or_, [ev.irq for ev in event_managers]))

class GPIOIn(Module, AutoCSR):
    def __init__(self, signal):
        self._in = CSRStatus("in", len(signal), description="GPIO Input(s) Status.")
        self.specials += MultiReg(signal, self._in.status)

class GPIOOut(Module, AutoCSR):
    def __init__(self, signal):
        self._out = CSRStorage("out", len(signal), description="GPIO Output(s) Control.")
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
        Record.__init__(self, set_layout_parameters(_wishbone_layout,
            adr_width  = adr_width,
            data_width = data_width,
            sel_width  = data_width // 8))
        self.adr.reset_less   = True
        self.dat_w.reset_less = True
        self.dat_r.reset_less = True
        self.sel.reset_less   = True

    @staticmethod
    def like(other):
        return WishboneInterface(len(other.dat_w))

    def _do_transaction(self):
        yield self.cyc.eq(1)
        yield self.stb.eq(1)
        yield
        while not (yield self.ack):
            yield
        yield self.cyc.eq(0)
        yield self.stb.eq(0)

    def write(self, adr, dat, sel=None):
        if sel is None:
            sel = 2**len(self.sel) - 1
        yield self.adr.eq(adr)
        yield self.dat_w.eq(dat)
        yield self.sel.eq(sel)
        yield self.we.eq(1)
        yield from self._do_transaction()

    def read(self, adr):
        yield self.adr.eq(adr)
        yield self.we.eq(0)
        yield from self._do_transaction()
        return (yield self.dat_r)

    def get_ios(self, bus_name="wb"):
        subsignals = []
        for name, width, direction in self.layout:
            subsignals.append(Subsignal(name, Pins(width)))
        ios = [(bus_name , 0) + tuple(subsignals)]
        return ios

    def connect_to_pads(self, pads, mode="master"):
        assert mode in ["slave", "master"]
        r = []
        for name, width, direction in self.layout:
            sig  = getattr(self, name)
            pad  = getattr(pads, name)
            if mode == "master":
                if direction == DIR_M_TO_S:
                    r.append(pad.eq(sig))
                else:
                    r.append(sig.eq(pad))
            else:
                if direction == DIR_S_TO_M:
                    r.append(pad.eq(sig))
                else:
                    r.append(sig.eq(pad))
        return r

class WishboneTimeout(Module):
    def __init__(self, master, cycles):
        self.error = Signal()

        timer = WaitTimer(int(cycles))
        self.submodules += timer
        self.comb += [
            timer.wait.eq(master.stb & master.cyc & ~master.ack),
            If(timer.done,
                master.dat_r.eq((2**len(master.dat_w))-1),
                master.ack.eq(1),
                self.error.eq(1)
            )
        ]

class WishboneInterconnectPointToPoint(Module):
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
        slave_sel = Signal(ns)
        slave_sel_r = Signal(ns)

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
            master.ack.eq(reduce(or_, [slave[1].ack for slave in slaves])),
            master.err.eq(reduce(or_, [slave[1].err for slave in slaves]))
        ]

        # mux (1-hot) slave data return
        masked = [Replicate(slave_sel_r[i], len(master.dat_r)) & slaves[i][1].dat_r for i in range(ns)]
        self.comb += master.dat_r.eq(reduce(or_, masked))

class WishboneInterconnectShared(Module):
    def __init__(self, masters, slaves, register=False, timeout_cycles=1e6):
        shared = WishboneInterface()
        self.submodules.arbiter = WishboneArbiter(masters, shared)
        self.submodules.decoder = WishboneDecoder(shared, slaves, register)
        if timeout_cycles is not None:
            self.submodules.timeout = WishboneTimeout(shared, timeout_cycles)

class WishboneCrossbar(Module):
    def __init__(self, masters, slaves, register=False):
        matches, busses = zip(*slaves)
        access = [[WishboneInterface() for j in slaves] for i in masters]
        # decode each master into its access row
        for row, master in zip(access, masters):
            row = list(zip(matches, row))
            self.submodules += WishboneDecoder(master, row, register)
        # arbitrate each access column onto its slave
        for column, bus in zip(zip(*access), busses):
            self.submodules += WishboneArbiter(column, bus)

class WishboneDownConverter(Module):
    """
    This module splits Wishbone accesses from a master interface to a smaller slave interface.

    Writes:
        Writes from master are splitted N writes to the slave. Access is acked when the last
        access is acked by the slave.

    Reads:
        Read from master are splitted in N reads to the the slave. Read datas from
        the slave are cached before being presented concatenated on the last access.

    """
    def __init__(self, master, slave):
        dw_from = len(master.dat_r)
        dw_to   = len(slave.dat_w)
        ratio   = dw_from//dw_to

        skip    = Signal()
        counter = Signal(max=ratio)

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
            Case(counter, {i: slave.sel.eq(master.sel[i*dw_to//8:]) for i in range(ratio)}),
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
        self.comb += Case(counter, {i: slave.dat_w.eq(master.dat_w[i*dw_to:]) for i in range(ratio)})

        # Read Datapath
        dat_r = Signal(dw_from, reset_less=True)
        self.comb += master.dat_r.eq(Cat(dat_r[dw_to:], slave.dat_r))
        self.sync += If(slave.ack | skip, dat_r.eq(master.dat_r))

class WishboneConverter(Module):
    """
    This module is a wrapper for DownConverter and UpConverter.
    It should preferably be used rather than direct instantiations
    of specific converters.
    """
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
            assert(mem_or_size.width <= bus_data_width)
            self.mem = mem_or_size
        else:
            self.mem = Memory("mem", bus_data_width, mem_or_size // (bus_data_width // 8), init)
        if read_only is None:
            if hasattr(self.mem, "bus_read_only"):
                read_only = self.mem.bus_read_only
            else:
                read_only = False

        # memory
        port = self.mem.get_port(write_capable=not read_only, we_granularity=8,
            mode=READ_FIRST if read_only else WRITE_FIRST)
        self.specials += self.mem, port
        # generate write enable signal
        if not read_only:
            self.comb += [port.we[i].eq(self.bus.cyc & self.bus.stb & self.bus.we & self.bus.sel[i]) for i in range(bus_data_width//8)]
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
            # If no CSR bus provided, create it with default parameters.
            self.csr = CSRBusInterface()
        self.wishbone = bus_wishbone
        if self.wishbone is None:
            # If no Wishbone bus provided, create it with default parameters.
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

class WishboneCache(Module):
    """
    This module is a write-back wishbone cache that can be used as a L2 cache.
    Cachesize (in 32-bit words) is the size of the data store and must be a power of 2
    """
    def __init__(self, cachesize, master, slave, reverse=True):
        self.master = master
        self.slave = slave

        dw_from = len(master.dat_r)
        dw_to = len(slave.dat_r)
        if dw_to > dw_from and (dw_to % dw_from) != 0:
            raise ValueError("Slave data width must be a multiple of {dw}".format(dw=dw_from))
        if dw_to < dw_from and (dw_from % dw_to) != 0:
            raise ValueError("Master data width must be a multiple of {dw}".format(dw=dw_to))

        # Split address:
        # TAG | LINE NUMBER | LINE OFFSET
        offsetbits = log2_int(max(dw_to//dw_from, 1))
        addressbits = len(slave.adr) + offsetbits
        linebits = log2_int(cachesize) - offsetbits
        tagbits = addressbits - linebits
        wordbits = log2_int(max(dw_from//dw_to, 1))
        adr_offset, adr_line, adr_tag = split(master.adr, offsetbits, linebits, tagbits)
        word = Signal(wordbits) if wordbits else None

        # Data memory
        data_mem = Memory("data_mem", dw_to * 2**wordbits, 2**linebits)
        data_port = data_mem.get_port(write_capable=True, we_granularity=8)
        self.specials += data_mem, data_port

        write_from_slave = Signal()
        if adr_offset is None:
            adr_offset_r = None
        else:
            adr_offset_r = Signal(offsetbits, reset_less=True)
            self.sync += adr_offset_r.eq(adr_offset)

        self.comb += [
            data_port.adr.eq(adr_line),
            If(write_from_slave,
                displacer(slave.dat_r, word, data_port.dat_w),
                displacer(Replicate(1, dw_to // 8), word, data_port.we)
            ).Else(
                data_port.dat_w.eq(Replicate(master.dat_w, max(dw_to // dw_from, 1))),
                If(master.cyc & master.stb & master.we & master.ack,
                    displacer(master.sel, adr_offset, data_port.we, 2**offsetbits, reverse=reverse)
                )
            ),
            chooser(data_port.dat_r, word, slave.dat_w),
            slave.sel.eq(2**(dw_to // 8) - 1),
            chooser(data_port.dat_r, adr_offset_r, master.dat_r, reverse=reverse)
        ]

        # Tag memory
        tag_layout = [("tag", tagbits), ("dirty", 1)]
        tag_mem = Memory("tag_mem", layout_len(tag_layout), 2**linebits)
        tag_port = tag_mem.get_port(write_capable=True)
        self.specials += tag_mem, tag_port
        tag_do = Record(tag_layout)
        tag_di = Record(tag_layout)
        self.comb += [
            tag_do.raw_bits().eq(tag_port.dat_r),
            tag_port.dat_w.eq(tag_di.raw_bits())
        ]

        self.comb += [
            tag_port.adr.eq(adr_line),
            tag_di.tag.eq(adr_tag)
        ]
        if word is not None:
            self.comb += slave.adr.eq(Cat(word, adr_line, tag_do.tag))
        else:
            self.comb += slave.adr.eq(Cat(adr_line, tag_do.tag))

        # slave word computation, word_clr and word_inc will be simplified
        # at synthesis when wordbits=0
        word_clr = Signal()
        word_inc = Signal()
        if word is not None:
            self.sync += \
                If(word_clr,
                    word.eq(0),
                ).Elif(word_inc,
                    word.eq(word+1)
                )

        def word_is_last(word):
            if word is not None:
                return word == 2**wordbits-1
            else:
                return 1

        # Control FSM
        self.submodules.fsm = fsm = FSM(reset_state="IDLE")
        fsm.act("IDLE",
            If(master.cyc & master.stb,
                NextState("TEST_HIT")
            )
        )
        fsm.act("TEST_HIT",
            word_clr.eq(1),
            If(tag_do.tag == adr_tag,
                master.ack.eq(1),
                If(master.we,
                    tag_di.dirty.eq(1),
                    tag_port.we.eq(1)
                ),
                NextState("IDLE")
            ).Else(
                If(tag_do.dirty,
                    NextState("EVICT")
                ).Else(
                    # Write the tag first to set the slave address
                    tag_port.we.eq(1),
                    word_clr.eq(1),
                    NextState("REFILL")
                )
            )
        )

        fsm.act("EVICT",
            slave.stb.eq(1),
            slave.cyc.eq(1),
            slave.we.eq(1),
            If(slave.ack,
                word_inc.eq(1),
                 If(word_is_last(word),
                    # Write the tag first to set the slave address
                    tag_port.we.eq(1),
                    word_clr.eq(1),
                    NextState("REFILL")
                )
            )
        )
        fsm.act("REFILL",
            slave.stb.eq(1),
            slave.cyc.eq(1),
            slave.we.eq(0),
            If(slave.ack,
                write_from_slave.eq(1),
                word_inc.eq(1),
                If(word_is_last(word),
                    NextState("TEST_HIT"),
                ).Else(
                    NextState("REFILL")
                )
            )
        )

_reserved_keywords = {
    "always", "and", "assign", "automatic", "begin", "buf", "bufif0", "bufif1",
    "case", "casex", "casez", "cell", "cmos", "config", "deassign", "default",
    "defparam", "design", "disable", "edge", "else", "end", "endcase",
    "endconfig", "endfunction", "endgenerate", "endmodule", "endprimitive",
    "endspecify", "endtable", "endtask", "event", "for", "force", "forever",
    "fork", "function", "generate", "genvar", "highz0", "highz1", "if",
    "ifnone", "incdir", "include", "initial", "inout", "input",
    "instance", "integer", "join", "large", "liblist", "library", "localparam",
    "macromodule", "medium", "module", "nand", "negedge", "nmos", "nor",
    "noshowcancelled", "not", "notif0", "notif1", "or", "output", "parameter",
    "pmos", "posedge", "primitive", "pull0", "pull1" "pulldown",
    "pullup", "pulsestyle_onevent", "pulsestyle_ondetect", "remos", "real",
    "realtime", "reg", "release", "repeat", "rnmos", "rpmos", "rtran",
    "rtranif0", "rtranif1", "scalared", "showcancelled", "signed", "small",
    "specify", "specparam", "strong0", "strong1", "supply0", "supply1",
    "table", "task", "time", "tran", "tranif0", "tranif1", "tri", "tri0",
    "tri1", "triand", "trior", "trireg", "unsigned", "use", "vectored", "wait",
    "wand", "weak0", "weak1", "while", "wire", "wor","xnor", "xor", "do"
}

def _printsig(ns, s):
    if s.signed:
        n = "signed "
    else:
        n = ""
    if len(s) > 1:
        n += "[" + str(len(s)-1) + ":0] "
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
            assert node.op == "m"
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
            sr = "[" + str(node.stop-1) + ":" + str(node.start) + "]"
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

def _printheader(f, ios, name, ns, attr_translate, reg_initialization):
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
            if reg_initialization:
                r += "reg " + _printsig(ns, sig) + " = " + _printexpr(ns, sig.reset)[0] + ";\n"
            else:
                r += "reg " + _printsig(ns, sig) + ";\n"
    r += "\n"
    return r

def _printcomb_simulation(f, ns, display_run, dummy_signal, blocking_assign):
    r = ""
    if f.comb:
        if dummy_signal:
            # Generate a dummy event to get the simulator to run the combinatorial process once at the beginning.
            syn_off = "// synthesis translate_off\n"
            syn_on = "// synthesis translate_on\n"
            dummy_s = Signal(name_override="dummy_s")
            r += syn_off
            r += "reg " + _printsig(ns, dummy_s) + ";\n"
            r += "initial " + ns.get_name(dummy_s) + " <= 1'd0;\n"
            r += syn_on

        target_stmt_map = defaultdict(list)

        for statement in flat_iteration(f.comb):
            targets = list_targets(statement)
            for t in targets:
                target_stmt_map[t].append(statement)

        groups = group_by_targets(f.comb)

        for n, (t, stmts) in enumerate(target_stmt_map.items()):
            assert isinstance(t, Signal)
            if len(stmts) == 1 and isinstance(stmts[0], _Assign):
                r += "assign " + _printnode(ns, _AT_BLOCKING, 0, stmts[0])
            else:
                if dummy_signal:
                    dummy_d = Signal(name_override="dummy_d")
                    r += "\n" + syn_off
                    r += "reg " + _printsig(ns, dummy_d) + ";\n"
                    r += syn_on

                r += "always @(*) begin\n"
                if display_run:
                    r += "\t$display(\"Running comb block #" + str(n) + "\");\n"
                if blocking_assign:
                    r += "\t" + ns.get_name(t) + " = " + _printexpr(ns, t.reset)[0] + ";\n"
                    r += _printnode(ns, _AT_BLOCKING, 1, stmts, t)
                else:
                    r += "\t" + ns.get_name(t) + " <= " + _printexpr(ns, t.reset)[0] + ";\n"
                    r += _printnode(ns, _AT_NONBLOCKING, 1, stmts, t)
                if dummy_signal:
                    r += syn_off
                    r += "\t" + ns.get_name(dummy_d) + " = " + ns.get_name(dummy_s) + ";\n"
                    r += syn_on
                r += "end\n"
    r += "\n"
    return r

def _printcomb_regular(f, ns, blocking_assign):
    r = ""
    if f.comb:
        groups = group_by_targets(f.comb)

        for n, g in enumerate(groups):
            if len(g[1]) == 1 and isinstance(g[1][0], _Assign):
                r += "assign " + _printnode(ns, _AT_BLOCKING, 0, g[1][0])
            else:
                r += "always @(*) begin\n"
                if blocking_assign:
                    for t in g[0]:
                        r += "\t" + ns.get_name(t) + " = " + _printexpr(ns, t.reset)[0] + ";\n"
                    r += _printnode(ns, _AT_BLOCKING, 1, g[1])
                else:
                    for t in g[0]:
                        r += "\t" + ns.get_name(t) + " <= " + _printexpr(ns, t.reset)[0] + ";\n"
                    r += _printnode(ns, _AT_NONBLOCKING, 1, g[1])
                r += "end\n"
    r += "\n"
    return r

def _printsync(f, ns):
    r = ""
    for k, v in sorted(f.sync.items(), key=itemgetter(0)):
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

class DummyAttrTranslate:
    def __getitem__(self, k):
        return (k, "true")

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

    def __str__(self):
        r = self.main_source + "\n"
        for filename, content in sorted(self.data_files.items(), key=itemgetter(0)):
            r += filename + ":\n" + content
        return r

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
    def __init__(self, pnd, reserved_keywords=set()):
        self.counts = {k: 1 for k in reserved_keywords}
        self.sigs = {}
        self.pnd = pnd
        self.clock_domains = dict()

    def get_name(self, sig):
        if isinstance(sig, ClockSignal):
            sig = self.clock_domains[sig.cd].clk
        if isinstance(sig, ResetSignal):
            sig = self.clock_domains[sig.cd].rst
            if sig is None:
                raise ValueError("Attempted to obtain name of non-existent reset signal of domain "+sig.cd)

        if sig.name_override is not None:
            sig_name = sig.name_override
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

def build_namespace(signals, reserved_keywords=set()):
    pnd = _build_pnd(signals)
    ns = Namespace(pnd, reserved_keywords)
    # register signals with name_override
    swno = {signal for signal in signals if signal.name_override is not None}
    for signal in sorted(swno, key=lambda x: x.duid):
        ns.get_name(signal)
    return ns

def convert(f, ios=None, name="top",
  special_overrides=dict(),
  attr_translate=DummyAttrTranslate(),
  create_clock_domains=True,
  display_run=False,
  reg_initialization=True,
  dummy_signal=True,
  blocking_assign=False,
  regular_comb=True):
    r = ConvOutput()
    if not isinstance(f, _Fragment):
        f = f.get_fragment()
    if ios is None:
        ios = set()

    for cd_name in sorted(list_clock_domains(f)):
        try:
            f.clock_domains[cd_name]
        except KeyError:
            if create_clock_domains:
                cd = ClockDomain(cd_name)
                f.clock_domains.append(cd)
                ios |= {cd.clk, cd.rst}
            else:
                print("available clock domains:")
                for f in f.clock_domains:
                    print(f.name)
                raise KeyError("Unresolved clock domain: '" + cd_name + "'")

    f = lower_complex_slices(f)
    insert_resets(f)
    f = lower_basics(f)
    f, lowered_specials = lower_specials(special_overrides, f)
    f = lower_basics(f)

    ns = build_namespace(list_signals(f) | list_special_ios(f, True, True, True) | ios, _reserved_keywords)
    ns.clock_domains = f.clock_domains
    r.ns = ns

    src = ""
    src += _printheader(f, ios, name, ns, attr_translate, reg_initialization=reg_initialization)
    if regular_comb:
        src += _printcomb_regular(f, ns, blocking_assign=blocking_assign)
    else:
        src += _printcomb_simulation(f, ns, display_run=display_run, dummy_signal=dummy_signal, blocking_assign=blocking_assign)
    src += _printsync(f, ns)
    src += _printspecials(special_overrides, f.specials - lowered_specials,
        ns, r.add_data_file, attr_translate)
    src += "endmodule\n"
    r.set_main_source(src)

    return r

burst_lengths = {
    "SDR":   1,
    "DDR":   4,
    "LPDDR": 4,
    "DDR2":  4,
    "DDR3":  8,
    "DDR4":  8
}

def get_cl_cw(memtype, tck):
    f_to_cl_cwl = OrderedDict()
    if memtype == "DDR2":
        f_to_cl_cwl[400e6]  = (3, 2)
        f_to_cl_cwl[533e6]  = (4, 3)
        f_to_cl_cwl[677e6]  = (5, 4)
        f_to_cl_cwl[800e6]  = (6, 5)
        f_to_cl_cwl[1066e6] = (7, 5)
    elif memtype == "DDR3":
        f_to_cl_cwl[800e6]  = ( 6, 5)
        f_to_cl_cwl[1066e6] = ( 7, 6)
        f_to_cl_cwl[1333e6] = (10, 7)
        f_to_cl_cwl[1600e6] = (11, 8)
    elif memtype == "DDR4":
        f_to_cl_cwl[1600e6] = (11,  9)
    else:
        raise ValueError
    for f, (cl, cwl) in f_to_cl_cwl.items():
        if tck >= 2/f:
            return cl, cwl
    raise ValueError

def get_sys_latency(nphases, cas_latency):
    return math.ceil(cas_latency/nphases)

def get_sys_phases(nphases, sys_latency, cas_latency):
    dat_phase = sys_latency*nphases - cas_latency
    cmd_phase = (dat_phase - 1)%nphases
    return cmd_phase, dat_phase

class PHYPadsReducer:
    """PHY Pads Reducer

    Reduce DRAM pads to only use specific modules.

    For testing purposes, we often need to use only some of the DRAM modules. PHYPadsReducer allows
    selecting specific modules and avoid re-definining dram pins in the Platform for this.
    """
    def __init__(self, pads, modules):
        self.pads    = pads
        self.modules = modules

    def __getattr__(self, name):
        if name in ["dq"]:
            return Array([getattr(self.pads, name)[8*i + j]
                for i in self.modules
                for j in range(8)])
        if name in ["dm", "dqs", "dqs_p", "dqs_n"]:
            return Array([getattr(self.pads, name)[i] for i in self.modules])
        else:
            return getattr(self.pads, name)

class PHYPadsCombiner:
    """PHY Pads Combiner

    Combine DRAM pads from fully dissociated chips in a unique DRAM pads structure.

    Most generally, DRAM chips are sharing command/address lines between chips (using a fly-by
    topology since DDR3). On some boards, the DRAM chips are using separate command/address lines
    and this combiner can be used to re-create a single pads structure (that will be compatible with
    LiteDRAM's PHYs) to create a single DRAM controller from multiple fully dissociated DRAMs chips.
    """
    def __init__(self, pads):
        if not isinstance(pads, list):
            self.groups = [pads]
        else:
            self.groups = pads
        self.sel = 0

    def sel_group(self, n):
        self.sel = n

    def __getattr__(self, name):
        if name in ["dm", "dq", "dqs", "dqs_p", "dqs_n"]:
            return Array([getattr(self.groups[j], name)[i]
                for i in range(len(getattr(self.groups[0], name)))
                for j in range(len(self.groups))])
        else:
            return getattr(self.groups[self.sel], name)

class BitSlip(Module):
    def __init__(self, dw, rst=None, slp=None, cycles=1):
        self.i = Signal(dw)
        self.o = Signal(dw)
        self.rst = Signal() if rst is None else rst
        self.slp = Signal() if slp is None else slp

        value = Signal(max=cycles*dw)
        self.sync += If(self.slp, value.eq(value + 1))
        self.sync += If(self.rst, value.eq(0))

        r = Signal((cycles+1)*dw, reset_less=True)
        self.sync += r.eq(Cat(r[dw:], self.i))
        cases = {}
        for i in range(cycles*dw):
            cases[i] = self.o.eq(r[i:dw+i])
        self.comb += Case(value, cases)

class DQSPattern(Module):
    def __init__(self, preamble=None, postamble=None, wlevel_en=0, wlevel_strobe=0, register=False):
        self.preamble  = Signal() if preamble  is None else preamble
        self.postamble = Signal() if postamble is None else postamble
        self.o = Signal(8)

        self.comb += [
            self.o.eq(0b01010101),
            If(self.preamble,
                self.o.eq(0b00010101)
            ),
            If(self.postamble,
                self.o.eq(0b01010100)
            ),
            If(wlevel_en,
                self.o.eq(0b00000000),
                If(wlevel_strobe,
                    self.o.eq(0b00000001)
                )
            )
        ]
        if register:
            o = Signal.like(self.o)
            self.sync += o.eq(self.o)
            self.o = o

class Settings:
    def set_attributes(self, attributes):
        for k, v in attributes.items():
            setattr(self, k, v)

class PhySettings(Settings):
    def __init__(self, phytype, memtype, databits, dfi_databits,
                 nphases,
                 rdphase, wrphase,
                 rdcmdphase, wrcmdphase,
                 cl, read_latency, write_latency, nranks=1, cwl=None):
        self.set_attributes(locals())
        self.cwl = cl if cwl is None else cwl
        self.is_rdimm = False

    # Optional DDR3/DDR4 electrical settings:
    # rtt_nom: Non-Writes on-die termination impedance
    # rtt_wr: Writes on-die termination impedance
    # ron: Output driver impedance
    def add_electrical_settings(self, rtt_nom, rtt_wr, ron):
        assert self.memtype in ["DDR3", "DDR4"]
        self.set_attributes(locals())

    # Optional RDIMM configuration
    def set_rdimm(self, tck, rcd_pll_bypass, rcd_ca_cs_drive, rcd_odt_cke_drive, rcd_clk_drive):
        assert self.memtype == "DDR4"
        self.is_rdimm = True
        self.set_attributes(locals())

class GeomSettings(Settings):
    def __init__(self, bankbits, rowbits, colbits):
        self.set_attributes(locals())
        self.addressbits = max(rowbits, colbits)

class TimingSettings(Settings):
    def __init__(self, tRP, tRCD, tWR, tWTR, tREFI, tRFC, tFAW, tCCD, tRRD, tRC, tRAS, tZQCS):
        self.set_attributes(locals())

def cmd_layout(address_width):
    return [
        ("valid",            1, DIR_M_TO_S),
        ("ready",            1, DIR_S_TO_M),
        ("we",               1, DIR_M_TO_S),
        ("addr", address_width, DIR_M_TO_S),
        ("lock",             1, DIR_S_TO_M), # only used internally

        ("wdata_ready",      1, DIR_S_TO_M),
        ("rdata_valid",      1, DIR_S_TO_M)
    ]

def data_layout(data_width):
    return [
        ("wdata",       data_width, DIR_M_TO_S),
        ("wdata_we", data_width//8, DIR_M_TO_S),
        ("rdata",       data_width, DIR_S_TO_M)
    ]

def cmd_description(address_width):
    return [
        ("we",   1),
        ("addr", address_width)
    ]

def wdata_description(data_width):
    return [
        ("data", data_width),
        ("we",   data_width//8)
    ]

def rdata_description(data_width):
    return [("data", data_width)]

def cmd_request_layout(a, ba):
    return [
        ("a",     a),
        ("ba",   ba),
        ("cas",   1),
        ("ras",   1),
        ("we",    1)
    ]

def cmd_request_rw_layout(a, ba):
    return cmd_request_layout(a, ba) + [
        ("is_cmd", 1),
        ("is_read", 1),
        ("is_write", 1)
    ]

class LiteDRAMInterface(Record):
    def __init__(self, address_align, settings):
        rankbits = log2_int(settings.phy.nranks)
        self.address_align = address_align
        self.address_width = settings.geom.rowbits + settings.geom.colbits + rankbits - address_align
        self.data_width    = settings.phy.dfi_databits*settings.phy.nphases
        self.nbanks   = settings.phy.nranks*(2**settings.geom.bankbits)
        self.nranks   = settings.phy.nranks
        self.settings = settings

        layout = [("bank"+str(i), cmd_layout(self.address_width)) for i in range(self.nbanks)]
        layout += data_layout(self.data_width)
        Record.__init__(self, layout)

class LiteDRAMNativePort(Settings):
    def __init__(self, mode, address_width, data_width, clock_domain="sys", id=0):
        self.set_attributes(locals())

        self.lock = Signal()

        self.cmd   = Endpoint(cmd_description(address_width))
        self.wdata = Endpoint(wdata_description(data_width))
        self.rdata = Endpoint(rdata_description(data_width))

        self.flush = Signal()

        # retro-compatibility # FIXME: remove
        self.aw = self.address_width
        self.dw = self.data_width
        self.cd = self.clock_domain

    def get_bank_address(self, bank_bits, cba_shift):
        cba_upper = cba_shift + bank_bits
        return self.cmd.addr[cba_shift:cba_upper]

    def get_row_column_address(self, bank_bits, rca_bits, cba_shift):
        cba_upper = cba_shift + bank_bits
        if cba_shift < rca_bits:
            if cba_shift:
                return Cat(self.cmd.addr[:cba_shift], self.cmd.addr[cba_upper:])
            else:
                return self.cmd.addr[cba_upper:]
        else:
            return self.cmd.addr[:cba_shift]

class LiteDRAMNativeWritePort(LiteDRAMNativePort):
    def __init__(self, *args, **kwargs):
        LiteDRAMNativePort.__init__(self, "write", *args, **kwargs)

class LiteDRAMNativeReadPort(LiteDRAMNativePort):
    def __init__(self, *args, **kwargs):
        LiteDRAMNativePort.__init__(self, "read", *args, **kwargs)

class tXXDController(Module):
    def __init__(self, txxd):
        self.valid = valid = Signal()
        self.ready = ready = Signal(reset=txxd is None)
        ready.attr.add("no_retiming")

        if txxd is not None:
            count = Signal(max=max(txxd, 2))
            self.sync += \
                If(valid,
                    count.eq(txxd - 1),
                    If((txxd - 1) == 0,
                        ready.eq(1)
                    ).Else(
                        ready.eq(0)
                    )
                ).Elif(~ready,
                    count.eq(count - 1),
                    If(count == 1,
                        ready.eq(1)
                    )
                )

class tFAWController(Module):
    def __init__(self, tfaw):
        self.valid = valid = Signal()
        self.ready = ready = Signal(reset=1)
        ready.attr.add("no_retiming")

        if tfaw is not None:
            count  = Signal(max=max(tfaw, 2))
            window = Signal(tfaw)
            self.sync += window.eq(Cat(valid, window))
            self.comb += count.eq(reduce(operator.add, [window[i] for i in range(tfaw)]))
            self.sync += \
                If(count < 4,
                    If(count == 3,
                        ready.eq(~valid)
                    ).Else(
                        ready.eq(1)
                    )
                )

def phase_cmd_description(addressbits, bankbits, nranks):
    return [
        ("address", addressbits, DIR_M_TO_S),
        ("bank",       bankbits, DIR_M_TO_S),
        ("cas_n",             1, DIR_M_TO_S),
        ("cs_n",         nranks, DIR_M_TO_S),
        ("ras_n",             1, DIR_M_TO_S),
        ("we_n",              1, DIR_M_TO_S),
        ("cke",          nranks, DIR_M_TO_S),
        ("odt",          nranks, DIR_M_TO_S),
        ("reset_n",           1, DIR_M_TO_S),
        ("act_n",             1, DIR_M_TO_S)
    ]

def phase_wrdata_description(databits):
    return [
        ("wrdata",         databits, DIR_M_TO_S),
        ("wrdata_en",             1, DIR_M_TO_S),
        ("wrdata_mask", databits//8, DIR_M_TO_S)
    ]

def phase_rddata_description(databits):
    return [
        ("rddata_en",           1, DIR_M_TO_S),
        ("rddata",       databits, DIR_S_TO_M),
        ("rddata_valid",        1, DIR_S_TO_M)
    ]

def phase_description(addressbits, bankbits, nranks, databits):
    r = phase_cmd_description(addressbits, bankbits, nranks)
    r += phase_wrdata_description(databits)
    r += phase_rddata_description(databits)
    return r

class DFIInterface(Record):
    def __init__(self, addressbits, bankbits, nranks, databits, nphases=1):
        layout = [("p"+str(i), phase_description(addressbits, bankbits, nranks, databits)) for i in range(nphases)]
        Record.__init__(self, layout)
        self.phases = [getattr(self, "p"+str(i)) for i in range(nphases)]
        for p in self.phases:
            p.cas_n.reset = 1
            p.cs_n.reset = (2**nranks-1)
            p.ras_n.reset = 1
            p.we_n.reset = 1
            p.act_n.reset = 1

    # Returns pairs (DFI-mandated signal name, Eigen signal object)
    def get_standard_names(self, m2s=True, s2m=True):
        r = []
        add_suffix = len(self.phases) > 1
        for n, phase in enumerate(self.phases):
            for field, size, direction in phase.layout:
                if (m2s and direction == DIR_M_TO_S) or (s2m and direction == DIR_S_TO_M):
                    if add_suffix:
                        if direction == DIR_M_TO_S:
                            suffix = "_p" + str(n)
                        else:
                            suffix = "_w" + str(n)
                    else:
                        suffix = ""
                    r.append(("dfi_" + field + suffix, getattr(phase, field)))
        return r

class Interconnect(Module):
    def __init__(self, master, slave):
        self.comb += master.connect(slave)

# 1:2 frequency-ratio DDR3 PHY for Lattice's ECP5
# DDR3: 800 MT/s

class ECP5DDRPHYInit(Module):
    def __init__(self):
        self.pause = Signal()
        self.stop  = Signal()
        self.delay = Signal()
        self.reset = Signal()

        new_lock = Signal()
        update   = Signal()
        stop     = Signal()
        freeze   = Signal()
        pause    = Signal()
        reset    = Signal()

        # DDRDLLA instance
        _lock = Signal()
        delay = Signal()
        self.specials += Instance("DDRDLLA",
            i_RST      = ResetSignal("init"),
            i_CLK      = ClockSignal("sys2x"),
            i_UDDCNTLN = ~update,
            i_FREEZE   = freeze,
            o_DDRDEL   = delay,
            o_LOCK     = _lock
        )
        lock   = Signal()
        lock_d = Signal()
        self.specials += MultiReg(_lock, lock, "init")
        self.sync.init += lock_d.eq(lock)
        self.comb += new_lock.eq(lock & ~lock_d)

        # DDRDLLA/DDQBUFM/ECLK initialization sequence
        t = 8 # in cycles
        self.sync.init += [
            # Wait DDRDLLA Lock
            timeline(new_lock, [
                (1*t,  [freeze.eq(1)]), # Freeze DDRDLLA
                (2*t,  [stop.eq(1)]),   # Stop ECLK domain
                (3*t,  [reset.eq(1)]),  # Reset ECLK domain
                (4*t,  [reset.eq(0)]),  # Release ECLK domain reset
                (5*t,  [stop.eq(0)]),   # Release ECLK domain stop
                (6*t,  [freeze.eq(0)]), # Release DDRDLLA freeze
                (7*t,  [pause.eq(1)]),  # Pause DQSBUFM
                (8*t,  [update.eq(1)]), # Update DDRDLLA
                (9*t,  [update.eq(0)]), # Release DDRDMMA update
                (10*t, [pause.eq(0)]),  # Release DQSBUFM pause
            ])
        ]

        self.comb += [
            self.pause.eq(pause),
            self.stop.eq(stop),
            self.delay.eq(delay),
            self.reset.eq(reset),
        ]

class ECP5DDRPHY(Module, AutoCSR):
    def __init__(self, pads, sys_clk_freq=100e6):
        pads        = PHYPadsCombiner(pads)
        memtype     = "DDR3"
        tck         = 2/(2*2*sys_clk_freq)
        addressbits = len(pads.a)
        bankbits    = len(pads.ba)
        nranks      = 1 if not hasattr(pads, "cs_n") else len(pads.cs_n)
        databits    = len(pads.dq)
        nphases     = 2
        assert databits%8 == 0

        # Init
        self.submodules.init = ECP5DDRPHYInit()

        # Parameters
        cl, cwl         = get_cl_cw(memtype, tck)
        cl_sys_latency  = get_sys_latency(nphases, cl)
        cwl_sys_latency = get_sys_latency(nphases, cwl)

        # Registers
        self._dly_sel = CSRStorage("dly_sel", databits // 8)

        self._rdly_dq_rst         = CSR("rdly_dq_rst")
        self._rdly_dq_inc         = CSR("rdly_dq_inc")
        self._rdly_dq_bitslip_rst = CSR("rdly_dq_bitslip_rst")
        self._rdly_dq_bitslip     = CSR("rdly_dq_bitslip")

        self._burstdet_clr  = CSR("burstdet_clr")
        self._burstdet_seen = CSRStatus("burstdet_seen", databits // 8)

        # Observation
        self.datavalid = Signal(databits // 8)

        # PHY settings
        rdcmdphase, rdphase = get_sys_phases(nphases, cl_sys_latency, cl)
        wrcmdphase, wrphase = get_sys_phases(nphases, cwl_sys_latency, cwl)
        self.settings = PhySettings(
            phytype       = "ECP5DDRPHY",
            memtype       = memtype,
            databits      = databits,
            dfi_databits  = 4 * databits,
            nranks        = nranks,
            nphases       = nphases,
            rdphase       = rdphase,
            wrphase       = wrphase,
            rdcmdphase    = rdcmdphase,
            wrcmdphase    = wrcmdphase,
            cl            = cl,
            cwl           = cwl,
            read_latency  = 2 + cl_sys_latency + 2 + log2_int(4 // nphases) + 5,
            write_latency = cwl_sys_latency
        )

        # DFI Interface
        self.dfi = dfi = DFIInterface(addressbits, bankbits, nranks, 4 * databits, 4)

        bl8_chunk = Signal()

        # Iterate on pads groups
        for pads_group in range(len(pads.groups)):
            pads.sel_group(pads_group)

            # Clock
            for i in range(len(pads.clk_p)):
                sd_clk_se = Signal()
                self.specials += Instance("ODDRX2F",
                    i_RST  = ResetSignal("sys"),
                    i_SCLK = ClockSignal("sys"),
                    i_ECLK = ClockSignal("sys2x"),
                    i_D0   = 0,
                    i_D1   = 1,
                    i_D2   = 0,
                    i_D3   = 1,
                    o_Q    = pads.clk_p[i]
                )

            # Addresses and Commands
            for i in range(addressbits):
                self.specials += Instance("ODDRX2F",
                    i_RST  = ResetSignal("sys"),
                    i_SCLK = ClockSignal("sys"),
                    i_ECLK = ClockSignal("sys2x"),
                    i_D0   = dfi.phases[0].address[i],
                    i_D1   = dfi.phases[0].address[i],
                    i_D2   = dfi.phases[1].address[i],
                    i_D3   = dfi.phases[1].address[i],
                    o_Q    = pads.a[i]
                )
            for i in range(bankbits):
                self.specials += Instance("ODDRX2F",
                    i_RST  = ResetSignal("sys"),
                    i_SCLK = ClockSignal("sys"),
                    i_ECLK = ClockSignal("sys2x"),
                    i_D0   = dfi.phases[0].bank[i],
                    i_D1   = dfi.phases[0].bank[i],
                    i_D2   = dfi.phases[1].bank[i],
                    i_D3   = dfi.phases[1].bank[i],
                    o_Q    = pads.ba[i]
                )
            controls = ["ras_n", "cas_n", "we_n", "cke", "odt"]
            if hasattr(pads, "reset_n"):
                controls.append("reset_n")
            if hasattr(pads, "cs_n"):
                controls.append("cs_n")
            for name in controls:
                for i in range(len(getattr(pads, name))):
                    self.specials += Instance("ODDRX2F",
                        i_RST  = ResetSignal("sys"),
                        i_SCLK = ClockSignal("sys"),
                        i_ECLK = ClockSignal("sys2x"),
                        i_D0   = getattr(dfi.phases[0], name)[i],
                        i_D1   = getattr(dfi.phases[0], name)[i],
                        i_D2   = getattr(dfi.phases[1], name)[i],
                        i_D3   = getattr(dfi.phases[1], name)[i],
                        o_Q    = getattr(pads, name)[i]
                    )

        # DQ
        dq_oe         = Signal()
        dqs_re        = Signal()
        dqs_oe        = Signal()
        dqs_postamble = Signal()
        dqs_preamble  = Signal()
        for i in range(databits//8):
            # DQSBUFM
            dqs_i   = Signal()
            dqsr90  = Signal()
            dqsw270 = Signal()
            dqsw    = Signal()
            rdpntr  = Signal(3)
            wrpntr  = Signal(3)
            rdly    = Signal(7)
            burstdet  = Signal()
            self.sync += [
                If(self._dly_sel.storage[i] & self._rdly_dq_rst.re, rdly.eq(0)),
                If(self._dly_sel.storage[i] & self._rdly_dq_inc.re, rdly.eq(rdly + 1))
            ]
            self.specials += Instance("DQSBUFM",
                p_DQS_LI_DEL_ADJ = "MINUS",
                p_DQS_LI_DEL_VAL = 1,
                p_DQS_LO_DEL_ADJ = "MINUS",
                p_DQS_LO_DEL_VAL = 4,
                # Clocks / Reset
                i_RST            = ResetSignal("sys"),
                i_SCLK           = ClockSignal("sys"),
                i_ECLK           = ClockSignal("sys2x"),
                i_DDRDEL         = self.init.delay,
                i_PAUSE          = self.init.pause | self._dly_sel.storage[i],

                # Control
                # Assert LOADNs to use DDRDEL control
                i_RDLOADN        = 0,
                i_RDMOVE         = 0,
                i_RDDIRECTION    = 1,
                i_WRLOADN        = 0,
                i_WRMOVE         = 0,
                i_WRDIRECTION    = 1,

                # Reads (generate shifted DQS clock for reads)
                i_READ0          = dqs_re,
                i_READ1          = dqs_re,
                i_READCLKSEL0    = rdly[0],
                i_READCLKSEL1    = rdly[1],
                i_READCLKSEL2    = rdly[2],
                i_DQSI           = dqs_i,
                o_DQSR90         = dqsr90,
                o_RDPNTR0        = rdpntr[0],
                o_RDPNTR1        = rdpntr[1],
                o_RDPNTR2        = rdpntr[2],
                o_WRPNTR0        = wrpntr[0],
                o_WRPNTR1        = wrpntr[1],
                o_WRPNTR2        = wrpntr[2],
                o_DATAVALID      = self.datavalid[i],
                o_BURSTDET       = burstdet,

                # Writes (generate shifted ECLK clock for writes)
                o_DQSW270        = dqsw270,
                o_DQSW           = dqsw
            )
            burstdet_d = Signal()
            self.sync += [
                burstdet_d.eq(burstdet),
                If(self._burstdet_clr.re,  self._burstdet_seen.status[i].eq(0)),
                If(burstdet & ~burstdet_d, self._burstdet_seen.status[i].eq(1)),
            ]

            # DQS and DM
            dm_o_data       = Signal(8)
            dm_o_data_d     = Signal(8)
            dm_o_data_muxed = Signal(4)
            self.comb += dm_o_data.eq(Cat(
                dfi.phases[0].wrdata_mask[0*databits//8+i],
                dfi.phases[0].wrdata_mask[1*databits//8+i],
                dfi.phases[0].wrdata_mask[2*databits//8+i],
                dfi.phases[0].wrdata_mask[3*databits//8+i],

                dfi.phases[1].wrdata_mask[0*databits//8+i],
                dfi.phases[1].wrdata_mask[1*databits//8+i],
                dfi.phases[1].wrdata_mask[2*databits//8+i],
                dfi.phases[1].wrdata_mask[3*databits//8+i]),
            )
            self.sync += dm_o_data_d.eq(dm_o_data)
            dm_bl8_cases = {}
            dm_bl8_cases[0] = dm_o_data_muxed.eq(dm_o_data[:4])
            dm_bl8_cases[1] = dm_o_data_muxed.eq(dm_o_data_d[4:])
            self.sync += Case(bl8_chunk, dm_bl8_cases)
            self.specials += Instance("ODDRX2DQA",
                i_RST     = ResetSignal("sys"),
                i_SCLK    = ClockSignal("sys"),
                i_ECLK    = ClockSignal("sys2x"),
                i_DQSW270 = dqsw270,
                i_D0      = dm_o_data_muxed[0],
                i_D1      = dm_o_data_muxed[1],
                i_D2      = dm_o_data_muxed[2],
                i_D3      = dm_o_data_muxed[3],
                o_Q       = pads.dm[i]
            )

            dqs      = Signal()
            dqs_oe_n = Signal()
            self.specials += [
                Instance("ODDRX2DQSB",
                    i_RST  = ResetSignal("sys"),
                    i_SCLK = ClockSignal("sys"),
                    i_ECLK = ClockSignal("sys2x"),
                    i_DQSW = dqsw,
                    i_D0   = 0,
                    i_D1   = 1,
                    i_D2   = 0,
                    i_D3   = 1,
                    o_Q    = dqs
                ),
                Instance("TSHX2DQSA",
                    i_RST  = ResetSignal("sys"),
                    i_SCLK = ClockSignal("sys"),
                    i_ECLK = ClockSignal("sys2x"),
                    i_DQSW = dqsw,
                    i_T0   = ~(dqs_oe | dqs_postamble),
                    i_T1   = ~(dqs_oe | dqs_preamble),
                    o_Q    = dqs_oe_n
                ),
                Tristate(pads.dqs_p[i], dqs, ~dqs_oe_n, dqs_i)
            ]

            for j in range(8*i, 8*(i+1)):
                dq_o            = Signal()
                dq_i            = Signal()
                dq_oe_n         = Signal()
                dq_i_delayed    = Signal()
                dq_i_data       = Signal(4)
                dq_o_data       = Signal(8)
                dq_o_data_d     = Signal(8)
                dq_o_data_muxed = Signal(4)
                self.comb += dq_o_data.eq(Cat(
                    dfi.phases[0].wrdata[0*databits+j],
                    dfi.phases[0].wrdata[1*databits+j],
                    dfi.phases[0].wrdata[2*databits+j],
                    dfi.phases[0].wrdata[3*databits+j],

                    dfi.phases[1].wrdata[0*databits+j],
                    dfi.phases[1].wrdata[1*databits+j],
                    dfi.phases[1].wrdata[2*databits+j],
                    dfi.phases[1].wrdata[3*databits+j])
                )
                self.sync += dq_o_data_d.eq(dq_o_data)
                dq_bl8_cases = {}
                dq_bl8_cases[0] = dq_o_data_muxed.eq(dq_o_data[:4])
                dq_bl8_cases[1] = dq_o_data_muxed.eq(dq_o_data_d[4:])
                self.sync += Case(bl8_chunk, dq_bl8_cases)
                self.specials += [
                    Instance("ODDRX2DQA",
                        i_RST     = ResetSignal("sys"),
                        i_SCLK    = ClockSignal("sys"),
                        i_ECLK    = ClockSignal("sys2x"),
                        i_DQSW270 = dqsw270,
                        i_D0      = dq_o_data_muxed[0],
                        i_D1      = dq_o_data_muxed[1],
                        i_D2      = dq_o_data_muxed[2],
                        i_D3      = dq_o_data_muxed[3],
                        o_Q       = dq_o
                    ),
                    Instance("DELAYF",
                        p_DEL_MODE  = "DQS_ALIGNED_X2",
                        i_LOADN     = 1,
                        i_MOVE      = 0,
                        i_DIRECTION = 0,
                        i_A         = dq_i,
                        o_Z         = dq_i_delayed
                    ),
                    Instance("IDDRX2DQA",
                        i_RST     = ResetSignal("sys"),
                        i_SCLK    = ClockSignal("sys"),
                        i_ECLK    = ClockSignal("sys2x"),
                        i_DQSR90  = dqsr90,
                        i_RDPNTR0 = rdpntr[0],
                        i_RDPNTR1 = rdpntr[1],
                        i_RDPNTR2 = rdpntr[2],
                        i_WRPNTR0 = wrpntr[0],
                        i_WRPNTR1 = wrpntr[1],
                        i_WRPNTR2 = wrpntr[2],
                        i_D       = dq_i_delayed,
                        o_Q0      = dq_i_data[0],
                        o_Q1      = dq_i_data[1],
                        o_Q2      = dq_i_data[2],
                        o_Q3      = dq_i_data[3],
                    )
                ]

                dq_i_bitslip = BitSlip(4,
                    rst    = self._dly_sel.storage[i] & self._rdly_dq_bitslip_rst.re,
                    slp    = self._dly_sel.storage[i] & self._rdly_dq_bitslip.re,
                    cycles = 1)
                self.submodules += dq_i_bitslip
                dq_i_bitslip_o_d = Signal(4)
                self.comb += dq_i_bitslip.i.eq(dq_i_data)
                self.sync += dq_i_bitslip_o_d.eq(dq_i_bitslip.o)
                self.comb += [
                    dfi.phases[0].rddata[0*databits+j].eq(dq_i_bitslip_o_d[0]),
                    dfi.phases[0].rddata[1*databits+j].eq(dq_i_bitslip_o_d[1]),
                    dfi.phases[0].rddata[2*databits+j].eq(dq_i_bitslip_o_d[2]),
                    dfi.phases[0].rddata[3*databits+j].eq(dq_i_bitslip_o_d[3]),
                    dfi.phases[1].rddata[0*databits+j].eq(dq_i_bitslip.o[0]),
                    dfi.phases[1].rddata[1*databits+j].eq(dq_i_bitslip.o[1]),
                    dfi.phases[1].rddata[2*databits+j].eq(dq_i_bitslip.o[2]),
                    dfi.phases[1].rddata[3*databits+j].eq(dq_i_bitslip.o[3]),
                ]
                self.specials += [
                    Instance("TSHX2DQA",
                        i_RST     = ResetSignal("sys"),
                        i_SCLK    = ClockSignal("sys"),
                        i_ECLK    = ClockSignal("sys2x"),
                        i_DQSW270 = dqsw270,
                        i_T0      = ~dq_oe,
                        i_T1      = ~dq_oe,
                        o_Q       = dq_oe_n,
                    ),
                    Tristate(pads.dq[j], dq_o, ~dq_oe_n, dq_i)
                ]

        # Read Control Path
        #
        # Creates a shift register of read commands coming from the DFI interface. This shift register
        # is used to control DQS read (internal read pulse of the DQSBUF) and to indicate to the
        # DFI interface that the read data is valid.
        #
        # The DQS read must be asserted for 2 sys_clk cycles before the read data is coming back from
        # the DRAM (see 6.2.4 READ Pulse Positioning Optimization of FPGA-TN-02035-1.2)
        #
        # The read data valid is asserted for 1 sys_clk cycle when the data is available on the DFI
        # interface, the latency is the sum of the ODDRX2DQA, CAS, IDDRX2DQA latencies.

        rddata_en = Signal(self.settings.read_latency)
        rddata_en_last = Signal.like(rddata_en)
        self.comb += rddata_en.eq(Cat(dfi.phases[self.settings.rdphase].rddata_en, rddata_en_last))
        self.sync += rddata_en_last.eq(rddata_en)
        self.sync += [phase.rddata_valid.eq(rddata_en[-1]) for phase in dfi.phases]
        self.comb += dqs_re.eq(rddata_en[cl_sys_latency + 1] | rddata_en[cl_sys_latency + 2])

        # Write Control Path
        #
        # Creates a shift register of write commands coming from the DFI interface. This shift register
        # is used to control DQ/DQS tristates and to select write data of the DRAM burst from the DFI
        # interface: The PHY is operating in halfrate mode (so provide 4 datas every sys_clk cycles:
        # 2x for DDR, 2x for halfrate) but DDR3 requires a burst of 8 datas (BL8) for best efficiency.
        # Writes are then performed in 2 sys_clk cycles and data needs to be selected for each cycle.

        wrdata_en = Signal(cwl_sys_latency + 4)
        wrdata_en_last = Signal.like(wrdata_en)
        self.comb += wrdata_en.eq(Cat(dfi.phases[self.settings.wrphase].wrdata_en, wrdata_en_last))
        self.sync += wrdata_en_last.eq(wrdata_en)
        self.comb += dq_oe.eq(wrdata_en[cwl_sys_latency + 1] | wrdata_en[cwl_sys_latency + 2])
        self.comb += bl8_chunk.eq(wrdata_en[cwl_sys_latency + 1])
        self.comb += dqs_oe.eq(dq_oe)

        # Write DQS Postamble/Preamble Control Path
        #
        # Generates DQS Preamble 1 cycle before the first write and Postamble 1 cycle after the last
        # write. During writes, DQS tristate is configured as output for at least 4 sys_clk cycles:
        # 1 for Preamble, 2 for the Write and 1 for the Postamble.

        self.comb += dqs_preamble.eq( wrdata_en[cwl_sys_latency + 0]  & ~wrdata_en[cwl_sys_latency + 1])
        self.comb += dqs_postamble.eq(wrdata_en[cwl_sys_latency + 3]  & ~wrdata_en[cwl_sys_latency + 2])

class PhaseInjector(Module, AutoCSR):
    def __init__(self, phase):
        self._command       = CSRStorage("command", 6)  # cs, we, cas, ras, wren, rden
        self._command_issue = CSR("command_issue")
        self._address       = CSRStorage("address", len(phase.address), reset_less=True)
        self._baddress      = CSRStorage("baddress", len(phase.bank),    reset_less=True)
        self._wrdata        = CSRStorage("wrdata", len(phase.wrdata),  reset_less=True)
        self._rddata        = CSRStatus("rddata", len(phase.rddata))

        self.comb += [
            If(self._command_issue.re,
                phase.cs_n.eq(Replicate(~self._command.storage[0], len(phase.cs_n))),
                phase.we_n.eq(~self._command.storage[1]),
                phase.cas_n.eq(~self._command.storage[2]),
                phase.ras_n.eq(~self._command.storage[3])
            ).Else(
                phase.cs_n.eq(Replicate(1, len(phase.cs_n))),
                phase.we_n.eq(1),
                phase.cas_n.eq(1),
                phase.ras_n.eq(1)
            ),
            phase.address.eq(self._address.storage),
            phase.bank.eq(self._baddress.storage),
            phase.wrdata_en.eq(self._command_issue.re & self._command.storage[4]),
            phase.rddata_en.eq(self._command_issue.re & self._command.storage[5]),
            phase.wrdata.eq(self._wrdata.storage),
            phase.wrdata_mask.eq(0)
        ]
        self.sync += If(phase.rddata_valid, self._rddata.status.eq(phase.rddata))

class DFIInjector(Module, AutoCSR):
    def __init__(self, addressbits, bankbits, nranks, databits, nphases=1):
        inti        = DFIInterface(addressbits, bankbits, nranks, databits, nphases)
        self.slave  = DFIInterface(addressbits, bankbits, nranks, databits, nphases)
        self.master = DFIInterface(addressbits, bankbits, nranks, databits, nphases)

        self._control = CSRStorage("control", fields=[
            CSRField("sel",     size=1, values=[
                ("``0b0``", "Software (CPU) control."),
                ("``0b1`",  "Hardware control (default)."),
            ], reset=0b1), # Defaults to HW control.
            CSRField("cke",     size=1),
            CSRField("odt",     size=1),
            CSRField("reset_n", size=1),
        ])

        for n, phase in enumerate(inti.phases):
            setattr(self.submodules, "pi" + str(n), PhaseInjector(phase))

        self.comb += If(self._control.fields.sel,
                self.slave.connect(self.master)
            ).Else(
                inti.connect(self.master)
            )
        for i in range(nranks):
            self.comb += [phase.cke[i].eq(self._control.fields.cke) for phase in inti.phases]
            self.comb += [phase.odt[i].eq(self._control.fields.odt) for phase in inti.phases if hasattr(phase, "odt")]
        self.comb += [phase.reset_n.eq(self._control.fields.reset_n) for phase in inti.phases if hasattr(phase, "reset_n")]

class RefreshExecuter(Module):
    """Refresh Executer

    Execute the refresh sequence to the DRAM:
    - Send a "Precharge All" command
    - Wait tRP
    - Send an "Auto Refresh" command
    - Wait tRFC
    """
    def __init__(self, cmd, trp, trfc):
        self.start = Signal()
        self.done  = Signal()

        self.sync += [
            cmd.a.eq(  0),
            cmd.ba.eq( 0),
            cmd.cas.eq(0),
            cmd.ras.eq(0),
            cmd.we.eq( 0),
            self.done.eq(0),
            # Wait start
            timeline(self.start, [
                # Precharge All
                (0, [
                    cmd.a.eq(  2**10),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(0),
                    cmd.ras.eq(1),
                    cmd.we.eq( 1)
                ]),
                # Auto Refresh after tRP
                (trp, [
                    cmd.a.eq(  0),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(1),
                    cmd.ras.eq(1),
                    cmd.we.eq( 0),
                ]),
                # Done after tRP + tRFC
                (trp + trfc, [
                    cmd.a.eq(  0),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(0),
                    cmd.ras.eq(0),
                    cmd.we.eq( 0),
                    self.done.eq(1),
                ]),
            ])
        ]

class RefreshSequencer(Module):
    """Refresh Sequencer

    Sequence N refreshs to the DRAM.
    """
    def __init__(self, cmd, trp, trfc, postponing=1):
        self.start = Signal()
        self.done  = Signal()

        executer = RefreshExecuter(cmd, trp, trfc)
        self.submodules += executer

        count = Signal(bits_for(postponing), reset=postponing-1)
        self.sync += [
            If(self.start,
                count.eq(count.reset)
            ).Elif(executer.done,
                If(count != 0,
                    count.eq(count - 1)
                )
            )
        ]
        self.comb += executer.start.eq(self.start | (count != 0))
        self.comb += self.done.eq(executer.done & (count == 0))

class RefreshTimer(Module):
    """Refresh Timer

    Generate periodic pulses (tREFI period) to trigger DRAM refresh.
    """
    def __init__(self, trefi):
        self.wait  = Signal()
        self.done  = Signal()
        self.count = Signal(bits_for(trefi))

        done  = Signal()
        count = Signal(bits_for(trefi), reset=trefi-1)

        self.sync += [
            If(self.wait & ~self.done,
                count.eq(count - 1)
            ).Else(
                count.eq(count.reset)
            )
        ]
        self.comb += [
            done.eq(count == 0),
            self.done.eq(done),
            self.count.eq(count)
        ]

class RefreshPostponer(Module):
    """Refresh Postponer

    Postpone N Refresh requests and generate a request when N is reached.
    """
    def __init__(self, postponing=1):
        self.req_i = Signal()
        self.req_o = Signal()

        count = Signal(bits_for(postponing), reset=postponing-1)
        self.sync += [
            self.req_o.eq(0),
            If(self.req_i,
                count.eq(count - 1),
                If(count == 0,
                    count.eq(count.reset),
                    self.req_o.eq(1)
                )
            )
        ]

class ZQCSExecuter(Module):
    """ZQ Short Calibration Executer

    Execute the ZQCS sequence to the DRAM:
    - Send a "Precharge All" command
    - Wait tRP
    - Send an "ZQ Short Calibration" command
    - Wait tZQCS
    """
    def __init__(self, cmd, trp, tzqcs):
        self.start = Signal()
        self.done  = Signal()

        self.sync += [
            # Note: Don't set cmd to 0 since already done in RefreshExecuter
            self.done.eq(0),
            # Wait start
            timeline(self.start, [
                # Precharge All
                (0, [
                    cmd.a.eq(  2**10),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(0),
                    cmd.ras.eq(1),
                    cmd.we.eq( 1)
                ]),
                # ZQ Short Calibration after tRP
                (trp, [
                    cmd.a.eq(  0),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(0),
                    cmd.ras.eq(0),
                    cmd.we.eq( 1),
                ]),
                # Done after tRP + tZQCS
                (trp + tzqcs, [
                    cmd.a.eq(  0),
                    cmd.ba.eq( 0),
                    cmd.cas.eq(0),
                    cmd.ras.eq(0),
                    cmd.we.eq( 0),
                    self.done.eq(1)
                ]),
            ])
        ]

class Refresher(Module):
    """Refresher

    Manage DRAM refresh.

    The DRAM needs to be periodically refreshed with a tREFI period to avoid data corruption. During
    a refresh, the controller send a "Precharge All" command to close and precharge all rows and then
    send a "Auto Refresh" command.

    Before executing the refresh, the Refresher advertises the Controller that a refresh should occur,
    this allows the Controller to finish the current transaction and block next transactions. Once all
    transactions are done, the Refresher can execute the refresh Sequence and release the Controller.

    """
    def __init__(self, settings, clk_freq, zqcs_freq=1e0, postponing=1):
        assert postponing <= 8
        abits  = settings.geom.addressbits
        babits = settings.geom.bankbits + log2_int(settings.phy.nranks)
        self.cmd = cmd = Endpoint(cmd_request_rw_layout(a=abits, ba=babits))

        wants_refresh = Signal()
        wants_zqcs    = Signal()

        # Refresh Timer ----------------------------------------------------------------------------
        timer = RefreshTimer(settings.timing.tREFI)
        self.submodules.timer = timer
        self.comb += timer.wait.eq(~timer.done)

        # Refresh Postponer ------------------------------------------------------------------------
        postponer = RefreshPostponer(postponing)
        self.submodules.postponer = postponer
        self.comb += postponer.req_i.eq(self.timer.done)
        self.comb += wants_refresh.eq(postponer.req_o)

        # Refresh Sequencer ------------------------------------------------------------------------
        sequencer = RefreshSequencer(cmd, settings.timing.tRP, settings.timing.tRFC, postponing)
        self.submodules.sequencer = sequencer

        if settings.timing.tZQCS is not None:
            # ZQCS Timer ---------------------------------------------------------------------------
            zqcs_timer = RefreshTimer(int(clk_freq/zqcs_freq))
            self.submodules.zqcs_timer = zqcs_timer
            self.comb += wants_zqcs.eq(zqcs_timer.done)

            # ZQCS Executer ------------------------------------------------------------------------
            zqcs_executer = ZQCSExecuter(cmd, settings.timing.tRP, settings.timing.tZQCS)
            self.submodules.zqs_executer = zqcs_executer
            self.comb += zqcs_timer.wait.eq(~zqcs_executer.done)

        # Refresh FSM ------------------------------------------------------------------------------
        self.submodules.fsm = fsm = FSM()
        fsm.act("IDLE",
            If(settings.with_refresh,
                If(wants_refresh,
                    NextState("WAIT-BANK-MACHINES")
                )
            )
        )
        fsm.act("WAIT-BANK-MACHINES",
            cmd.valid.eq(1),
            If(cmd.ready,
                sequencer.start.eq(1),
                NextState("DO-REFRESH")
            )
        )
        if settings.timing.tZQCS is None:
            fsm.act("DO-REFRESH",
                cmd.valid.eq(1),
                If(sequencer.done,
                    cmd.valid.eq(0),
                    cmd.last.eq(1),
                    NextState("IDLE")
                )
            )
        else:
            fsm.act("DO-REFRESH",
                cmd.valid.eq(1),
                If(sequencer.done,
                    If(wants_zqcs,
                        zqcs_executer.start.eq(1),
                        NextState("DO-ZQCS")
                    ).Else(
                        cmd.valid.eq(0),
                        cmd.last.eq(1),
                        NextState("IDLE")
                    )
                )
            )
            fsm.act("DO-ZQCS",
                cmd.valid.eq(1),
                If(zqcs_executer.done,
                    cmd.valid.eq(0),
                    cmd.last.eq(1),
                    NextState("IDLE")
                )
            )

class _AddressSlicer:
    """Helper for extracting row/col from address

    Column occupies lower bits of the address, row - higher bits. Address has
    a forced alignment, so column does not contain alignment bits.
    """
    def __init__(self, colbits, address_align):
        self.colbits       = colbits
        self.address_align = address_align

    def row(self, address):
        split = self.colbits - self.address_align
        return address[split:]

    def col(self, address):
        split = self.colbits - self.address_align
        return Cat(Replicate(0, self.address_align), address[:split])

class BankMachine(Module):
    """Converts requests from ports into DRAM commands

    BankMachine abstracts single DRAM bank by keeping track of the currently
    selected row. It converts requests from LiteDRAMCrossbar to targetted
    to that bank into DRAM commands that go to the Multiplexer, inserting any
    needed activate/precharge commands (with optional auto-precharge). It also
    keeps track and enforces some DRAM timings (other timings are enforced in
    the Multiplexer).

    BankMachines work independently from the data path (which connects
    LiteDRAMCrossbar with the Multiplexer directly).

    Stream of requests from LiteDRAMCrossbar is being queued, so that reqeust
    can be "looked ahead", and auto-precharge can be performed (if enabled in
    settings).

    Lock (cmd_layout.lock) is used to synchronise with LiteDRAMCrossbar. It is
    being held when:
     - there is a valid command awaiting in `cmd_buffer_lookahead` - this buffer
       becomes ready simply when the next data gets fetched to the `cmd_buffer`
     - there is a valid command in `cmd_buffer` - `cmd_buffer` becomes ready
       when the BankMachine sends wdata_ready/rdata_valid back to the crossbar

    Parameters
    ----------
    n : int
        Bank number
    address_width : int
        LiteDRAMInterface address width
    address_align : int
        Address alignment depending on burst length
    nranks : int
        Number of separate DRAM chips (width of chip select)
    settings : ControllerSettings
        LiteDRAMController settings

    Attributes
    ----------
    req : Record(cmd_layout)
        Stream of requests from LiteDRAMCrossbar
    refresh_req : Signal(), in
        Indicates that refresh needs to be done, connects to Refresher.cmd.valid
    refresh_gnt : Signal(), out
        Indicates that refresh permission has been granted, satisfying timings
    cmd : Endpoint(cmd_request_rw_layout)
        Stream of commands to the Multiplexer
    """
    def __init__(self, n, address_width, address_align, nranks, settings):
        self.req = req = Record(cmd_layout(address_width))
        self.refresh_req = refresh_req = Signal()
        self.refresh_gnt = refresh_gnt = Signal()

        a  = settings.geom.addressbits
        ba = settings.geom.bankbits + log2_int(nranks)
        self.cmd = cmd = Endpoint(cmd_request_rw_layout(a, ba))

        auto_precharge = Signal()

        # Command buffer ---------------------------------------------------------------------------
        cmd_buffer_layout    = [("we", 1), ("addr", len(req.addr))]
        cmd_buffer_lookahead = SyncFIFO(
            cmd_buffer_layout, settings.cmd_buffer_depth,
            buffered=settings.cmd_buffer_buffered)
        cmd_buffer = Buffer(cmd_buffer_layout) # 1 depth buffer to detect row change
        self.submodules += cmd_buffer_lookahead, cmd_buffer
        self.comb += [
            req.connect(cmd_buffer_lookahead.sink, keep={"valid", "ready", "we", "addr"}),
            cmd_buffer_lookahead.source.connect(cmd_buffer.sink),
            cmd_buffer.source.ready.eq(req.wdata_ready | req.rdata_valid),
            req.lock.eq(cmd_buffer_lookahead.source.valid | cmd_buffer.source.valid),
        ]

        slicer = _AddressSlicer(settings.geom.colbits, address_align)

        # Row tracking -----------------------------------------------------------------------------
        row        = Signal(settings.geom.rowbits)
        row_opened = Signal()
        row_hit    = Signal()
        row_open   = Signal()
        row_close  = Signal()
        self.comb += row_hit.eq(row == slicer.row(cmd_buffer.source.addr))
        self.sync += \
            If(row_close,
                row_opened.eq(0)
            ).Elif(row_open,
                row_opened.eq(1),
                row.eq(slicer.row(cmd_buffer.source.addr))
            )

        # Address generation -----------------------------------------------------------------------
        row_col_n_addr_sel = Signal()
        self.comb += [
            cmd.ba.eq(n),
            If(row_col_n_addr_sel,
                cmd.a.eq(slicer.row(cmd_buffer.source.addr))
            ).Else(
                cmd.a.eq((auto_precharge << 10) | slicer.col(cmd_buffer.source.addr))
            )
        ]

        # tWTP (write-to-precharge) controller -----------------------------------------------------
        write_latency = math.ceil(settings.phy.cwl / settings.phy.nphases)
        precharge_time = write_latency + settings.timing.tWR + settings.timing.tCCD # AL=0
        self.submodules.twtpcon = twtpcon = tXXDController(precharge_time)
        self.comb += twtpcon.valid.eq(cmd.valid & cmd.ready & cmd.is_write)

        # tRC (activate-activate) controller -------------------------------------------------------
        self.submodules.trccon = trccon = tXXDController(settings.timing.tRC)
        self.comb += trccon.valid.eq(cmd.valid & cmd.ready & row_open)

        # tRAS (activate-precharge) controller -----------------------------------------------------
        self.submodules.trascon = trascon = tXXDController(settings.timing.tRAS)
        self.comb += trascon.valid.eq(cmd.valid & cmd.ready & row_open)

        # Auto Precharge generation ----------------------------------------------------------------
        # generate auto precharge when current and next cmds are to different rows
        if settings.with_auto_precharge:
            self.comb += \
                If(cmd_buffer_lookahead.source.valid & cmd_buffer.source.valid,
                    If(slicer.row(cmd_buffer_lookahead.source.addr) !=
                       slicer.row(cmd_buffer.source.addr),
                        auto_precharge.eq(row_close == 0)
                    )
                )

        # Control and command generation FSM -------------------------------------------------------
        # Note: tRRD, tFAW, tCCD, tWTR timings are enforced by the multiplexer
        self.submodules.fsm = fsm = FSM()
        fsm.act("REGULAR",
            If(refresh_req,
                NextState("REFRESH")
            ).Elif(cmd_buffer.source.valid,
                If(row_opened,
                    If(row_hit,
                        cmd.valid.eq(1),
                        If(cmd_buffer.source.we,
                            req.wdata_ready.eq(cmd.ready),
                            cmd.is_write.eq(1),
                            cmd.we.eq(1),
                        ).Else(
                            req.rdata_valid.eq(cmd.ready),
                            cmd.is_read.eq(1)
                        ),
                        cmd.cas.eq(1),
                        If(cmd.ready & auto_precharge,
                           NextState("AUTOPRECHARGE")
                        )
                    ).Else(  # row_opened & ~row_hit
                        NextState("PRECHARGE")
                    )
                ).Else(  # ~row_opened
                    NextState("ACTIVATE")
                )
            )
        )
        fsm.act("PRECHARGE",
            # Note: we are presenting the column address, A10 is always low
            If(twtpcon.ready & trascon.ready,
                cmd.valid.eq(1),
                If(cmd.ready,
                    NextState("TRP")
                ),
                cmd.ras.eq(1),
                cmd.we.eq(1),
                cmd.is_cmd.eq(1)
            ),
            row_close.eq(1)
        )
        fsm.act("AUTOPRECHARGE",
            If(twtpcon.ready & trascon.ready,
                NextState("TRP")
            ),
            row_close.eq(1)
        )
        fsm.act("ACTIVATE",
            If(trccon.ready,
                row_col_n_addr_sel.eq(1),
                row_open.eq(1),
                cmd.valid.eq(1),
                cmd.is_cmd.eq(1),
                If(cmd.ready,
                    NextState("TRCD")
                ),
                cmd.ras.eq(1)
            )
        )
        fsm.act("REFRESH",
            If(twtpcon.ready,
                refresh_gnt.eq(1),
            ),
            row_close.eq(1),
            cmd.is_cmd.eq(1),
            If(~refresh_req,
                NextState("REGULAR")
            )
        )
        fsm.delayed_enter("TRP", "ACTIVATE", settings.timing.tRP - 1)
        fsm.delayed_enter("TRCD", "REGULAR", settings.timing.tRCD - 1)

class Bandwidth(Module, AutoCSR):
    """Measures LiteDRAM bandwidth

    This module works by counting the number of read/write commands issued by
    the controller during a fixed time period. To copy the values registered
    during the last finished period, user must write to the `update` register.

    Parameters
    ----------
    cmd : Endpoint(cmd_request_rw_layout)
        Multiplexer endpoint on which all read/write requests are being sent
    data_width : int, in
        Data width that can be read back from CSR
    period_bits : int, in
        Defines length of bandwidth measurement period = 2^period_bits

    Attributes
    ----------
    update : CSR, in
        Copy the values from last finished period to the status registers
    nreads : CSRStatus, out
        Number of READ commands issued during a period
    nwrites : CSRStatus, out
        Number of WRITE commands issued during a period
    data_width : CSRStatus, out
        Can be read to calculate bandwidth in bits/sec as:
            bandwidth = (nreads+nwrites) * data_width / period
    """
    def __init__(self, cmd, data_width, period_bits=24):
        self.update     = CSR("update")
        self.nreads     = CSRStatus("nreads", period_bits + 1)
        self.nwrites    = CSRStatus("nwrites", period_bits + 1)
        self.data_width = CSRStatus("data_width", bits_for(data_width), reset=data_width)

        cmd_valid    = Signal()
        cmd_ready    = Signal()
        cmd_is_read  = Signal()
        cmd_is_write = Signal()
        self.sync += [
            cmd_valid.eq(cmd.valid),
            cmd_ready.eq(cmd.ready),
            cmd_is_read.eq(cmd.is_read),
            cmd_is_write.eq(cmd.is_write)
        ]

        counter   = Signal(period_bits)
        period    = Signal()
        nreads    = Signal(period_bits + 1)
        nwrites   = Signal(period_bits + 1)
        nreads_r  = Signal(period_bits + 1)
        nwrites_r = Signal(period_bits + 1)
        self.sync += [
            Cat(counter, period).eq(counter + 1),
            If(period,
                nreads_r.eq(nreads),
                nwrites_r.eq(nwrites),
                nreads.eq(0),
                nwrites.eq(0),
                # don't miss command if there is one on period boundary
                If(cmd_valid & cmd_ready,
                    If(cmd_is_read, nreads.eq(1)),
                    If(cmd_is_write, nwrites.eq(1)),
                )
            ).Elif(cmd_valid & cmd_ready,
                If(cmd_is_read, nreads.eq(nreads + 1)),
                If(cmd_is_write, nwrites.eq(nwrites + 1)),
            ),
            If(self.update.re,
                self.nreads.status.eq(nreads_r),
                self.nwrites.status.eq(nwrites_r)
            )
        ]

class _CommandChooser(Module):
    """Arbitrates between requests, filtering them based on their type

    Uses RoundRobin to choose current request, filters requests based on
    `want_*` signals.

    Parameters
    ----------
    requests : [Endpoint(cmd_request_rw_layout), ...]
        Request streams to consider for arbitration

    Attributes
    ----------
    want_reads : Signal, in
        Consider read requests
    want_writes : Signal, in
        Consider write requests
    want_cmds : Signal, in
        Consider command requests (without ACT)
    want_activates : Signal, in
        Also consider ACT commands
    cmd : Endpoint(cmd_request_rw_layout)
        Currently selected request stream (when ~cmd.valid, cas/ras/we are 0)
    """
    def __init__(self, requests):
        self.want_reads     = Signal()
        self.want_writes    = Signal()
        self.want_cmds      = Signal()
        self.want_activates = Signal()

        a  = len(requests[0].a)
        ba = len(requests[0].ba)

        # cas/ras/we are 0 when valid is inactive
        self.cmd = cmd = Endpoint(cmd_request_rw_layout(a, ba))

        n = len(requests)

        valids = Signal(n)
        for i, request in enumerate(requests):
            is_act_cmd = request.ras & ~request.cas & ~request.we
            command = request.is_cmd & self.want_cmds & (~is_act_cmd | self.want_activates)
            read = request.is_read == self.want_reads
            write = request.is_write == self.want_writes
            self.comb += valids[i].eq(request.valid & (command | (read & write)))

        arbiter = RoundRobin(n, SP_CE)
        self.submodules += arbiter
        choices = Array(valids[i] for i in range(n))
        self.comb += [
            arbiter.request.eq(valids),
            cmd.valid.eq(choices[arbiter.grant])
        ]

        for name in ["a", "ba", "is_read", "is_write", "is_cmd"]:
            choices = Array(getattr(req, name) for req in requests)
            self.comb += getattr(cmd, name).eq(choices[arbiter.grant])

        for name in ["cas", "ras", "we"]:
            # we should only assert those signals when valid is 1
            choices = Array(getattr(req, name) for req in requests)
            self.comb += \
                If(cmd.valid,
                    getattr(cmd, name).eq(choices[arbiter.grant])
                )

        for i, request in enumerate(requests):
            self.comb += \
                If(cmd.valid & cmd.ready & (arbiter.grant == i),
                    request.ready.eq(1)
                )
        # Arbitrate if a command is being accepted or if the command is not valid to ensure a valid
        # command is selected when cmd.ready goes high.
        self.comb += arbiter.ce.eq(cmd.ready | ~cmd.valid)

    # helpers
    def accept(self):
        return self.cmd.valid & self.cmd.ready

    def activate(self):
        return self.cmd.ras & ~self.cmd.cas & ~self.cmd.we

    def write(self):
        return self.cmd.is_write

    def read(self):
        return self.cmd.is_read

(STEER_NOP, STEER_CMD, STEER_REQ, STEER_REFRESH) = range(4)

class _Steerer(Module):
    """Connects selected request to DFI interface

    cas/ras/we/is_write/is_read are connected only when `cmd.valid & cmd.ready`.
    Rank bits are decoded and used to drive cs_n in multi-rank systems,
    STEER_REFRESH always enables all ranks.

    Parameters
    ----------
    commands : [Endpoint(cmd_request_rw_layout), ...]
        Command streams to choose from. Must be of len=4 in the order:
            NOP, CMD, REQ, REFRESH
        NOP can be of type Record(cmd_request_rw_layout) instead, so that it is
        always considered invalid (because of lack of the `valid` attribute).
    dfi : DFIInterface
        DFI interface connected to PHY

    Attributes
    ----------
    sel : [Signal(max=len(commands)), ...], in
        Signals for selecting which request gets connected to the corresponding
        DFI phase. The signals should take one of the values from STEER_* to
        select given source.
    """
    def __init__(self, commands, dfi):
        ncmd = len(commands)
        nph  = len(dfi.phases)
        self.sel = [Signal(max=ncmd) for i in range(nph)]

        def valid_and(cmd, attr):
            if not hasattr(cmd, "valid"):
                return 0
            else:
                return cmd.valid & cmd.ready & getattr(cmd, attr)

        for i, (phase, sel) in enumerate(zip(dfi.phases, self.sel)):
            nranks   = len(phase.cs_n)
            rankbits = log2_int(nranks)
            if hasattr(phase, "reset_n"):
                self.comb += phase.reset_n.eq(1)
            self.comb += phase.cke.eq(Replicate(Signal(reset=1), nranks))
            if hasattr(phase, "odt"):
                # FIXME: add dynamic drive for multi-rank (will be needed for high frequencies)
                self.comb += phase.odt.eq(Replicate(Signal(reset=1), nranks))
            if rankbits:
                rank_decoder = Decoder(nranks)
                self.submodules += rank_decoder
                self.comb += rank_decoder.i.eq((Array(cmd.ba[-rankbits:] for cmd in commands)[sel]))
                if i == 0: # Select all ranks on refresh.
                    self.sync += If(sel == STEER_REFRESH, phase.cs_n.eq(0)).Else(phase.cs_n.eq(~rank_decoder.o))
                else:
                    self.sync += phase.cs_n.eq(~rank_decoder.o)
                self.sync += phase.bank.eq(Array(cmd.ba[:-rankbits] for cmd in commands)[sel])
            else:
                self.sync += phase.cs_n.eq(0)
                self.sync += phase.bank.eq(Array(cmd.ba[:] for cmd in commands)[sel])

            self.sync += [
                phase.address.eq(Array(cmd.a for cmd in commands)[sel]),
                phase.cas_n.eq(~Array(valid_and(cmd, "cas") for cmd in commands)[sel]),
                phase.ras_n.eq(~Array(valid_and(cmd, "ras") for cmd in commands)[sel]),
                phase.we_n.eq(~Array(valid_and(cmd, "we") for cmd in commands)[sel])
            ]

            rddata_ens = Array(valid_and(cmd, "is_read") for cmd in commands)
            wrdata_ens = Array(valid_and(cmd, "is_write") for cmd in commands)
            self.sync += [
                phase.rddata_en.eq(rddata_ens[sel]),
                phase.wrdata_en.eq(wrdata_ens[sel])
            ]

class Multiplexer(Module, AutoCSR):
    """Multplexes requets from BankMachines to DFI

    This module multiplexes requests from BankMachines (and Refresher) and
    connects them to DFI. Refresh commands are coordinated between the Refresher
    and BankMachines to ensure there are no conflicts. Enforces required timings
    between commands (some timings are enforced by BankMachines).

    Parameters
    ----------
    settings : ControllerSettings
        Controller settings (with .phy, .geom and .timing settings)
    bank_machines : [BankMachine, ...]
        Bank machines that generate command requests to the Multiplexer
    refresher : Refresher
        Generates REFRESH command requests
    dfi : DFIInterface
        DFI connected to the PHY
    interface : LiteDRAMInterface
        Data interface connected directly to LiteDRAMCrossbar
    """
    def __init__(self, settings, bank_machines, refresher, dfi, interface):
        assert(settings.phy.nphases == len(dfi.phases))

        ras_allowed = Signal(reset=1)
        cas_allowed = Signal(reset=1)

        # Command choosing -------------------------------------------------------------------------
        requests = [bm.cmd for bm in bank_machines]
        self.submodules.choose_cmd = choose_cmd = _CommandChooser(requests)
        self.submodules.choose_req = choose_req = _CommandChooser(requests)
        if settings.phy.nphases == 1:
            # When only 1 phase, use choose_req for all requests
            choose_cmd = choose_req
            self.comb += choose_req.want_cmds.eq(1)
            self.comb += choose_req.want_activates.eq(ras_allowed)

        # Command steering -------------------------------------------------------------------------
        nop = Record(cmd_request_layout(settings.geom.addressbits, log2_int(len(bank_machines))))
        # nop must be 1st
        commands = [nop, choose_cmd.cmd, choose_req.cmd, refresher.cmd]
        steerer = _Steerer(commands, dfi)
        self.submodules += steerer

        # tRRD timing (Row to Row delay) -----------------------------------------------------------
        self.submodules.trrdcon = trrdcon = tXXDController(settings.timing.tRRD)
        self.comb += trrdcon.valid.eq(choose_cmd.accept() & choose_cmd.activate())

        # tFAW timing (Four Activate Window) -------------------------------------------------------
        self.submodules.tfawcon = tfawcon = tFAWController(settings.timing.tFAW)
        self.comb += tfawcon.valid.eq(choose_cmd.accept() & choose_cmd.activate())

        # RAS control ------------------------------------------------------------------------------
        self.comb += ras_allowed.eq(trrdcon.ready & tfawcon.ready)

        # tCCD timing (Column to Column delay) -----------------------------------------------------
        self.submodules.tccdcon = tccdcon = tXXDController(settings.timing.tCCD)
        self.comb += tccdcon.valid.eq(choose_req.accept() & (choose_req.write() | choose_req.read()))

        # CAS control ------------------------------------------------------------------------------
        self.comb += cas_allowed.eq(tccdcon.ready)

        # tWTR timing (Write to Read delay) --------------------------------------------------------
        write_latency = math.ceil(settings.phy.cwl / settings.phy.nphases)
        self.submodules.twtrcon = twtrcon = tXXDController(
            settings.timing.tWTR + write_latency +
            # tCCD must be added since tWTR begins after the transfer is complete
            settings.timing.tCCD if settings.timing.tCCD is not None else 0)
        self.comb += twtrcon.valid.eq(choose_req.accept() & choose_req.write())

        # Read/write turnaround --------------------------------------------------------------------
        read_available = Signal()
        write_available = Signal()
        reads = [req.valid & req.is_read for req in requests]
        writes = [req.valid & req.is_write for req in requests]
        self.comb += [
            read_available.eq(reduce(operator.or_, reads)),
            write_available.eq(reduce(operator.or_, writes))
        ]

        def anti_starvation(timeout):
            en = Signal()
            max_time = Signal()
            if timeout:
                t = timeout - 1
                time = Signal(max=t+1)
                self.comb += max_time.eq(time == 0)
                self.sync += If(~en,
                        time.eq(t)
                    ).Elif(~max_time,
                        time.eq(time - 1)
                    )
            else:
                self.comb += max_time.eq(0)
            return en, max_time

        read_time_en,   max_read_time = anti_starvation(settings.read_time)
        write_time_en, max_write_time = anti_starvation(settings.write_time)

        # Refresh ----------------------------------------------------------------------------------
        self.comb += [bm.refresh_req.eq(refresher.cmd.valid) for bm in bank_machines]
        go_to_refresh = Signal()
        bm_refresh_gnts = [bm.refresh_gnt for bm in bank_machines]
        self.comb += go_to_refresh.eq(reduce(operator.and_, bm_refresh_gnts))

        # Datapath ---------------------------------------------------------------------------------
        all_rddata = [p.rddata for p in dfi.phases]
        all_wrdata = [p.wrdata for p in dfi.phases]
        all_wrdata_mask = [p.wrdata_mask for p in dfi.phases]
        self.comb += [
            interface.rdata.eq(Cat(*all_rddata)),
            Cat(*all_wrdata).eq(interface.wdata),
            Cat(*all_wrdata_mask).eq(~interface.wdata_we)
        ]

        def steerer_sel(steerer, r_w_n):
            r = []
            for i in range(settings.phy.nphases):
                s = steerer.sel[i].eq(STEER_NOP)
                if r_w_n == "read":
                    if i == settings.phy.rdphase:
                        s = steerer.sel[i].eq(STEER_REQ)
                    elif i == settings.phy.rdcmdphase:
                        s = steerer.sel[i].eq(STEER_CMD)
                elif r_w_n == "write":
                    if i == settings.phy.wrphase:
                        s = steerer.sel[i].eq(STEER_REQ)
                    elif i == settings.phy.wrcmdphase:
                        s = steerer.sel[i].eq(STEER_CMD)
                else:
                    raise ValueError
                r.append(s)
            return r

        # Control FSM ------------------------------------------------------------------------------
        self.submodules.fsm = fsm = FSM()
        fsm.act("READ",
            read_time_en.eq(1),
            choose_req.want_reads.eq(1),
            If(settings.phy.nphases == 1,
                choose_req.cmd.ready.eq(cas_allowed & (~choose_req.activate() | ras_allowed))
            ).Else(
                choose_cmd.want_activates.eq(ras_allowed),
                choose_cmd.cmd.ready.eq(~choose_cmd.activate() | ras_allowed),
                choose_req.cmd.ready.eq(cas_allowed)
            ),
            steerer_sel(steerer, "read"),
            If(write_available,
                # TODO: switch only after several cycles of ~read_available?
                If(~read_available | max_read_time,
                    NextState("RTW")
                )
            ),
            If(go_to_refresh,
                NextState("REFRESH")
            )
        )
        fsm.act("WRITE",
            write_time_en.eq(1),
            choose_req.want_writes.eq(1),
            If(settings.phy.nphases == 1,
                choose_req.cmd.ready.eq(cas_allowed & (~choose_req.activate() | ras_allowed))
            ).Else(
                choose_cmd.want_activates.eq(ras_allowed),
                choose_cmd.cmd.ready.eq(~choose_cmd.activate() | ras_allowed),
                choose_req.cmd.ready.eq(cas_allowed),
            ),
            steerer_sel(steerer, "write"),
            If(read_available,
                If(~write_available | max_write_time,
                    NextState("WTR")
                )
            ),
            If(go_to_refresh,
                NextState("REFRESH")
            )
        )
        fsm.act("REFRESH",
            steerer.sel[0].eq(STEER_REFRESH),
            refresher.cmd.ready.eq(1),
            If(refresher.cmd.last,
                NextState("READ")
            )
        )
        fsm.act("WTR",
            If(twtrcon.ready,
                NextState("READ")
            )
        )
        # TODO: reduce this, actual limit is around (cl+1)/nphases
        fsm.delayed_enter("RTW", "WRITE", settings.phy.read_latency-1)

        if settings.with_bandwidth:
            data_width = settings.phy.dfi_databits*settings.phy.nphases
            self.submodules.bandwidth = Bandwidth(self.choose_req.cmd, data_width)

class ControllerSettings(Settings):
    def __init__(self,
        # Command buffers
        cmd_buffer_depth    = 8,
        cmd_buffer_buffered = False,

        # Read/Write times
        read_time           = 32,
        write_time          = 16,

        # Bandwidth
        with_bandwidth      = False,

        # Refresh
        with_refresh        = True,
        refresh_cls         = Refresher,
        refresh_zqcs_freq   = 1e0,
        refresh_postponing  = 1,

        # Auto-Precharge
        with_auto_precharge = True,

        # Address mapping
        address_mapping     = "ROW_BANK_COL"):
        self.set_attributes(locals())

class LiteDRAMController(Module):
    def __init__(self, phy_settings, geom_settings, timing_settings, clk_freq,
        controller_settings=ControllerSettings()):
        burst_length = phy_settings.nphases * (1 if phy_settings.memtype == "SDR" else 2)
        address_align = log2_int(burst_length)

        # Settings ---------------------------------------------------------------------------------
        self.settings        = controller_settings
        self.settings.phy    = phy_settings
        self.settings.geom   = geom_settings
        self.settings.timing = timing_settings

        nranks = phy_settings.nranks
        nbanks = 2**geom_settings.bankbits

        # LiteDRAM Interface (User) ----------------------------------------------------------------
        self.interface = interface = LiteDRAMInterface(address_align, self.settings)

        # DFI Interface (Memory) -------------------------------------------------------------------
        self.dfi = DFIInterface(
            addressbits = geom_settings.addressbits,
            bankbits    = geom_settings.bankbits,
            nranks      = phy_settings.nranks,
            databits    = phy_settings.dfi_databits,
            nphases     = phy_settings.nphases)

        # Refresher --------------------------------------------------------------------------------
        self.submodules.refresher = self.settings.refresh_cls(self.settings,
            clk_freq   = clk_freq,
            zqcs_freq  = self.settings.refresh_zqcs_freq,
            postponing = self.settings.refresh_postponing)

        # Bank Machines ----------------------------------------------------------------------------
        bank_machines = []
        for n in range(nranks*nbanks):
            bank_machine = BankMachine(n,
                address_width = interface.address_width,
                address_align = address_align,
                nranks        = nranks,
                settings      = self.settings)
            bank_machines.append(bank_machine)
            self.submodules += bank_machine
            self.comb += getattr(interface, "bank"+str(n)).connect(bank_machine.req)

        # Multiplexer ------------------------------------------------------------------------------
        self.submodules.multiplexer = Multiplexer(
            settings      = self.settings,
            bank_machines = bank_machines,
            refresher     = self.refresher,
            dfi           = self.dfi,
            interface     = interface)

    def get_csrs(self):
        return self.multiplexer.get_csrs()

class LiteDRAMCrossbar(Module):
    """Multiplexes LiteDRAMController (slave) between ports (masters)

    To get a port to LiteDRAM, use the `get_port` method. It handles data width
    conversion and clock domain crossing, returning LiteDRAMNativePort.

    The crossbar routes requests from masters to the BankMachines
    (bankN.cmd_layout) and connects data path directly to the Multiplexer
    (data_layout). It performs address translation based on chosen
    `controller.settings.address_mapping`.
    Internally, all masters are multiplexed between controller banks based on
    the bank address (extracted from the presented address). Each bank has
    a RoundRobin arbiter, that selects from masters that want to access this
    bank and are not already locked.

    Locks (cmd_layout.lock) make sure that, when a master starts a transaction
    with given bank (which may include multiple reads/writes), no other bank
    will be assigned to it during this time.
    Arbiter (of a bank) considers given master as a candidate for selection if:
     - given master's command is valid
     - given master addresses the arbiter's bank
     - given master is not locked
       * i.e. it is not during transaction with another bank
       * i.e. no other bank's arbiter granted permission for this master (with
         bank.lock being active)

    Data ready/valid signals for banks are routed from bankmachines with
    a latency that synchronizes them with the data coming over datapath.

    Parameters
    ----------
    controller : LiteDRAMInterface
        Interface to LiteDRAMController

    Attributes
    ----------
    masters : [LiteDRAMNativePort, ...]
        LiteDRAM memory ports
    """
    def __init__(self, controller):
        self.controller = controller

        self.rca_bits         = controller.address_width
        self.nbanks           = controller.nbanks
        self.nranks           = controller.nranks
        self.cmd_buffer_depth = controller.settings.cmd_buffer_depth
        self.read_latency     = controller.settings.phy.read_latency + 1
        self.write_latency    = controller.settings.phy.write_latency + 1

        self.bank_bits = log2_int(self.nbanks, False)
        self.rank_bits = log2_int(self.nranks, False)

        self.masters = []

    def get_port(self, mode="both", data_width=None, clock_domain="sys", reverse=False):
        if self.finalized:
            raise FinalizeError

        if data_width is None:
            # use internal data_width when no width adaptation is requested
            data_width = self.controller.data_width

        # Crossbar port ----------------------------------------------------------------------------
        port = LiteDRAMNativePort(
            mode          = mode,
            address_width = self.rca_bits + self.bank_bits - self.rank_bits,
            data_width    = self.controller.data_width,
            clock_domain  = "sys",
            id            = len(self.masters))
        self.masters.append(port)

        # Clock domain crossing --------------------------------------------------------------------
        if clock_domain != "sys":
            new_port = LiteDRAMNativePort(
                mode          = mode,
                address_width = port.address_width,
                data_width    = port.data_width,
                clock_domain  = clock_domain,
                id            = port.id)
            self.submodules += LiteDRAMNativePortCDC(new_port, port)
            port = new_port

        # Data width convertion --------------------------------------------------------------------
        if data_width != self.controller.data_width:
            if data_width > self.controller.data_width:
                addr_shift = -log2_int(data_width//self.controller.data_width)
            else:
                addr_shift = log2_int(self.controller.data_width//data_width)
            new_port = LiteDRAMNativePort(
                mode          = mode,
                address_width = port.address_width + addr_shift,
                data_width    = data_width,
                clock_domain  = clock_domain,
                id            = port.id)
            self.submodules += ClockDomainsRenamer(clock_domain)(
                LiteDRAMNativePortConverter(new_port, port, reverse))
            port = new_port

        return port

    def do_finalize(self):
        controller = self.controller
        nmasters   = len(self.masters)

        # Address mapping --------------------------------------------------------------------------
        cba_shifts = {"ROW_BANK_COL": controller.settings.geom.colbits - controller.address_align}
        cba_shift = cba_shifts[controller.settings.address_mapping]
        m_ba      = [m.get_bank_address(self.bank_bits, cba_shift)for m in self.masters]
        m_rca     = [m.get_row_column_address(self.bank_bits, self.rca_bits, cba_shift) for m in self.masters]

        master_readys       = [0]*nmasters
        master_wdata_readys = [0]*nmasters
        master_rdata_valids = [0]*nmasters

        arbiters = [RoundRobin(nmasters, SP_CE) for n in range(self.nbanks)]
        self.submodules += arbiters

        for nb, arbiter in enumerate(arbiters):
            bank = getattr(controller, "bank"+str(nb))

            # For each master, determine if another bank locks it ----------------------------------
            master_locked = []
            for nm, master in enumerate(self.masters):
                locked = Signal()
                for other_nb, other_arbiter in enumerate(arbiters):
                    if other_nb != nb:
                        other_bank = getattr(controller, "bank"+str(other_nb))
                        locked = locked | (other_bank.lock & (other_arbiter.grant == nm))
                master_locked.append(locked)

            # Arbitrate ----------------------------------------------------------------------------
            bank_selected  = [(ba == nb) & ~locked for ba, locked in zip(m_ba, master_locked)]
            bank_requested = [bs & master.cmd.valid for bs, master in zip(bank_selected, self.masters)]
            self.comb += [
                arbiter.request.eq(Cat(*bank_requested)),
                arbiter.ce.eq(~bank.valid & ~bank.lock)
            ]

            # Route requests -----------------------------------------------------------------------
            self.comb += [
                bank.addr.eq(Array(m_rca)[arbiter.grant]),
                bank.we.eq(Array(self.masters)[arbiter.grant].cmd.we),
                bank.valid.eq(Array(bank_requested)[arbiter.grant])
            ]
            master_readys = [master_ready | ((arbiter.grant == nm) & bank_selected[nm] & bank.ready)
                for nm, master_ready in enumerate(master_readys)]
            master_wdata_readys = [master_wdata_ready | ((arbiter.grant == nm) & bank.wdata_ready)
                for nm, master_wdata_ready in enumerate(master_wdata_readys)]
            master_rdata_valids = [master_rdata_valid | ((arbiter.grant == nm) & bank.rdata_valid)
                for nm, master_rdata_valid in enumerate(master_rdata_valids)]

        # Delay write/read signals based on their latency
        for nm, master_wdata_ready in enumerate(master_wdata_readys):
            for i in range(self.write_latency):
                new_master_wdata_ready = Signal()
                self.sync += new_master_wdata_ready.eq(master_wdata_ready)
                master_wdata_ready = new_master_wdata_ready
            master_wdata_readys[nm] = master_wdata_ready

        for nm, master_rdata_valid in enumerate(master_rdata_valids):
            for i in range(self.read_latency):
                new_master_rdata_valid = Signal()
                self.sync += new_master_rdata_valid.eq(master_rdata_valid)
                master_rdata_valid = new_master_rdata_valid
            master_rdata_valids[nm] = master_rdata_valid

        for master, master_ready in zip(self.masters, master_readys):
            self.comb += master.cmd.ready.eq(master_ready)
        for master, master_wdata_ready in zip(self.masters, master_wdata_readys):
            self.comb += master.wdata.ready.eq(master_wdata_ready)
        for master, master_rdata_valid in zip(self.masters, master_rdata_valids):
            self.comb += master.rdata.valid.eq(master_rdata_valid)

        # Route data writes ------------------------------------------------------------------------
        wdata_cases = {}
        for nm, master in enumerate(self.masters):
            wdata_cases[2**nm] = [
                controller.wdata.eq(master.wdata.data),
                controller.wdata_we.eq(master.wdata.we)
            ]
        wdata_cases["default"] = [
            controller.wdata.eq(0),
            controller.wdata_we.eq(0)
        ]
        self.comb += Case(Cat(*master_wdata_readys), wdata_cases)

        # Route data reads -------------------------------------------------------------------------
        for master in self.masters:
            self.comb += master.rdata.data.eq(controller.rdata)

class LiteDRAMCore(Module, AutoCSR):
    def __init__(self, phy, geom_settings, timing_settings, clk_freq, **kwargs):
        self.submodules.dfii = DFIInjector(
            addressbits = geom_settings.addressbits,
            bankbits    = geom_settings.bankbits,
            nranks      = phy.settings.nranks,
            databits    = phy.settings.dfi_databits,
            nphases     = phy.settings.nphases)
        self.comb += self.dfii.master.connect(phy.dfi)

        self.submodules.controller = controller = LiteDRAMController(
            phy_settings    = phy.settings,
            geom_settings   = geom_settings,
            timing_settings = timing_settings,
            clk_freq        = clk_freq,
            **kwargs)
        self.comb += controller.dfi.connect(self.dfii.slave)

        self.submodules.crossbar = LiteDRAMCrossbar(controller.interface)

cmds = {
    "PRECHARGE_ALL": "DFII_COMMAND_RAS|DFII_COMMAND_WE|DFII_COMMAND_CS",
    "MODE_REGISTER": "DFII_COMMAND_RAS|DFII_COMMAND_CAS|DFII_COMMAND_WE|DFII_COMMAND_CS",
    "AUTO_REFRESH":  "DFII_COMMAND_RAS|DFII_COMMAND_CAS|DFII_COMMAND_CS",
    "UNRESET":       "DFII_CONTROL_ODT|DFII_CONTROL_RESET_N",
    "CKE":           "DFII_CONTROL_CKE|DFII_CONTROL_ODT|DFII_CONTROL_RESET_N"
}

def get_sdr_phy_init_sequence(phy_settings, timing_settings):
    cl = phy_settings.cl
    bl = phy_settings.nphases
    mr = log2_int(bl) + (cl << 4)
    reset_dll = 1 << 8

    init_sequence = [
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 20000),
        ("Precharge All",  0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Load Mode Register / Reset DLL, CL={0:d}, BL={1:d}".format(cl, bl), mr + reset_dll, 0, cmds["MODE_REGISTER"], 200),
        ("Precharge All", 0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Load Mode Register / CL={0:d}, BL={1:d}".format(cl, bl), mr, 0, cmds["MODE_REGISTER"], 200)
    ]

    return init_sequence, None

def get_ddr_phy_init_sequence(phy_settings, timing_settings):
    cl  = phy_settings.cl
    bl  = 4
    mr  = log2_int(bl) + (cl << 4)
    emr = 0
    reset_dll = 1 << 8

    init_sequence = [
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 20000),
        ("Precharge All",  0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Load Extended Mode Register", emr, 1, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register / Reset DLL, CL={0:d}, BL={1:d}".format(cl, bl), mr + reset_dll, 0, cmds["MODE_REGISTER"], 200),
        ("Precharge All", 0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Load Mode Register / CL={0:d}, BL={1:d}".format(cl, bl), mr, 0, cmds["MODE_REGISTER"], 200)
    ]

    return init_sequence, None

def get_lpddr_phy_init_sequence(phy_settings, timing_settings):
    cl  = phy_settings.cl
    bl  = 4
    mr  = log2_int(bl) + (cl << 4)
    emr = 0
    reset_dll = 1 << 8

    init_sequence = [
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 20000),
        ("Precharge All",  0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Load Extended Mode Register", emr, 2, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register / Reset DLL, CL={0:d}, BL={1:d}".format(cl, bl), mr + reset_dll, 0, cmds["MODE_REGISTER"], 200),
        ("Precharge All", 0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Load Mode Register / CL={0:d}, BL={1:d}".format(cl, bl), mr, 0, cmds["MODE_REGISTER"], 200)
    ]

    return init_sequence, None

def get_ddr2_phy_init_sequence(phy_settings, timing_settings):
    cl   = phy_settings.cl
    bl   = 4
    wr   = 2
    mr   = log2_int(bl) + (cl << 4) + (wr << 9)
    emr  = 0
    emr2 = 0
    emr3 = 0
    ocd  = 7 << 7
    reset_dll = 1 << 8

    init_sequence = [
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 20000),
        ("Precharge All",  0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Load Extended Mode Register 3", emr3, 3, cmds["MODE_REGISTER"], 0),
        ("Load Extended Mode Register 2", emr2, 2, cmds["MODE_REGISTER"], 0),
        ("Load Extended Mode Register", emr, 1, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register / Reset DLL, CL={0:d}, BL={1:d}".format(cl, bl), mr + reset_dll, 0, cmds["MODE_REGISTER"], 200),
        ("Precharge All", 0x0400, 0, cmds["PRECHARGE_ALL"], 0),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Auto Refresh", 0x0, 0, cmds["AUTO_REFRESH"], 4),
        ("Load Mode Register / CL={0:d}, BL={1:d}".format(cl, bl), mr, 0, cmds["MODE_REGISTER"], 200),
        ("Load Extended Mode Register / OCD Default", emr+ocd, 1, cmds["MODE_REGISTER"], 0),
        ("Load Extended Mode Register / OCD Exit", emr, 1, cmds["MODE_REGISTER"], 0),
    ]

    return init_sequence, None

def get_ddr3_phy_init_sequence(phy_settings, timing_settings):
    cl  = phy_settings.cl
    bl  = 8
    cwl = phy_settings.cwl

    def format_mr0(bl, cl, wr, dll_reset):
        bl_to_mr0 = {
            4: 0b10,
            8: 0b00
        }
        cl_to_mr0 = {
             5: 0b0010,
             6: 0b0100,
             7: 0b0110,
             8: 0b1000,
             9: 0b1010,
            10: 0b1100,
            11: 0b1110,
            12: 0b0001,
            13: 0b0011,
            14: 0b0101
        }
        wr_to_mr0 = {
            16: 0b000,
             5: 0b001,
             6: 0b010,
             7: 0b011,
             8: 0b100,
            10: 0b101,
            12: 0b110,
            14: 0b111
        }
        mr0 = bl_to_mr0[bl]
        mr0 |= (cl_to_mr0[cl] & 1) << 2
        mr0 |= ((cl_to_mr0[cl] >> 1) & 0b111) << 4
        mr0 |= dll_reset << 8
        mr0 |= wr_to_mr0[wr] << 9
        return mr0

    def format_mr1(ron, rtt_nom):
        mr1 = ((ron >> 0) & 1) << 1
        mr1 |= ((ron >> 1) & 1) << 5
        mr1 |= ((rtt_nom >> 0) & 1) << 2
        mr1 |= ((rtt_nom >> 1) & 1) << 6
        mr1 |= ((rtt_nom >> 2) & 1) << 9
        return mr1

    def format_mr2(cwl, rtt_wr):
        mr2 = (cwl-5) << 3
        mr2 |= rtt_wr << 9
        return mr2

    z_to_rtt_nom = {
        "disabled" : 0,
        "60ohm"    : 1,
        "120ohm"   : 2,
        "40ohm"    : 3,
        "20ohm"    : 4,
        "30ohm"    : 5
    }

    z_to_rtt_wr = {
        "disabled" : 0,
        "60ohm"    : 1,
        "120ohm"   : 2,
    }

    z_to_ron = {
        "40ohm" : 0,
        "34ohm" : 1,
    }

    # default electrical settings (point to point)
    rtt_nom = "60ohm"
    rtt_wr  = "60ohm"
    ron     = "34ohm"

    # override electrical settings if specified
    if hasattr(phy_settings, "rtt_nom"):
        rtt_nom = phy_settings.rtt_nom
    if hasattr(phy_settings, "rtt_wr"):
        rtt_wr = phy_settings.rtt_wr
    if hasattr(phy_settings, "ron"):
        ron = phy_settings.ron

    wr  = max(timing_settings.tWTR*phy_settings.nphases, 5) # >= ceiling(tWR/tCK)
    mr0 = format_mr0(bl, cl, wr, 1)
    mr1 = format_mr1(z_to_ron[ron], z_to_rtt_nom[rtt_nom])
    mr2 = format_mr2(cwl, z_to_rtt_wr[rtt_wr])
    mr3 = 0

    init_sequence = [
        ("Release reset", 0x0000, 0, cmds["UNRESET"], 50000),
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 10000),
        ("Load Mode Register 2, CWL={0:d}".format(cwl), mr2, 2, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 3", mr3, 3, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 1", mr1, 1, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 0, CL={0:d}, BL={1:d}".format(cl, bl), mr0, 0, cmds["MODE_REGISTER"], 200),
        ("ZQ Calibration", 0x0400, 0, "DFII_COMMAND_WE|DFII_COMMAND_CS", 200),
    ]

    return init_sequence, mr1

def get_ddr4_phy_init_sequence(phy_settings, timing_settings):
    cl  = phy_settings.cl
    bl  = 8
    cwl = phy_settings.cwl

    def format_mr0(bl, cl, wr, dll_reset):
        bl_to_mr0 = {
            4: 0b10,
            8: 0b00
        }
        cl_to_mr0 = {
             9: 0b00000,
            10: 0b00001,
            11: 0b00010,
            12: 0b00011,
            13: 0b00100,
            14: 0b00101,
            15: 0b00110,
            16: 0b00111,
            18: 0b01000,
            20: 0b01001,
            22: 0b01010,
            24: 0b01011,
            23: 0b01100,
            17: 0b01101,
            19: 0b01110,
            21: 0b01111,
            25: 0b10000,
            26: 0b10001,
            27: 0b10010,
            28: 0b10011,
            29: 0b10100,
            30: 0b10101,
            31: 0b10110,
            32: 0b10111,
        }
        wr_to_mr0 = {
            10: 0b0000,
            12: 0b0001,
            14: 0b0010,
            16: 0b0011,
            18: 0b0100,
            20: 0b0101,
            24: 0b0110,
            22: 0b0111,
            26: 0b1000,
            28: 0b1001,
        }
        mr0 = bl_to_mr0[bl]
        mr0 |= (cl_to_mr0[cl] & 0b1) << 2
        mr0 |= ((cl_to_mr0[cl] >> 1) & 0b111) << 4
        mr0 |= ((cl_to_mr0[cl] >> 4) & 0b1) << 12
        mr0 |= dll_reset << 8
        mr0 |= (wr_to_mr0[wr] & 0b111) << 9
        mr0 |= (wr_to_mr0[wr] >> 3) << 13
        return mr0

    def format_mr1(dll_enable, ron, rtt_nom):
        mr1 = dll_enable
        mr1 |= ((ron >> 0) & 0b1) << 1
        mr1 |= ((ron >> 1) & 0b1) << 2
        mr1 |= ((rtt_nom >> 0) & 0b1) << 8
        mr1 |= ((rtt_nom >> 1) & 0b1) << 9
        mr1 |= ((rtt_nom >> 2) & 0b1) << 10
        return mr1

    def format_mr2(cwl, rtt_wr):
        cwl_to_mr2 = {
             9: 0b000,
            10: 0b001,
            11: 0b010,
            12: 0b011,
            14: 0b100,
            16: 0b101,
            18: 0b110,
            20: 0b111
        }
        mr2 = cwl_to_mr2[cwl] << 3
        mr2 |= rtt_wr << 9
        return mr2

    def format_mr3(fine_refresh_mode):
        fine_refresh_mode_to_mr3 = {
            "1x": 0b000,
            "2x": 0b001,
            "4x": 0b010
        }
        mr3 = fine_refresh_mode_to_mr3[fine_refresh_mode] << 6
        return mr3

    def format_mr6(tccd):
        tccd_to_mr6 = {
            4: 0b000,
            5: 0b001,
            6: 0b010,
            7: 0b011,
            8: 0b100
        }
        mr6 = tccd_to_mr6[tccd] << 10
        return mr6

    z_to_rtt_nom = {
        "disabled" : 0b000,
        "60ohm"    : 0b001,
        "120ohm"   : 0b010,
        "40ohm"    : 0b011,
        "240ohm"   : 0b100,
        "48ohm"    : 0b101,
        "80ohm"    : 0b110,
        "34ohm"    : 0b111
    }

    z_to_rtt_wr = {
        "disabled" : 0b000,
        "120ohm"   : 0b001,
        "240ohm"   : 0b010,
        "high-z"   : 0b011,
        "80ohm"    : 0b100,
    }

    z_to_ron = {
        "34ohm" : 0b00,
        "48ohm" : 0b01,
    }

    # default electrical settings (point to point)
    rtt_nom = "40ohm"
    rtt_wr  = "120ohm"
    ron     = "34ohm"

    # override electrical settings if specified
    if hasattr(phy_settings, "rtt_nom"):
        rtt_nom = phy_settings.rtt_nom
    if hasattr(phy_settings, "rtt_wr"):
        rtt_wr = phy_settings.rtt_wr
    if hasattr(phy_settings, "ron"):
        ron = phy_settings.ron

    wr  = max(timing_settings.tWTR*phy_settings.nphases, 10) # >= ceiling(tWR/tCK)
    mr0 = format_mr0(bl, cl, wr, 1)
    mr1 = format_mr1(1, z_to_ron[ron], z_to_rtt_nom[rtt_nom])
    mr2 = format_mr2(cwl, z_to_rtt_wr[rtt_wr])
    mr3 = format_mr3(timing_settings.fine_refresh_mode)
    mr4 = 0
    mr5 = 0
    mr6 = format_mr6(4) # FIXME: tCCD

    rdimm_init = []
    if phy_settings.is_rdimm:
        def get_coarse_speed(tck, pll_bypass):
            # JESD82-31A page 78
            f_to_coarse_speed = {
                1600e6: 0,
                1866e6: 1,
                2133e6: 2,
                2400e6: 3,
                2666e6: 4,
                2933e6: 5,
                3200e6: 6,
            }
            if pll_bypass:
                return 7
            else:
                for f, speed in f_to_coarse_speed.items():
                        if tck >= 2/f:
                            return speed
                raise ValueError
        def get_fine_speed(tck):
            # JESD82-31A page 83
            freq = 2/tck
            fine_speed = (freq - 1240e6) // 20e6
            fine_speed = max(fine_speed, 0)
            fine_speed = min(fine_speed, 0b1100001)
            return fine_speed

        coarse_speed = get_coarse_speed(phy_settings.tck, phy_settings.rcd_pll_bypass)
        fine_speed = get_fine_speed(phy_settings.tck)

        rcd_reset = 0x060 | 0x0                          # F0RC06: command space control; 0: reset RCD

        f0rc0f = 0x0F0 | 0x4                             # F0RC05: 0 nCK latency adder

        f0rc03 = 0x030 | phy_settings.rcd_ca_cs_drive    # F0RC03: CA/CS drive strength
        f0rc04 = 0x040 | phy_settings.rcd_odt_cke_drive  # F0RC04: ODT/CKE drive strength
        f0rc05 = 0x050 | phy_settings.rcd_clk_drive      # F0RC04: ODT/CKE drive strength

        f0rc0a = 0x0A0 | coarse_speed                    # F0RC0A: coarse speed selection and PLL bypass
        f0rc3x = 0x300 | fine_speed                      # F0RC3x: fine speed selection

        rdimm_init = [
            ("Reset RCD", rcd_reset, 7, cmds["MODE_REGISTER"], 50000),
            ("Load RCD F0RC0F", f0rc0f, 7, cmds["MODE_REGISTER"], 100),
            ("Load RCD F0RC03", f0rc03, 7, cmds["MODE_REGISTER"], 100),
            ("Load RCD F0RC04", f0rc04, 7, cmds["MODE_REGISTER"], 100),
            ("Load RCD F0RC05", f0rc05, 7, cmds["MODE_REGISTER"], 100),
            ("Load RCD F0RC0A", f0rc0a, 7, cmds["MODE_REGISTER"], 100),
            ("Load RCD F0RC3X", f0rc3x, 7, cmds["MODE_REGISTER"], 100),
        ]

    init_sequence = [
        ("Release reset", 0x0000, 0, cmds["UNRESET"], 50000),
        ("Bring CKE high", 0x0000, 0, cmds["CKE"], 10000),
    ] + rdimm_init + [
        ("Load Mode Register 3", mr3, 3, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 6", mr6, 6, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 5", mr5, 5, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 4", mr4, 4, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 2, CWL={0:d}".format(cwl), mr2, 2, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 1", mr1, 1, cmds["MODE_REGISTER"], 0),
        ("Load Mode Register 0, CL={0:d}, BL={1:d}".format(cl, bl), mr0, 0, cmds["MODE_REGISTER"], 200),
        ("ZQ Calibration", 0x0400, 0, "DFII_COMMAND_WE|DFII_COMMAND_CS", 200),
    ]

    return init_sequence, mr1

def get_sdram_phy_init_sequence(phy_settings, timing_settings):
    return {
        "SDR"  : get_sdr_phy_init_sequence,
        "DDR"  : get_ddr_phy_init_sequence,
        "LPDDR": get_lpddr_phy_init_sequence,
        "DDR2" : get_ddr2_phy_init_sequence,
        "DDR3" : get_ddr3_phy_init_sequence,
        "DDR4" : get_ddr4_phy_init_sequence,
    }[phy_settings.memtype](phy_settings, timing_settings)

def get_sdram_phy_c_header(phy_settings, timing_settings):
    r = "#ifndef __GENERATED_SDRAM_PHY_H\n#define __GENERATED_SDRAM_PHY_H\n"
    r += "#include <hw/common.h>\n"
    r += "#include <generated/csr.h>\n"
    r += "\n"

    r += "#define DFII_CONTROL_SEL        0x01\n"
    r += "#define DFII_CONTROL_CKE        0x02\n"
    r += "#define DFII_CONTROL_ODT        0x04\n"
    r += "#define DFII_CONTROL_RESET_N    0x08\n"
    r += "\n"

    r += "#define DFII_COMMAND_CS         0x01\n"
    r += "#define DFII_COMMAND_WE         0x02\n"
    r += "#define DFII_COMMAND_CAS        0x04\n"
    r += "#define DFII_COMMAND_RAS        0x08\n"
    r += "#define DFII_COMMAND_WRDATA     0x10\n"
    r += "#define DFII_COMMAND_RDDATA     0x20\n"
    r += "\n"

    phytype = phy_settings.phytype.upper()
    nphases = phy_settings.nphases

    # Define PHY type and number of phases
    r += "#define SDRAM_PHY_"+phytype+"\n"
    r += "#define SDRAM_PHY_PHASES "+str(nphases)+"\n"

    # Define Read/Write Leveling capability
    if phytype in ["USDDRPHY", "USPDDRPHY", "K7DDRPHY", "V7DDRPHY"]:
        r += "#define SDRAM_PHY_WRITE_LEVELING_CAPABLE\n"
    if phytype in ["USDDRPHY", "USPDDRPHY"]:
        r += "#define SDRAM_PHY_WRITE_LEVELING_REINIT\n"
    if phytype in ["USDDRPHY", "USPDDRPHY", "A7DDRPHY", "K7DDRPHY", "V7DDRPHY", "ECP5DDRPHY"]:
        r += "#define SDRAM_PHY_READ_LEVELING_CAPABLE\n"

    # Define number of modules/delays/bitslips
    if phytype in ["USDDRPHY", "USPDDRPHY"]:
        r += "#define SDRAM_PHY_MODULES DFII_PIX_DATA_BYTES/2\n"
        r += "#define SDRAM_PHY_DELAYS 512\n"
        r += "#define SDRAM_PHY_BITSLIPS 16\n"
    elif phytype in ["A7DDRPHY", "K7DDRPHY", "V7DDRPHY"]:
        r += "#define SDRAM_PHY_MODULES DFII_PIX_DATA_BYTES/2\n"
        r += "#define SDRAM_PHY_DELAYS 32\n"
        r += "#define SDRAM_PHY_BITSLIPS 16\n"
    elif phytype in ["ECP5DDRPHY"]:
        r += "#define SDRAM_PHY_MODULES DFII_PIX_DATA_BYTES/4\n"
        r += "#define SDRAM_PHY_DELAYS 8\n"
        r += "#define SDRAM_PHY_BITSLIPS 4\n"

    if phy_settings.is_rdimm:
        assert phy_settings.memtype == "DDR4"
        r += "#define SDRAM_PHY_DDR4_RDIMM\n"

    r += "\n"

    r += "static void cdelay(int i);\n"

    # commands_px functions
    for n in range(nphases):
        r += """
__attribute__((unused)) static void command_p{n}(int cmd)
{{
    sdram_dfii_pi{n}_command_write(cmd);
    sdram_dfii_pi{n}_command_issue_write(1);
}}""".format(n=str(n))
    r += "\n\n"

    # rd/wr access macros
    r += """
#define sdram_dfii_pird_address_write(X) sdram_dfii_pi{rdphase}_address_write(X)
#define sdram_dfii_piwr_address_write(X) sdram_dfii_pi{wrphase}_address_write(X)
#define sdram_dfii_pird_baddress_write(X) sdram_dfii_pi{rdphase}_baddress_write(X)
#define sdram_dfii_piwr_baddress_write(X) sdram_dfii_pi{wrphase}_baddress_write(X)
#define command_prd(X) command_p{rdphase}(X)
#define command_pwr(X) command_p{wrphase}(X)
""".format(rdphase=str(phy_settings.rdphase), wrphase=str(phy_settings.wrphase))
    r += "\n"

    #
    # sdrrd/sdrwr functions utilities
    #
    r += "#define DFII_PIX_DATA_SIZE CSR_SDRAM_DFII_PI0_WRDATA_SIZE\n"
    sdram_dfii_pix_wrdata_addr = []
    for n in range(nphases):
        sdram_dfii_pix_wrdata_addr.append("CSR_SDRAM_DFII_PI{n}_WRDATA_ADDR".format(n=n))
    r += """
const unsigned long sdram_dfii_pix_wrdata_addr[SDRAM_PHY_PHASES] = {{
\t{sdram_dfii_pix_wrdata_addr}
}};
""".format(sdram_dfii_pix_wrdata_addr=",\n\t".join(sdram_dfii_pix_wrdata_addr))

    sdram_dfii_pix_rddata_addr = []
    for n in range(nphases):
        sdram_dfii_pix_rddata_addr.append("CSR_SDRAM_DFII_PI{n}_RDDATA_ADDR".format(n=n))
    r += """
const unsigned long sdram_dfii_pix_rddata_addr[SDRAM_PHY_PHASES] = {{
\t{sdram_dfii_pix_rddata_addr}
}};
""".format(sdram_dfii_pix_rddata_addr=",\n\t".join(sdram_dfii_pix_rddata_addr))
    r += "\n"

    init_sequence, mr1 = get_sdram_phy_init_sequence(phy_settings, timing_settings)

    if phy_settings.memtype in ["DDR3", "DDR4"]:
        # the value of MR1 needs to be modified during write leveling
        r += "#define DDRX_MR1 {}\n\n".format(mr1)

    r += "static void init_sequence(void)\n{\n"
    for comment, a, ba, cmd, delay in init_sequence:
        invert_masks = [(0, 0), ]
        if phy_settings.is_rdimm:
            assert phy_settings.memtype == "DDR4"
            # JESD82-31A page 38
            #
            # B-side chips have certain usually-inconsequential address and BA
            # bits inverted by the RCD to reduce SSO current. For mode register
            # writes, however, we must compensate for this. BG[1] also directs
            # writes either to the A side (BG[1]=0) or B side (BG[1]=1)
            #
            # The 'ba != 7' is because we don't do this to writes to the RCD
            # itself.
            if ba != 7:
                invert_masks.append((0b10101111111000, 0b1111))

        for a_inv, ba_inv in invert_masks:
            r += "\t/* {0} */\n".format(comment)
            r += "\tsdram_dfii_pi0_address_write({0:#x});\n".format(a ^ a_inv)
            r += "\tsdram_dfii_pi0_baddress_write({0:d});\n".format(ba ^ ba_inv)
            if cmd[:12] == "DFII_CONTROL":
                r += "\tsdram_dfii_control_write({0});\n".format(cmd)
            else:
                r += "\tcommand_p0({0});\n".format(cmd)
            if delay:
                r += "\tcdelay({0:d});\n".format(delay)
            r += "\n"
    r += "}\n"

    r += "#endif\n"

    return r

def get_sdram_phy_py_header(phy_settings, timing_settings):
    r = ""
    r += "dfii_control_sel     = 0x01\n"
    r += "dfii_control_cke     = 0x02\n"
    r += "dfii_control_odt     = 0x04\n"
    r += "dfii_control_reset_n = 0x08\n"
    r += "\n"
    r += "dfii_command_cs     = 0x01\n"
    r += "dfii_command_we     = 0x02\n"
    r += "dfii_command_cas    = 0x04\n"
    r += "dfii_command_ras    = 0x08\n"
    r += "dfii_command_wrdata = 0x10\n"
    r += "dfii_command_rddata = 0x20\n"
    r += "\n"

    init_sequence, mr1 = get_sdram_phy_init_sequence(phy_settings, timing_settings)

    if mr1 is not None:
        r += "ddrx_mr1 = 0x{:x}\n".format(mr1)
        r += "\n"

    r += "init_sequence = [\n"
    for comment, a, ba, cmd, delay in init_sequence:
        r += "    "
        r += "(\"" + comment + "\", "
        r += str(a) + ", "
        r += str(ba) + ", "
        r += cmd.lower() + ", "
        r += str(delay) + "),"
        r += "\n"
    r += "]\n"
    return r

class LiteDRAMNativePortCDC(Module):
    def __init__(self, port_from, port_to,
                 cmd_depth   = 4,
                 wdata_depth = 16,
                 rdata_depth = 16):
        assert port_from.address_width == port_to.address_width
        assert port_from.data_width    == port_to.data_width
        assert port_from.mode          == port_to.mode

        address_width     = port_from.address_width
        data_width        = port_from.data_width
        mode              = port_from.mode
        clock_domain_from = port_from.clock_domain
        clock_domain_to   = port_to.clock_domain

        cmd_fifo = AsyncFIFO(
            [("we", 1), ("addr", address_width)], cmd_depth)
        cmd_fifo = ClockDomainsRenamer(
            {"write": clock_domain_from,
             "read":  clock_domain_to})(cmd_fifo)
        self.submodules += cmd_fifo
        self.submodules += Pipeline(
            port_from.cmd, cmd_fifo, port_to.cmd)

        if mode == "write" or mode == "both":
            wdata_fifo = AsyncFIFO(
                [("data", data_width), ("we", data_width//8)], wdata_depth)
            wdata_fifo = ClockDomainsRenamer(
                {"write": clock_domain_from,
                 "read":  clock_domain_to})(wdata_fifo)
            self.submodules += wdata_fifo
            self.submodules += Pipeline(
                port_from.wdata, wdata_fifo, port_to.wdata)

        if mode == "read" or mode == "both":
            rdata_fifo = AsyncFIFO([("data", data_width)], rdata_depth)
            rdata_fifo = ClockDomainsRenamer(
                {"write": clock_domain_to,
                 "read":  clock_domain_from})(rdata_fifo)
            self.submodules += rdata_fifo
            self.submodules += Pipeline(
                port_to.rdata, rdata_fifo, port_from.rdata)

class LiteDRAMNativePortDownConverter(Module):
    """LiteDRAM port DownConverter

    This module reduces user port data width to fit controller data width.
    With N = port_from.data_width/port_to.data_width:
    - Address is adapted (multiplied by N + internal increments)
    - A write from the user is splitted and generates N writes to the
    controller.
    - A read from the user generates N reads to the controller and returned
      datas are regrouped in a single data presented to the user.
    """
    def __init__(self, port_from, port_to, reverse=False):
        assert port_from.clock_domain == port_to.clock_domain
        assert port_from.data_width    > port_to.data_width
        assert port_from.mode         == port_to.mode
        if port_from.data_width % port_to.data_width:
            raise ValueError("Ratio must be an int")

        ratio = port_from.data_width//port_to.data_width
        mode  = port_from.mode

        counter       = Signal(max=ratio)
        counter_reset = Signal()
        counter_ce    = Signal()
        self.sync += \
            If(counter_reset,
                counter.eq(0)
            ).Elif(counter_ce,
                counter.eq(counter + 1)
            )

        self.submodules.fsm = fsm = FSM(reset_state="IDLE")
        fsm.act("IDLE",
            counter_reset.eq(1),
            If(port_from.cmd.valid,
                NextState("CONVERT")
            )
        )
        fsm.act("CONVERT",
            port_to.cmd.valid.eq(1),
            port_to.cmd.we.eq(port_from.cmd.we),
            port_to.cmd.addr.eq(port_from.cmd.addr*ratio + counter),
            If(port_to.cmd.ready,
                counter_ce.eq(1),
                If(counter == ratio - 1,
                    port_from.cmd.ready.eq(1),
                    NextState("IDLE")
                )
            )
        )

        if mode == "write" or mode == "both":
            wdata_converter = StrideConverter(
                port_from.wdata.description,
                port_to.wdata.description,
                reverse=reverse)
            self.submodules += wdata_converter
            self.submodules += Pipeline(
                port_from.wdata, wdata_converter, port_to.wdata)

        if mode == "read" or mode == "both":
            rdata_converter = StrideConverter(
                port_to.rdata.description,
                port_from.rdata.description,
                reverse=reverse)
            self.submodules += rdata_converter
            self.submodules += Pipeline(
                port_to.rdata, rdata_converter, port_from.rdata)

class LiteDRAMNativeWritePortUpConverter(Module):
    # TODO: finish and remove hack
    """LiteDRAM write port UpConverter

    This module increase user port data width to fit controller data width.
    With N = port_to.data_width/port_from.data_width:
    - Address is adapted (divided by N)
    - N writes from user are regrouped in a single one to the controller
    (when possible, ie when consecutive and bursting)
    """
    def __init__(self, port_from, port_to, reverse=False):
        assert port_from.clock_domain == port_to.clock_domain
        assert port_from.data_width    < port_to.data_width
        assert port_from.mode         == port_to.mode
        assert port_from.mode         == "write"
        if port_to.data_width % port_from.data_width:
            raise ValueError("Ratio must be an int")

        ratio = port_to.data_width//port_from.data_width

        we      = Signal()
        address = Signal(port_to.address_width)

        counter       = Signal(max=ratio)
        counter_reset = Signal()
        counter_ce    = Signal()
        self.sync += \
            If(counter_reset,
                counter.eq(0)
            ).Elif(counter_ce,
                counter.eq(counter + 1)
            )

        self.submodules.fsm = fsm = FSM(reset_state="IDLE")
        fsm.act("IDLE",
            port_from.cmd.ready.eq(1),
            If(port_from.cmd.valid,
                counter_ce.eq(1),
                NextValue(we, port_from.cmd.we),
                NextValue(address, port_from.cmd.addr),
                NextState("RECEIVE")
            )
        )
        fsm.act("RECEIVE",
            port_from.cmd.ready.eq(1),
            If(port_from.cmd.valid,
                counter_ce.eq(1),
                If(counter == ratio-1,
                    NextState("GENERATE")
                )
            )
        )
        fsm.act("GENERATE",
            port_to.cmd.valid.eq(1),
            port_to.cmd.we.eq(we),
            port_to.cmd.addr.eq(address[log2_int(ratio):]),
            If(port_to.cmd.ready,
                NextState("IDLE")
            )
        )

        wdata_converter = StrideConverter(
            port_from.wdata.description,
            port_to.wdata.description,
            reverse=reverse)
        self.submodules += wdata_converter
        self.submodules += Pipeline(
            port_from.wdata,
            wdata_converter,
            port_to.wdata)

class LiteDRAMNativeReadPortUpConverter(Module):
    """LiteDRAM port UpConverter

    This module increase user port data width to fit controller data width.
    With N = port_to.data_width/port_from.data_width:
    - Address is adapted (divided by N)
    - N read from user are regrouped in a single one to the controller
    (when possible, ie when consecutive and bursting)
    """
    def __init__(self, port_from, port_to, reverse=False):
        assert port_from.clock_domain == port_to.clock_domain
        assert port_from.data_width    < port_to.data_width
        assert port_from.mode         == port_to.mode
        assert port_from.mode         == "read"
        if port_to.data_width % port_from.data_width:
            raise ValueError("Ratio must be an int")

        ratio = port_to.data_width//port_from.data_width

        # Command ----------------------------------------------------------------------------------
        cmd_buffer = SyncFIFO([("sel", ratio)], 4)
        self.submodules += cmd_buffer

        counter = Signal(max=ratio)
        counter_ce = Signal()
        self.sync += \
            If(counter_ce,
                counter.eq(counter + 1)
            )

        self.comb += \
            If(port_from.cmd.valid,
                If(counter == 0,
                    port_to.cmd.valid.eq(1),
                    port_to.cmd.addr.eq(port_from.cmd.addr[log2_int(ratio):]),
                    port_from.cmd.ready.eq(port_to.cmd.ready),
                    counter_ce.eq(port_to.cmd.ready)
                ).Else(
                    port_from.cmd.ready.eq(1),
                    counter_ce.eq(1)
                )
            )

        # TODO: fix sel
        self.comb += \
            If(port_to.cmd.valid & port_to.cmd.ready,
                cmd_buffer.sink.valid.eq(1),
                cmd_buffer.sink.sel.eq(2**ratio-1)
            )

        # Datapath ---------------------------------------------------------------------------------
        rdata_buffer    = Buffer(port_to.rdata.description)
        rdata_converter = StrideConverter(
            port_to.rdata.description,
            port_from.rdata.description,
            reverse=reverse)
        self.submodules +=  rdata_buffer, rdata_converter

        rdata_chunk       = Signal(ratio, reset=1)
        rdata_chunk_valid = Signal()
        self.sync += \
            If(rdata_converter.source.valid &
               rdata_converter.source.ready,
                rdata_chunk.eq(Cat(rdata_chunk[ratio-1], rdata_chunk[:ratio-1]))
            )

        self.comb += [
            port_to.rdata.connect(rdata_buffer.sink),
            rdata_buffer.source.connect(rdata_converter.sink),
            rdata_chunk_valid.eq((cmd_buffer.source.sel & rdata_chunk) != 0),
            If(port_from.flush,
                rdata_converter.source.ready.eq(1)
            ).Elif(cmd_buffer.source.valid,
                If(rdata_chunk_valid,
                    port_from.rdata.valid.eq(rdata_converter.source.valid),
                    port_from.rdata.data.eq(rdata_converter.source.data),
                    rdata_converter.source.ready.eq(port_from.rdata.ready)
                ).Else(
                    rdata_converter.source.ready.eq(1)
                )
            ),
            cmd_buffer.source.ready.eq(
                rdata_converter.source.ready & rdata_chunk[ratio-1])
        ]

class LiteDRAMNativePortConverter(Module):
    def __init__(self, port_from, port_to, reverse=False):
        assert port_from.clock_domain == port_to.clock_domain
        assert port_from.mode         == port_to.mode

        mode = port_from.mode

        if port_from.data_width > port_to.data_width:
            converter = LiteDRAMNativePortDownConverter(port_from, port_to, reverse)
            self.submodules += converter
        elif port_from.data_width < port_to.data_width:
            if mode == "write":
                converter = LiteDRAMNativeWritePortUpConverter(port_from, port_to, reverse)
            elif mode == "read":
                converter = LiteDRAMNativeReadPortUpConverter(port_from, port_to, reverse)
            else:
                raise NotImplementedError
            self.submodules += converter
        else:
            self.comb += [
                port_from.cmd.connect(port_to.cmd),
                port_from.wdata.connect(port_to.wdata),
                port_to.rdata.connect(port_from.rdata)
            ]

class LiteDRAMWishbone2Native(Module):
    def __init__(self, wishbone, port, base_address=0x00000000):
        wishbone_data_width = len(wishbone.dat_w)
        port_data_width     = 2**int(math.log2(len(port.wdata.data))) # Round to lowest power 2
        assert wishbone_data_width >= port_data_width

        adr_offset = base_address >> log2_int(port.data_width//8)

        # Write Datapath ---------------------------------------------------------------------------
        wdata_converter = StrideConverter(
            [("data", wishbone_data_width), ("we", wishbone_data_width//8)],
            [("data", port_data_width),     ("we", port_data_width//8)],
        )
        self.submodules += wdata_converter
        self.comb += [
            wdata_converter.sink.valid.eq(wishbone.cyc & wishbone.stb & wishbone.we),
            wdata_converter.sink.data.eq(wishbone.dat_w),
            wdata_converter.sink.we.eq(wishbone.sel),
            wdata_converter.source.connect(port.wdata)
        ]

        # Read Datapath ----------------------------------------------------------------------------
        rdata_converter = StrideConverter(
            [("data", port_data_width)],
            [("data", wishbone_data_width)],
        )
        self.submodules += rdata_converter
        self.comb += [
            port.rdata.connect(rdata_converter.sink),
            rdata_converter.source.ready.eq(1),
            wishbone.dat_r.eq(rdata_converter.source.data),
        ]

        # Control ----------------------------------------------------------------------------------
        ratio = wishbone_data_width//port_data_width
        count = Signal(max=max(ratio, 2))
        self.submodules.fsm = fsm = FSM(reset_state="CMD")
        fsm.act("CMD",
            port.cmd.valid.eq(wishbone.cyc & wishbone.stb),
            port.cmd.we.eq(wishbone.we),
            port.cmd.addr.eq(wishbone.adr*ratio + count - adr_offset),
            If(port.cmd.valid & port.cmd.ready,
                NextValue(count, count + 1),
                If(count == (ratio - 1),
                    NextValue(count, 0),
                    If(wishbone.we,
                        NextState("WAIT-WRITE")
                    ).Else(
                        NextState("WAIT-READ")
                    )
                )
            )
        )
        fsm.act("WAIT-WRITE",
            If(wdata_converter.sink.ready,
                wishbone.ack.eq(1),
                NextState("CMD")
            )
        )
        fsm.act("WAIT-READ",
            If(rdata_converter.source.valid,
               wishbone.ack.eq(1),
               NextState("CMD")
            )
        )

_technology_timings = ["tREFI", "tWTR", "tCCD", "tRRD", "tZQCS"]

class _TechnologyTimings(Settings):
    def __init__(self, tREFI, tWTR, tCCD, tRRD, tZQCS=None):
        self.set_attributes(locals())

_speedgrade_timings = ["tRP", "tRCD", "tWR", "tRFC", "tFAW", "tRAS"]

class _SpeedgradeTimings(Settings):
    def __init__(self, tRP, tRCD, tWR, tRFC, tFAW, tRAS):
        self.set_attributes(locals())

def _read_field(byte, nbits, shift):
    mask = 2**nbits - 1
    return (byte & (mask << shift)) >> shift

def _twos_complement(value, nbits):
    if value & (1 << (nbits - 1)):
        value -= (1 << nbits)
    return value

def _word(msb, lsb):
    return (msb << 8) | lsb

# most signifficant (upper) / least signifficant (lower) nibble
def _msn(byte):
    return _read_field(byte, nbits=4, shift=4)

def _lsn(byte):
    return _read_field(byte, nbits=4, shift=0)

class SDRAMModule:
    """SDRAM module geometry and timings.

    SDRAM controller has to ensure that all geometry and
    timings parameters are fulfilled. Timings parameters
    can be expressed in ns, in SDRAM clock cycles or both
    and controller needs to use the greater value.

    SDRAM modules with the same geometry exist can have
    various speedgrades.
    """
    registered = False
    def __init__(self, clk_freq, rate, speedgrade=None, fine_refresh_mode=None):
        self.clk_freq      = clk_freq
        self.rate          = rate
        self.speedgrade    = speedgrade
        self.geom_settings = GeomSettings(
            bankbits = log2_int(self.nbanks),
            rowbits  = log2_int(self.nrows),
            colbits  = log2_int(self.ncols),
        )
        assert not (self.memtype != "DDR4" and fine_refresh_mode != None)
        assert fine_refresh_mode in [None, "1x", "2x", "4x"]
        if (fine_refresh_mode is None) and (self.memtype == "DDR4"):
            fine_refresh_mode = "1x"
        self.timing_settings = TimingSettings(
            tRP   = self.ns_to_cycles(self.get("tRP")),
            tRCD  = self.ns_to_cycles(self.get("tRCD")),
            tWR   = self.ns_to_cycles(self.get("tWR")),
            tREFI = self.ns_to_cycles(self.get("tREFI", fine_refresh_mode), False),
            tRFC  = self.ck_ns_to_cycles(*self.get("tRFC", fine_refresh_mode)),
            tWTR  = self.ck_ns_to_cycles(*self.get("tWTR")),
            tFAW  = None if self.get("tFAW") is None else self.ck_ns_to_cycles(*self.get("tFAW")),
            tCCD  = None if self.get("tCCD") is None else self.ck_ns_to_cycles(*self.get("tCCD")),
            tRRD  = None if self.get("tRRD") is None else self.ck_ns_to_cycles(*self.get("tRRD")),
            tRC   = None  if self.get("tRAS") is None else self.ns_to_cycles(self.get("tRP") + self.get("tRAS")),
            tRAS  = None if self.get("tRAS") is None else self.ns_to_cycles(self.get("tRAS")),
            tZQCS = None if self.get("tZQCS") is None else self.ck_ns_to_cycles(*self.get("tZQCS"))
        )
        self.timing_settings.fine_refresh_mode = fine_refresh_mode

    def get(self, name, key=None):
        r = None
        if name in _speedgrade_timings:
            if hasattr(self, "speedgrade_timings"):
                speedgrade = "default" if self.speedgrade is None else self.speedgrade
                r = getattr(self.speedgrade_timings[speedgrade], name)
            else:
                name = name + "_" + self.speedgrade if self.speedgrade is not None else name
                try:
                    r = getattr(self, name)
                except:
                    pass
        else:
            if hasattr(self, "technology_timings"):
                r = getattr(self.technology_timings, name)
            else:
                try:
                    r = getattr(self, name)
                except:
                    pass
        if (r is not None) and (key is not None):
            r = r[key]
        return r

    def ns_to_cycles(self, t, margin=True):
        clk_period_ns = 1e9/self.clk_freq
        if margin:
            margins = {
                "1:1" : 0,
                "1:2" : clk_period_ns/2,
                "1:4" : 3*clk_period_ns/4
            }
            t += margins[self.rate]
        return math.ceil(t/clk_period_ns)

    def ck_to_cycles(self, c):
        d = {
            "1:1" : 1,
            "1:2" : 2,
            "1:4" : 4
        }
        return math.ceil(c/d[self.rate])

    def ck_ns_to_cycles(self, c, t):
        c = 0 if c is None else c
        t = 0 if t is None else t
        return max(self.ck_to_cycles(c), self.ns_to_cycles(t))

class SDRAMRegisteredModule(SDRAMModule): registered = True

class DDR3Module(SDRAMModule):                     memtype = "DDR3"
class DDR3RegisteredModule(SDRAMRegisteredModule): memtype = "DDR3"

class MT41K64M16(DDR3Module):
    memtype = "DDR3"
    # geometry
    nbanks = 8
    nrows  = 8192
    ncols  = 1024
    # timings
    technology_timings = _TechnologyTimings(tREFI=64e6/8192, tWTR=(4, 7.5), tCCD=(4, None), tRRD=(4, 10), tZQCS=(64, 80))
    speedgrade_timings = {
        "800":  _SpeedgradeTimings(tRP=13.1,  tRCD=13.1,  tWR=13.1,  tRFC=(64,  None), tFAW=(None, 50), tRAS=37.5),
        "1066": _SpeedgradeTimings(tRP=13.1,  tRCD=13.1,  tWR=13.1,  tRFC=(86,  None), tFAW=(None, 50), tRAS=37.5),
        "1333": _SpeedgradeTimings(tRP=13.5,  tRCD=13.5,  tWR=13.5,  tRFC=(107, None), tFAW=(None, 45), tRAS=36),
        "1600": _SpeedgradeTimings(tRP=13.75, tRCD=13.75, tWR=13.75, tRFC=(128, None), tFAW=(None, 40), tRAS=35),
    }
    speedgrade_timings["default"] = speedgrade_timings["1600"]

class PID(IntEnum):
    # USB Packet IDs
    """
    >>> bin(PID.SETUP.value)
    '0b1101'
    >>> PID.SETUP.encode()
    'KKKKJJJJJJJJJJJJKKKKKKKKJJJJKKKK'
    >>> for p in PID:
    ...    print("%-10s" % p, "%x" % p.value, "%02x" % p.byte(), p.encode(1))
    PID.SETUP  d 2d KJJJKKJK
    PID.OUT    1 e1 KJKJKKKK
    PID.IN     9 69 KJKKJJJK
    PID.SOF    5 a5 KJJKJJKK
    PID.DATA0  3 c3 KKJKJKKK
    PID.DATA1  b 4b KKJJKJJK
    PID.DATA2  7 87 KKKJKJKK
    PID.MDATA  f 0f KKKKJKJK
    PID.ACK    2 d2 JJKJJKKK
    PID.NAK    a 5a JJKKKJJK
    PID.STALL  e 1e JJJJJKJK
    PID.NYET   6 96 JJJKKJKK
    PID.PRE    c 3c JKKKKKJK
    PID.SPLIT  8 78 JKJJJJJK
    PID.PING   4 b4 JKKJJJKK
    PID.RESERVED 0 f0 JKJKKKKK
    """

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
        # Prevent cyclic imports by importing here...
        from .utils.packet import nrzi, sync, encode_pid
        return nrzi(sync() + encode_pid(self.value), cycles)[cycles * len(sync()):]

class PIDTypes(IntEnum):
    """
    >>> # Token PIDs
    >>> PIDTypes.token(PID.SETUP), PIDTypes.data(PID.SETUP), PIDTypes.handshake(PID.SETUP)
    (True, False, False)
    >>> PIDTypes.token(PID.OUT), PIDTypes.data(PID.OUT), PIDTypes.handshake(PID.OUT)
    (True, False, False)
    >>> PIDTypes.token(PID.IN), PIDTypes.data(PID.IN), PIDTypes.handshake(PID.IN)
    (True, False, False)
    >>> PIDTypes.token(PID.SOF), PIDTypes.data(PID.SOF), PIDTypes.handshake(PID.SOF)
    (True, False, False)

    >>> # Data PIDs
    >>> PIDTypes.token(PID.DATA0), PIDTypes.data(PID.DATA0), PIDTypes.handshake(PID.DATA0)
    (False, True, False)
    >>> PIDTypes.token(PID.DATA1), PIDTypes.data(PID.DATA1), PIDTypes.handshake(PID.DATA1)
    (False, True, False)
    >>> # USB2.0 Data PIDs
    >>> PIDTypes.token(PID.DATA2), PIDTypes.data(PID.DATA2), PIDTypes.handshake(PID.DATA2)
    (False, True, False)
    >>> PIDTypes.token(PID.MDATA), PIDTypes.data(PID.MDATA), PIDTypes.handshake(PID.MDATA)
    (False, True, False)

    >>> # Handshake PIDs
    >>> PIDTypes.token(PID.ACK), PIDTypes.data(PID.ACK), PIDTypes.handshake(PID.ACK)
    (False, False, True)
    >>> PIDTypes.token(PID.NAK), PIDTypes.data(PID.NAK), PIDTypes.handshake(PID.NAK)
    (False, False, True)
    >>> PIDTypes.token(PID.STALL), PIDTypes.data(PID.STALL), PIDTypes.handshake(PID.STALL)
    (False, False, True)
    >>> # USB2.0 Handshake PIDs
    >>> PIDTypes.token(PID.NYET), PIDTypes.data(PID.NYET), PIDTypes.handshake(PID.NYET)
    (False, False, True)

    >>> # Special PIDs
    >>> PIDTypes.token(PID.PRE), PIDTypes.data(PID.PRE), PIDTypes.handshake(PID.PRE)
    (False, False, False)
    """

    TOKEN     = 0b0001
    DATA      = 0b0011
    HANDSHAKE = 0b0010
    SPECIAL   = 0b0000

    TYPE_MASK = 0b0011

    @staticmethod
    def token(p):
        assert isinstance(p, PID), repr(p)
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.TOKEN

    @staticmethod
    def data(p):
        assert isinstance(p, PID), repr(p)
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.DATA

    @staticmethod
    def handshake(p):
        assert isinstance(p, PID), repr(p)
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.HANDSHAKE

    @staticmethod
    def special(p):
        assert isinstance(p, PID), repr(p)
        return (p & PIDTypes.TYPE_MASK) == PIDTypes.SPECIAL

class Raw(Instance.PreformattedParam):
    def __init__(self, value):
        self.value = value

class IoBuf(Module):
    def __init__(self, usbp_pin, usbn_pin, usb_pullup_pin=None):
        # tx/rx io interface
        self.usb_tx_en = Signal()
        self.usb_p_tx = Signal()
        self.usb_n_tx = Signal()

        self.usb_p_rx = Signal()
        self.usb_n_rx = Signal()

        self.usb_p_rx_io = Signal()
        self.usb_n_rx_io = Signal()

        usb_p_t = TSTriple()
        usb_n_t = TSTriple()

        self.specials += usb_p_t.get_tristate(usbp_pin)
        self.specials += usb_n_t.get_tristate(usbn_pin)

        self.usb_pullup = Signal()
        if usb_pullup_pin is not None:
            self.comb += [
                usb_pullup_pin.eq(self.usb_pullup),
            ]

        usb_tx_en = Signal()
        usb_p_tx = Signal()
        usb_n_tx = Signal()

        self.sync.usb_48 += [
             usb_tx_en.eq(self.usb_tx_en),
        ]

        # Add IO buffers for outputs
        self.specials += Instance('OFS1P3BX',
            i_D=self.usb_p_tx,
            i_SCLK=ClockSignal('usb_48'),
            i_SP=1,
            i_PD=0,
            o_Q=usb_p_tx,
        )
        self.specials += Instance('OFS1P3BX',
            i_D=self.usb_n_tx,
            i_SCLK=ClockSignal('usb_48'),
            i_SP=1,
            i_PD=0,
            o_Q=usb_n_tx,
        )

        # Use IO buffers on input
        usb_p_rx_ = Signal()
        usb_n_rx_ = Signal()
        usb_p_t_i = Signal()
        usb_n_t_i = Signal()
        self.specials += Instance('IFS1P3BX',
            i_D=usb_p_t.i,
            i_SCLK=ClockSignal('usb_48'),
            i_SP=1,
            i_PD=0,
            o_Q=usb_p_rx_,
        )
        self.sync.usb_48 += usb_p_t_i.eq(usb_p_rx_)

        self.specials += Instance('IFS1P3BX',
            i_D=usb_n_t.i,
            i_SCLK=ClockSignal('usb_48'),
            i_SP=1,
            i_PD=0,
            o_Q=usb_n_rx_,
        )
        self.sync.usb_48 += usb_n_t_i.eq(usb_n_rx_)

        #######################################################################
        #######################################################################
        #### Mux the USB +/- pair with the TX and RX paths
        #######################################################################
        #######################################################################
        #self.specials += [
            #MultiReg(usb_p_t.i, usb_p_t_i),
            #MultiReg(usb_n_t.i, usb_n_t_i)
        #]

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

class FakeIoBuf(Module):
    def __init__(self):
        self.usb_pullup = Signal()

        self.usb_p = Signal()
        self.usb_n = Signal()

        self.usb_tx_en = Signal()
        self.usb_p_tx = Signal()
        self.usb_n_tx = Signal()

        self.usb_p_rx = Signal()
        self.usb_n_rx = Signal()

        self.usb_p_rx_io = Signal()
        self.usb_n_rx_io = Signal()

        self.comb += [
            If(self.usb_tx_en,
                self.usb_p_rx.eq(0b1),
                self.usb_n_rx.eq(0b0)
            ).Else(
                self.usb_p_rx.eq(self.usb_p_rx_io),
                self.usb_n_rx.eq(self.usb_n_rx_io)
            ),
        ]

        self.comb += [
            If(self.usb_tx_en,
                self.usb_p.eq(self.usb_p_tx),
                self.usb_n.eq(self.usb_n_tx),
            ).Else(
                self.usb_p.eq(self.usb_p_rx),
                self.usb_n.eq(self.usb_n_rx),
            ),
        ]

    def recv(self, v):
        tx_en = yield self.usb_tx_en
        assert not tx_en, "Currently transmitting!"

        if v == '0' or v == '_':
            # SE0 - both lines pulled low
            yield self.usb_p_rx_io.eq(0)
            yield self.usb_n_rx_io.eq(0)
        elif v == '1':
            # SE1 - illegal, should never occur
            yield self.usb_p_rx_io.eq(1)
            yield self.usb_n_rx_io.eq(1)
        elif v == '-' or v == 'I':
            # Idle
            yield self.usb_p_rx_io.eq(1)
            yield self.usb_n_rx_io.eq(0)
        elif v == 'J':
            yield self.usb_p_rx_io.eq(1)
            yield self.usb_n_rx_io.eq(0)
        elif v == 'K':
            yield self.usb_p_rx_io.eq(0)
            yield self.usb_n_rx_io.eq(1)
        else:
            assert False, "Unknown value: %s" % v

    def current(self):
        usb_p = yield self.usb_p
        usb_n = yield self.usb_n
        values = (usb_p, usb_n)

        if values == (0, 0):
            return '_'
        elif values == (1, 1):
            return '1'
        elif values == (1, 0):
            return 'J'
        elif values == (0, 1):
            return 'K'
        else:
            assert False, values

@ResetInserter()
class RxBitstuffRemover(Module):
    """RX Bitstuff Removal

    Long sequences of 1's would cause the receiver to lose it's lock on the
    transmitter's clock.  USB solves this with bitstuffing.  A '0' is stuffed
    after every 6 consecutive 1's.  This extra bit is required to recover the
    clock, but it should not be passed on to higher layers in the device.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 7.1.9
    https://en.wikipedia.org/wiki/Bit_stuffing

    Clock Domain
    ------------
    usb_12 : 12MHz

    Input Ports
    ------------
    i_valid : Signal(1)
        Qualifier for all of the input signals.  Indicates one bit of valid
        data is present on the inputs.

    i_data : Signal(1)
        Decoded data bit from USB bus.
        Qualified by valid.

    Output Ports
    ------------
    o_data : Signal(1)
        Decoded data bit from USB bus.

    o_stall : Signal(1)
        Indicates the bit stuffer just removed an extra bit, so no data available.

    o_error : Signal(1)
        Indicates there has been a bitstuff error. A bitstuff error occurs
        when there should be a stuffed '0' after 6 consecutive 1's; but instead
        of a '0', there is an additional '1'.  This is normal during IDLE, but
        should never happen within a packet.
        Qualified by valid.
    """

    def __init__(self):
        self.i_valid = Signal()
        self.i_data = Signal()

        # This state machine recognizes sequences of 6 bits and drops the 7th bit.
        # The fsm implements a counter in a series of several states.
        # This is intentional to help absolutely minimize the levels of logic used.
        self.submodules.stuff = stuff = FSM(reset_state="D0")

        drop_bit = Signal(1)

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
        self.o_data = Signal()
        self.o_error = Signal()
        self.o_stall = Signal(reset=1)

        self.sync += [
            self.o_data.eq(self.i_data),
            self.o_stall.eq(drop_bit | ~self.i_valid),
            self.o_error.eq(drop_bit & self.i_data & self.i_valid),
        ]

class RxClockDataRecovery(Module):
    """RX Clock Data Recovery module.

    RxClockDataRecovery synchronizes the USB differential pair with the FPGAs
    clocks, de-glitches the differential pair, and recovers the incoming clock
    and data.

    Clock Domain
    ------------
    usb_48 : 48MHz

    Input Ports
    -----------
    Input ports are passed in via the constructor.

    usbp_raw : Signal(1)
        Raw USB+ input from the FPGA IOs, no need to synchronize.

    usbn_raw : Signal(1)
        Raw USB- input from the FPGA IOs, no need to synchronize.

    Output Ports
    ------------
    Output ports are data members of the module. All output ports are flopped.
    The line_state_dj/dk/se0/se1 outputs are 1-hot encoded.

    line_state_valid : Signal(1)
        Asserted for one clock when the output line state is ready to be sampled.

    line_state_dj : Signal(1)
        Represents Full Speed J-state on the incoming USB data pair.
        Qualify with line_state_valid.

    line_state_dk : Signal(1)
        Represents Full Speed K-state on the incoming USB data pair.
        Qualify with line_state_valid.

    line_state_se0 : Signal(1)
        Represents SE0 on the incoming USB data pair.
        Qualify with line_state_valid.

    line_state_se1 : Signal(1)
        Represents SE1 on the incoming USB data pair.
        Qualify with line_state_valid.
    """

    def __init__(self, usbp_raw, usbn_raw):
        if False:
            #######################################################################
            # Synchronize raw USB signals
            #
            # We need to synchronize the raw USB signals with the usb_48 clock
            # domain.  MultiReg implements a multi-stage shift register that takes
            # care of this for us.  Without MultiReg we would have metastability
            # issues.
            #
            usbp = Signal(reset=1)
            usbn = Signal()

            self.specials += MultiReg(usbp_raw, usbp, n=1, reset=1)
            self.specials += MultiReg(usbn_raw, usbn, n=1)
        else:
            # Leave raw USB signals meta-stable.  The synchronizer should clean
            # them up.
            usbp = usbp_raw
            usbn = usbn_raw

        #######################################################################
        # Line State Recovery State Machine
        #
        # The receive path doesn't use a differential receiver.  Because of
        # this there is a chance that one of the differential pairs will appear
        # to have changed to the new state while the other is still in the old
        # state.  The following state machine detects transitions and waits an
        # extra sampling clock before decoding the state on the differential
        # pair.  This transition period # will only ever last for one clock as
        # long as there is no noise on the line.  If there is enough noise on
        # the line then the data may be corrupted and the packet will fail the
        # data integrity checks.
        #
        self.submodules.lsr = lsr = FSM()

        dpair = Signal(2)
        self.comb += dpair.eq(Cat(usbn, usbp))

        # output signals for use by the clock recovery stage
        line_state_dt = Signal()
        line_state_dj = Signal()
        line_state_dk = Signal()
        line_state_se0 = Signal()
        line_state_se1 = Signal()

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

        #######################################################################
        # Clock and Data Recovery
        #
        # The DT state from the line state recovery state machine is used to align to
        # transmit clock.  The line state is sampled in the middle of the bit time.
        #
        # Example of signal relationships
        # -------------------------------
        # line_state        DT  DJ  DJ  DJ  DT  DK  DK  DK  DK  DK  DK  DT  DJ  DJ  DJ
        # line_state_valid  ________----____________----____________----________----____
        # bit_phase         0   0   1   2   3   0   1   2   3   0   1   2   0   1   2
        #

        # We 4x oversample, so make the line_state_phase have 4 possible values.
        line_state_phase = Signal(2)

        self.line_state_valid = Signal()
        self.line_state_dj = Signal()
        self.line_state_dk = Signal()
        self.line_state_se0 = Signal()
        self.line_state_se1 = Signal()

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

@ResetInserter()
class RxPacketDetect(Module):
    """Packet Detection

    Full Speed packets begin with the following sequence:

        KJKJKJKK

    This raw sequence corresponds to the following data:

        00000001

    The bus idle condition is signaled with the J state:

        JJJJJJJJ

    This translates to a series of '1's since there are no transitions.  Given
    this information, it is easy to detect the beginning of a packet by looking
    for 00000001.

    The end of a packet is even easier to detect.  The end of a packet is
    signaled with two SE0 and one J.  We can just look for the first SE0 to
    detect the end of the packet.

    Packet detection can occur in parallel with bitstuff removal.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 7.1.10

    Input Ports
    ------------
    i_valid : Signal(1)
        Qualifier for all of the input signals.  Indicates one bit of valid
        data is present on the inputs.

    i_data : Signal(1)
        Decoded data bit from USB bus.
        Qualified by valid.

    i_se0 : Signal(1)
        Indicator for SE0 from USB bus.
        Qualified by valid.

    Output Ports
    ------------
    o_pkt_start : Signal(1)
        Asserted for one clock on the last bit of the sync.

    o_pkt_active : Signal(1)
        Asserted while in the middle of a packet.

    o_pkt_end : Signal(1)
        Asserted for one clock after the last data bit of a packet was received.
    """

    def __init__(self):
        self.i_valid = Signal()
        self.i_data = Signal()
        self.i_se0 = Signal()

        self.submodules.pkt = pkt = FSM()

        pkt_start = Signal()
        pkt_active = Signal()
        pkt_end = Signal()

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
        self.o_pkt_start = Signal()
        self.o_pkt_active = Signal()
        self.o_pkt_end = Signal()
        self.comb += [
            self.o_pkt_start.eq(pkt_start),
            self.o_pkt_active.eq(pkt_active),
            self.o_pkt_end.eq(pkt_end),
        ]

class RxNRZIDecoder(Module):
    """RX NRZI decoder.

    In order to ensure there are enough bit transitions for a receiver to recover
    the clock usb uses NRZI encoding.  This module processes the incoming
    dj, dk, se0, and valid signals and decodes them to data values.  It
    also pipelines the se0 signal and passes it through unmodified.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 7.1.8
    https://en.wikipedia.org/wiki/Non-return-to-zero

    Clock Domain
    ------------
    usb_48 : 48MHz

    Input Ports
    -----------
    Input ports are passed in via the constructor.

    i_valid : Signal(1)
        Qualifier for all of the input signals.  Indicates one bit of valid
        data is present on the inputs.

    i_dj : Signal(1)
        Indicates the bus is currently in a Full-Speed J-state.
        Qualified by valid.

    i_dk : Signal(1)
        Indicates the bus is currently in a Full-Speed K-state.
        Qualified by valid.

    i_se0 : Signal(1)
        Indicates the bus is currently in a SE0 state.
        Qualified by valid.

    Output Ports
    ------------
    Output ports are data members of the module. All output ports are flopped.

    o_valid : Signal(1)
        Qualifier for all of the output signals. Indicates one bit of valid
        data is present on the outputs.

    o_data : Signal(1)
        Decoded data bit from USB bus.
        Qualified by valid.

    o_se0 : Signal(1)
        Indicates the bus is currently in a SE0 state.
        Qualified by valid.
    """

    def __init__(self):
        self.i_valid = Signal()
        self.i_dj = Signal()
        self.i_dk = Signal()
        self.i_se0 = Signal()

        # pass all of the outputs through a pipe stage
        self.o_valid = Signal(1)
        self.o_data = Signal(1)
        self.o_se0 = Signal(1)

        if False:
            valid = Signal(1)
            data = Signal(1)

            # simple state machine decodes a JK transition as a '0' and no transition as a '1'.  se0 is ignored.
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
            last_data = Signal()
            self.sync += [
                If(self.i_valid,
                    last_data.eq(self.i_dk),
                    self.o_data.eq(~(self.i_dk ^ last_data)),
                    self.o_se0.eq((~self.i_dj) & (~self.i_dk)),
                ),
                self.o_valid.eq(self.i_valid),
            ]

@ResetInserter()
class RxShifter(Module):
    """RX Shifter

    A shifter is responsible for shifting in serial bits and presenting them
    as parallel data.  The shifter knows how many bits to shift and has
    controls for resetting the shifter.

    Clock Domain
    ------------
    usb_12 : 12MHz

    Parameters
    ----------
    Parameters are passed in via the constructor.

    width : int
        Number of bits to shift in.

    Input Ports
    -----------
    i_valid : Signal(1)
        Qualifier for all of the input signals.  Indicates one bit of valid
        data is present on the inputs.

    i_data : Signal(1)
        Serial input data.
        Qualified by valid.

    Output Ports
    ------------
    o_data : Signal(width)
        Shifted in data.

    o_put : Signal(1)
        Asserted for one clock once the register is full.
    """

    def __init__(self, width):
        self.i_valid = Signal()
        self.i_data = Signal()

        self.o_data = Signal(width)
        self.o_put = Signal()

        # Instead of using a counter, we will use a sentinel bit in the shift register to indicate when it is full.
        shift_reg = Signal(width+1, reset=0b1)

        self.comb += self.o_data.eq(shift_reg[0:width])
        self.sync += [
            self.o_put.eq(shift_reg[width-1] & ~shift_reg[width] & self.i_valid),
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
        self.reset = Signal()

        # 12MHz USB alignment pulse in 48MHz clock domain
        self.o_bit_strobe = Signal()

        # Reset state is J
        self.i_usbp = Signal(reset=1)
        self.i_usbn = Signal(reset=0)

        self.o_data_strobe = Signal()
        self.o_data_payload = Signal(8)

        self.o_pkt_start = Signal()
        self.o_pkt_in_progress = Signal()
        self.o_pkt_end = Signal()

        # 48MHz domain
        # Clock recovery
        clock_data_recovery = RxClockDataRecovery(self.i_usbp, self.i_usbn)
        self.submodules.clock_data_recovery = ClockDomainsRenamer("usb_48")(clock_data_recovery)
        self.comb += [
            self.o_bit_strobe.eq(clock_data_recovery.line_state_valid),
        ]

        # A reset condition is one where the device is in SE0 for more than 2.5 uS, which is ~30 bit times.
        self.o_reset = Signal()
        reset_counter = Signal(7)
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
        reset = Signal()
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

        last_reset = Signal()
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
        flag_start = Signal()
        flag_end = Signal()
        flag_valid = Signal()
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

@ResetInserter()
class TxBitstuffer(Module):
    """
    Bitstuff Insertion

    Long sequences of 1's would cause the receiver to lose it's lock on the
    transmitter's clock.  USB solves this with bitstuffing.  A '0' is stuffed
    after every 6 consecutive 1's.

    The TxBitstuffer is the only component in the transmit pipeline that can
    delay transmission of serial data.  It is therefore responsible for
    generating the bit_strobe signal that keeps the pipe moving forward.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 7.1.9
    https://en.wikipedia.org/wiki/Bit_stuffing

    Clock Domain
    ------------
    usb_12 : 48MHz

    Input Ports
    ------------
    i_data : Signal(1)
        Data bit to be transmitted on USB.

    Output Ports
    ------------
    o_data : Signal(1)
        Data bit to be transmitted on USB.

    o_stall : Signal(1)
        Used to apply backpressure on the tx pipeline.
    """

    def __init__(self):
        self.i_data = Signal()

        self.o_stall = Signal(1)
        self.o_will_stall = Signal(1)
        self.o_data = Signal(1)

        self.submodules.stuff = stuff = FSM()

        stuff_bit = Signal(1)

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

class TxNRZIEncoder(Module):
    """
    NRZI Encode

    In order to ensure there are enough bit transitions for a receiver to recover
    the clock usb uses NRZI encoding.  This module processes the incoming
    dj, dk, se0, and valid signals and decodes them to data values.  It
    also pipelines the se0 signal and passes it through unmodified.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 7.1.8
    https://en.wikipedia.org/wiki/Non-return-to-zero

    Clock Domain
    ------------
    usb_48 : 48MHz

    Input Ports
    -----------
    i_valid : Signal(1)
        Qualifies oe, data, and se0.

    i_oe : Signal(1)
        Indicates that the transmit pipeline should be driving USB.

    i_data : Signal(1)
        Data bit to be transmitted on USB. Qualified by o_valid.

    i_se0 : Signal(1)
        Overrides value of o_data when asserted and indicates that SE0 state
        should be asserted on USB. Qualified by o_valid.

    Output Ports
    ------------
    o_usbp : Signal(1)
        Raw value of USB+ line.

    o_usbn : Signal(1)
        Raw value of USB- line.

    o_oe : Signal(1)
        When asserted it indicates that the tx pipeline should be driving USB.
    """

    def __init__(self):
        self.i_valid = Signal()
        self.i_oe = Signal()
        self.i_data = Signal()

        # Simple state machine to perform NRZI encoding.
        self.submodules.nrzi = nrzi = FSM()

        usbp = Signal(1)
        usbn = Signal(1)
        oe = Signal(1)

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
        self.o_usbp = Signal(1)
        self.o_usbn = Signal(1)
        self.o_oe = Signal(1)

        self.sync += [
            self.o_oe.eq(oe),
            self.o_usbp.eq(usbp),
            self.o_usbn.eq(usbn),
        ]

@ResetInserter()
@CEInserter()
class TxShifter(Module):
    """Transmit Shifter

    TxShifter accepts parallel data and shifts it out serially.

    Parameters
    ----------
    Parameters are passed in via the constructor.

    width : int
        Width of the data to be shifted.

    Input Ports
    -----------
    Input ports are passed in via the constructor.

    i_data : Signal(width)
        Data to be transmitted.

    Output Ports
    ------------
    Output ports are data members of the module. All outputs are flopped.

    o_data : Signal(1)
        Serial data output.

    o_empty : Signal(1)
        Asserted the cycle before the shifter loads in more i_data.

    o_get : Signal(1)
        Asserted the cycle after the shifter loads in i_data.

    """

    def __init__(self, width):
        self.i_data = Signal(width)
        self.o_get = Signal(1)
        self.o_empty = Signal(1)

        self.o_data = Signal(1)

        shifter = Signal(width)
        pos = Signal(width, reset=0b1)

        empty = Signal(1)
        self.sync += [
            pos.eq(pos >> 1),
            shifter.eq(shifter >> 1),
            If(empty,
                shifter.eq(self.i_data),
                pos.eq(1 << (width-1)),
            ),
            self.o_get.eq(empty),
        ]
        self.comb += [
            empty.eq(pos[0]),
            self.o_empty.eq(empty),
            self.o_data.eq(shifter[0]),
        ]

@CEInserter()
@ResetInserter()
class TxSerialCrcGenerator(Module):
    """
    Transmit CRC Generator

    TxSerialCrcGenerator generates a running CRC.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 8.3.5
    https://en.wikipedia.org/wiki/Cyclic_redundancy_check

    Parameters
    ----------
    Parameters are passed in via the constructor.

    width : int
        Width of the CRC.

    polynomial : int
        CRC polynomial in integer form.

    initial : int
        Initial value of the CRC register before data starts shifting in.

    Input Ports
    ------------
    i_data : Signal(1)
        Serial data to generate CRC for.

    Output Ports
    ------------
    o_crc : Signal(width)
        Current CRC value.

    """

    def __init__(self, width, polynomial, initial):

        self.i_data = Signal()

        crc = Signal(width, reset=initial)
        crc_invert = Signal(1)

        self.comb += [
            crc_invert.eq(self.i_data ^ crc[width - 1])
        ]

        for i in range(width):
            rhs_data = None
            if i == 0:
                rhs_data = crc_invert
            else:
                if (polynomial >> i) & 1:
                    rhs_data = crc[i - 1] ^ crc_invert
                else:
                    rhs_data = crc[i - 1]

            self.sync += [
                crc[i].eq(rhs_data)
            ]

        self.o_crc = Signal(width)

        for i in range(width):
            self.comb += [
                self.o_crc[i].eq(1 ^ crc[width - i - 1]),
            ]

def bytes_to_int(d):
    """Convert a list of bytes to an int

    Bytes are in LSB first.

    >>> hex(bytes_to_int([0, 1]))
    '0x100'
    >>> hex(bytes_to_int([1, 2]))
    '0x201'
    """
    v = 0
    for i,d in enumerate(d):
        v |= d << (i*8)
    return v

def cols(rows):
    """
    >>> a = [
    ...  [1, 2],
    ...  ['a', 'b'],
    ...  [4, 5],
    ... ]
    >>> for c in cols(a):
    ...   print(c)
    [1, 'a', 4]
    [2, 'b', 5]
    >>> a = [
    ...  [1, 2, 3],
    ...  ['a', 'b', 'c'],
    ... ]
    >>> for c in cols(a):
    ...   print(c)
    [1, 'a']
    [2, 'b']
    [3, 'c']

    """
    all_c = []
    for ci in range(len(rows[0])):
        all_c.append([])
    for ci in range(len(rows[0])):
        for ri in range(len(rows)):
            assert len(rows[ri]) == len(all_c), "len(%r) != %i" % (rows[ri], len(all_c))
            all_c[ci].append(rows[ri][ci])
    return all_c

def lfsr_serial_shift_crc(lfsr_poly, lfsr_cur, data):
    """
    shift_by == num_data_bits
    len(data_cur) == num_data_bits
    >>> for i in range(5):
    ...   l = [0]*5; l[i] = 1
    ...   r = lfsr_serial_shift_crc(
    ...      lfsr_poly=[0,0,1,0,1], # (5, 2, 0)
    ...      lfsr_cur=l,
    ...      data=[0,0,0,0],
    ...   )
    ...   print("Min[%i] =" % i, r)
    Min[0] = [1, 0, 0, 0, 0]
    Min[1] = [0, 0, 1, 0, 1]
    Min[2] = [0, 1, 0, 1, 0]
    Min[3] = [1, 0, 1, 0, 0]
    Min[4] = [0, 1, 1, 0, 1]
    >>> for i in range(4):
    ...   d = [0]*4; d[i] = 1
    ...   r = lfsr_serial_shift_crc(
    ...      lfsr_poly=[0,0,1,0,1], # (5, 2, 0)
    ...      lfsr_cur=[0,0,0,0,0],
    ...      data=d,
    ...   )
    ...   print("Nin[%i] =" % i, r)
    Nin[0] = [0, 0, 1, 0, 1]
    Nin[1] = [0, 1, 0, 1, 0]
    Nin[2] = [1, 0, 1, 0, 0]
    Nin[3] = [0, 1, 1, 0, 1]

    """
    lfsr_poly = lfsr_poly[::-1]
    data = data[::-1]

    shift_by = len(data)
    lfsr_poly_size = len(lfsr_poly)
    assert lfsr_poly_size > 1
    assert len(lfsr_cur) == lfsr_poly_size

    lfsr_next = list(lfsr_cur)
    for j in range(shift_by):
        lfsr_upper_bit = lfsr_next[lfsr_poly_size-1]
        for i in range(lfsr_poly_size-1, 0, -1):
            if lfsr_poly[i]:
                lfsr_next[i] = lfsr_next[i-1] ^ lfsr_upper_bit ^ data[j]
            else:
                lfsr_next[i] = lfsr_next[i-1]
        lfsr_next[0] = lfsr_upper_bit ^ data[j]
    return list(lfsr_next[::-1])

def print_matrix(crc_width, cols_nin, cols_min):
    """
    >>> crc_width = 5
    >>> data_width = 4
    >>> poly_list = [0, 0, 1, 0, 1]
    >>> _, cols_nin, cols_min = build_matrix(poly_list, data_width)
    >>> print_matrix(crc_width, cols_nin, cols_min)
       0 d[ 0],      ,      , d[ 3],      , c[ 1],      ,      , c[ 4]
       1      , d[ 1],      ,      ,      ,      , c[ 2],      ,
       2 d[ 0],      , d[ 2], d[ 3],      , c[ 1],      , c[ 3], c[ 4]
       3      , d[ 1],      , d[ 3],      ,      , c[ 2],      , c[ 4]
       4      ,      , d[ 2],      , c[ 0],      ,      , c[ 3],
    """
    for i in range(crc_width):
        text_xor = []
        for j, use in enumerate(cols_nin[i]):
            if use:
                text_xor.append('d[%2i]' % j)
            else:
                text_xor.append('     ')
        for j, use in enumerate(cols_min[i]):
            if use:
                text_xor.append('c[%2i]' % j)
            else:
                text_xor.append('     ')
        print("{:4d} {}".format(i, ", ".join("{:>5s}".format(x) for x in text_xor).rstrip()))

def build_matrix(lfsr_poly, data_width):
    """
    >>> print("\\n".join(build_matrix([0,0,1,0,1], 4)[0]))
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 0, 0], [1, 0, 0, 0]) = [0, 0, 1, 0, 1]
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 0, 0], [0, 1, 0, 0]) = [0, 1, 0, 1, 0]
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 0, 0], [0, 0, 1, 0]) = [1, 0, 1, 0, 0]
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 1]) = [0, 1, 1, 0, 1]
    <BLANKLINE>
    lfsr([0, 0, 1, 0, 1], [1, 0, 0, 0, 0], [0, 0, 0, 0]) = [1, 0, 0, 0, 0]
    lfsr([0, 0, 1, 0, 1], [0, 1, 0, 0, 0], [0, 0, 0, 0]) = [0, 0, 1, 0, 1]
    lfsr([0, 0, 1, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 0]) = [0, 1, 0, 1, 0]
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 1, 0], [0, 0, 0, 0]) = [1, 0, 1, 0, 0]
    lfsr([0, 0, 1, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0]) = [0, 1, 1, 0, 1]
    <BLANKLINE>
    Mout[4] = [0, 0, 1, 0] [1, 0, 0, 1, 0]
    Mout[3] = [0, 1, 0, 1] [0, 0, 1, 0, 1]
    Mout[2] = [1, 0, 1, 1] [0, 1, 0, 1, 1]
    Mout[1] = [0, 1, 0, 0] [0, 0, 1, 0, 0]
    Mout[0] = [1, 0, 0, 1] [0, 1, 0, 0, 1]
    """
    lfsr_poly_size = len(lfsr_poly)

    # data_width*lfsr_polysize matrix == lfsr(0,Nin)
    rows_nin = []

    # (a) calculate the N values when Min=0 and Build NxM matrix
    #  - Each value is one hot encoded (there is only one bit)
    #  - IE N=4, 0x1, 0x2, 0x4, 0x8
    #  - Mout = F(Nin,Min=0)
    #  - Each row contains the results of (a)
    #  - IE row[0] == 0x1, row[1] == 0x2
    #  - Output is M-bit wide (CRC width)
    #  - Each column of the matrix represents an output bit Mout[i] as a function of Nin
    info = []
    for i in range(data_width):
        # lfsr_cur = [0,...,0] = Min
        lfsr_cur = [0,]*lfsr_poly_size
        # data = [0,..,1,..,0] = Nin
        data = [0,]*data_width
        data[i] = 1
        # Calculate the CRC
        rows_nin.append(lfsr_serial_shift_crc(lfsr_poly, lfsr_cur, data))
        info.append("lfsr(%r, %r, %r) = %r" % (lfsr_poly, lfsr_cur, data, rows_nin[-1]))
    assert len(rows_nin) == data_width
    cols_nin = cols(rows_nin)[::-1]

    # lfsr_polysize*lfsr_polysize matrix == lfsr(Min,0)
    info.append("")
    rows_min = []
    for i in range(lfsr_poly_size):
        # lfsr_cur = [0,..,1,...,0] = Min
        lfsr_cur = [0,]*lfsr_poly_size
        lfsr_cur[i] = 1
        # data = [0,..,0] = Nin
        data = [0,]*data_width
        # Calculate the crc
        rows_min.append(lfsr_serial_shift_crc(lfsr_poly, lfsr_cur, data))
        info.append("lfsr(%r, %r, %r) = %r" % (lfsr_poly, lfsr_cur, data, rows_min[-1]))
    assert len(rows_min) == lfsr_poly_size
    cols_min = cols(rows_min)[::-1]

    # (c) Calculate CRC for the M values when Nin=0 and Build MxM matrix
    #  - Each value is one hot encoded
    #  - Mout = F(Nin=0,Min)
    #  - Each row contains results from (7)
    info.append("")
    for i in range(data_width, -1, -1):
        info.append("Mout[%i] = %r %r" % (i, cols_nin[i], cols_min[i]))

    return info, cols_nin, cols_min

@ResetInserter()
class TxParallelCrcGenerator(Module):
    """
    Transmit CRC Generator

    TxParallelCrcGenerator generates a running CRC.

    https://www.pjrc.com/teensy/beta/usb20.pdf, USB2 Spec, 8.3.5
    https://en.wikipedia.org/wiki/Cyclic_redundancy_check

    Parameters
    ----------
    Parameters are passed in via the constructor.

    width : int
        Width of the CRC.

    polynomial : int
        CRC polynomial in integer form.

    initial : int
        Initial value of the CRC register before data starts shifting in.

    Input Ports
    ------------
    i_data_payload : Signal(8)
        Byte wide data to generate CRC for.

    i_data_strobe : Signal(1)
        Strobe signal for the payload.

    Output Ports
    ------------
    o_crc : Signal(width)
        Current CRC value.

    """

    def __init__(self, data_width, crc_width, polynomial, initial=0):
        self.i_data_payload = Signal(data_width)
        self.i_data_strobe = Signal()
        self.o_crc = Signal(crc_width)
        crc_dat = Signal(data_width)
        crc_cur = Signal(crc_width, reset=initial)
        crc_next = Signal(crc_width, reset_less=True)

        crc_cur_reset_bits = [int(i) for i in "{0:0{width}b}".format(crc_cur.reset.value,width=crc_width)[::-1]]

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
        assert len(poly_list) == crc_width

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

class TxCrcPipeline(Module):
    def __init__(self):
        self.i_data_payload = Signal(8)
        self.o_data_ack = Signal()
        self.o_crc16 = Signal(16)

        self.reset = reset = Signal()
        reset_n1 = Signal()
        reset_n2 = Signal()
        self.ce = ce = Signal()

        self.sync += [
            reset_n2.eq(reset_n1),
            reset_n1.eq(reset),
        ]

        self.submodules.shifter = shifter = TxShifter(width=8)
        self.comb += [
            shifter.i_data.eq(self.i_data_payload),
            shifter.reset.eq(reset),
            shifter.ce.eq(ce),
            self.o_data_ack.eq(shifter.o_get),
        ]

        self.submodules.crc = crc_calc = TxSerialCrcGenerator(
            width      = 16,
            polynomial = 0b1000000000000101,
            initial    = 0b1111111111111111,
        )
        self.comb += [
            crc_calc.i_data.eq(shifter.o_data),
            crc_calc.reset.eq(reset_n2),
            crc_calc.ce.eq(ce),
            self.o_crc16.eq(crc_calc.o_crc),
        ]

class TxPipeline(Module):
    def __init__(self):
        self.i_bit_strobe = Signal()

        self.i_data_payload = Signal(8)
        self.o_data_strobe = Signal()

        self.i_oe = Signal()

        self.o_usbp = Signal()
        self.o_usbn = Signal()
        self.o_oe = Signal()

        self.o_pkt_end = Signal()

        tx_pipeline_fsm = FSM()
        self.submodules.tx_pipeline_fsm = ClockDomainsRenamer("usb_12")(tx_pipeline_fsm)
        shifter = TxShifter(width=8)
        self.submodules.shifter = ClockDomainsRenamer("usb_12")(shifter)
        bitstuff = TxBitstuffer()
        self.submodules.bitstuff = ClockDomainsRenamer("usb_12")(bitstuff)
        nrzi = TxNRZIEncoder()
        self.submodules.nrzi = ClockDomainsRenamer("usb_48")(nrzi)

        sync_pulse = Signal(8)

        self.fit_dat = fit_dat = Signal()
        self.fit_oe  = fit_oe  = Signal()

        da_reset_shifter = Signal()
        da_reset_bitstuff = Signal() # Need to reset the bit stuffer 1 cycle after the shifter.
        stall = Signal()

        # These signals are set during the sync pulse
        sp_reset_bitstuff = Signal()
        sp_reset_shifter = Signal()
        sp_bit = Signal()
        sp_o_data_strobe = Signal()

        # 12MHz domain
        da_stalled_reset = Signal()
        bitstuff_valid_data = Signal()

        # Keep a Gray counter around to smoothly transition between states
        state_gray = Signal(2)
        state_data = Signal()
        state_sync = Signal()

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

        tx_pipeline_fsm.act('IDLE',
            If(self.i_oe,
                NextState('SEND_SYNC'),
                NextValue(sync_pulse, 1 << 7),
                NextValue(state_gray, 0b01),
            ).Else(
                NextValue(state_gray, 0b00),
            )
        )

        tx_pipeline_fsm.act('SEND_SYNC',
            NextValue(sync_pulse, sync_pulse >> 1),

            If(sync_pulse[0],
                NextState('SEND_DATA'),
                NextValue(state_gray, 0b11),
            ).Else(
                NextValue(state_gray, 0b01),
            ),
        )

        tx_pipeline_fsm.act('SEND_DATA',
            If(~self.i_oe & shifter.o_empty & ~bitstuff.o_stall,
                If(bitstuff.o_will_stall,
                    NextState('STUFF_LAST_BIT')
                ).Else(
                    NextValue(state_gray, 0b10),
                    NextState('IDLE'),
                )
            ).Else(
                NextValue(state_gray, 0b11),
            ),
        )

        tx_pipeline_fsm.act('STUFF_LAST_BIT',
            NextValue(state_gray, 0b10),
            NextState('IDLE'),
        )

        # 48MHz domain
        # NRZI encoding
        nrzi_dat = Signal()
        nrzi_oe = Signal()

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

class EndpointType(IntEnum):
    IN = 1
    OUT = 2
    BIDIR = IN | OUT

    @classmethod
    def epaddr(cls, ep_num, ep_dir):
        assert ep_dir != cls.BIDIR
        return ep_num << 1 | (ep_dir == cls.IN)

    @classmethod
    def epnum(cls, ep_addr):
        return ep_addr >> 1

    @classmethod
    def epdir(cls, ep_addr):
        if ep_addr & 0x1 == 0:
            return cls.OUT
        else:
            return cls.IN

class EndpointResponse(IntEnum):
    """
    >>> # Clearing top bit of STALL -> NAK
    >>> assert (EndpointResponse.STALL & EndpointResponse.RESET_MASK) == EndpointResponse.NAK
    """

    STALL = 0b11
    ACK   = 0b00
    NAK   = 0b01
    NONE  = 0b10

    RESET_MASK = 0b01

class PacketHeaderDecode(Module):
    def __init__(self, rx):
        self.submodules.rx = rx

        self.o_pid = Signal(4)
        self.o_addr = Signal(7)
        endp4 = Signal()
        self.o_endp = Signal(4)
        crc5 = Signal(5)
        self.o_decoded = Signal()

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

        self.i_pkt_start = Signal()
        self.o_pkt_end = Signal()

        self.i_pid = Signal(4)
        self.i_data_payload = Signal(8)
        self.i_data_ready = Signal()
        self.o_data_ack = Signal()

        o_oe12 = Signal()
        self.specials += MultiReg(tx.o_oe, o_oe12, odomain="usb_12", n=1)

        pid = Signal(4)

        fsm = FSM()
        self.submodules.fsm = fsm = ClockDomainsRenamer("usb_12")(fsm)
        fsm.act('IDLE',
            NextValue(tx.i_oe, self.i_pkt_start),
            If(self.i_pkt_start,
                # If i_pkt_start is set, then send the next packet.
                # We pre-queue the SYNC byte here to cut down on latency.
                NextState('QUEUE_SYNC'),
            ).Else(
                NextValue(tx.i_oe, 0),
            )
        )

        # Send the QUEUE_SYNC byte
        fsm.act('QUEUE_SYNC',
            # The PID might change mid-sync, because we're still figuring out what the response ought to be.
            NextValue(pid, self.i_pid),
            tx.i_data_payload.eq(1),
            If(tx.o_data_strobe,
                NextState('QUEUE_PID'),
            ),
        )

        # Send the PID byte
        fsm.act('QUEUE_PID',
            tx.i_data_payload.eq(Cat(pid, pid ^ 0b1111)),
            If(tx.o_data_strobe,
                If(pid & PIDTypes.TYPE_MASK == PIDTypes.HANDSHAKE,
                    NextState('WAIT_TRANSMIT'),
                ).Elif(pid & PIDTypes.TYPE_MASK == PIDTypes.DATA,
                    NextState('QUEUE_DATA0'),
                ).Else(
                    NextState('ERROR'),
                ),
            ),
        )

        nextstate = 'WAIT_TRANSMIT'
        if auto_crc:
            nextstate = 'QUEUE_CRC0'

        fsm.act('QUEUE_DATA0',
            If(~self.i_data_ready,
                NextState(nextstate),
            ).Else(
                NextState('QUEUE_DATAn'),
            ),
        )

        # Keep transmitting data bytes until the i_data_ready signal is not high on a o_data_strobe event.
        fsm.act('QUEUE_DATAn',
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
                crc.reset.eq(fsm.ongoing('QUEUE_PID')),
                If(fsm.ongoing('QUEUE_DATAn'),
                    crc.i_data_strobe.eq(tx.o_data_strobe),
                ),
            ]

            fsm.act('QUEUE_CRC0',
                tx.i_data_payload.eq(crc.o_crc[:8]),
                If(tx.o_data_strobe,
                    NextState('QUEUE_CRC1'),
                ),
            )
            fsm.act('QUEUE_CRC1',
                tx.i_data_payload.eq(crc.o_crc[8:]),
                If(tx.o_data_strobe,
                    NextState('WAIT_TRANSMIT'),
                ),
            )

        fsm.act('WAIT_TRANSMIT',
            NextValue(tx.i_oe, 0),
            If(~o_oe12,
                self.o_pkt_end.eq(1),
                NextState('IDLE'),
            ),
        )

        fsm.act('ERROR')

class UsbTransfer(Module):
    def __init__(self, iobuf, auto_crc=True):
        self.submodules.iobuf = ClockDomainsRenamer("usb_48")(iobuf)

        self.submodules.tx = tx = TxPipeline()
        self.submodules.txstate = txstate = TxPacketSend(tx, auto_crc=auto_crc)

        self.submodules.rx = rx = RxPipeline()
        self.submodules.rxstate = rxstate = PacketHeaderDecode(rx)

        # ----------------------
        # USB 48MHz bit strobe
        # ----------------------
        self.comb += [
            tx.i_bit_strobe.eq(rx.o_bit_strobe),
        ]

        # Whether to reset the FSM
        self.reset = Signal()

        # The state of the USB reset (SE0) signal
        self.usb_reset = Signal()
        self.comb += self.usb_reset.eq(rx.o_reset)

        # ----------------------
        # Data paths
        # ----------------------
        self.data_recv_put = Signal()
        self.data_recv_payload = Signal(8)

        self.data_send_get = Signal()
        self.data_send_have = Signal()
        self.data_send_payload = Signal(8)

        # ----------------------
        # State signally
        # ----------------------
        # The value of these signals are generally dependent on endp, so we need to wait for the rdy signal to use them.
        self.rdy  = Signal(reset=1)
        self.dtb  = Signal()
        self.arm  = Signal()
        self.sta  = Signal()
        self.addr = Signal(7)       # If the address doesn't match, we won't respond

        # ----------------------
        # Tristate
        # ----------------------
        self.submodules.iobuf = iobuf
        self.comb += [
            rx.i_usbp.eq(iobuf.usb_p_rx),
            rx.i_usbn.eq(iobuf.usb_n_rx),
            iobuf.usb_tx_en.eq(tx.o_oe),
            iobuf.usb_p_tx.eq(tx.o_usbp),
            iobuf.usb_n_tx.eq(tx.o_usbn),
        ]

        self.tok    = Signal(4)     # Contains the transfer token type
        self.endp   = Signal(4)

        self.idle   = Signal(reset=0)      # Asserted when in the "WAIT_TOKEN" state
        self.start  = Signal()      # Asserted when a transfer is starting
        self.poll   = Signal()      # Asserted when polling for a response (i.e. one cycle after `self.start`)
        self.setup  = Signal()      # Asserted when a transfer is a setup
        self.commit = Signal()      # Asserted when a transfer succeeds
        self.retry  = Signal()      # Asserted when the host sends an IN without an ACK
        self.abort  = Signal()      # Asserted when a transfer fails
        self.end    = Signal()      # Asserted when transfer ends
        self.data_end=Signal()      # Asserted when a DATAx transfer finishes
        self.error  = Signal()      # Asserted when in the ERROR state
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

        response_pid = Signal(4)
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
            # If we've indicated that we'll accept the data, put it into `data_recv_payload` and strobe `data_recv_put` every time a full byte comes in.
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

class USBWishboneBridge(Module):

    def __init__(self, usb_core, clk_freq=12000000, magic_packet=0x43, cdc=False):
        self.wishbone = WishboneInterface()

        """USB Wishbone Bridge

        This bridge provides a transparent bridge to the target device's Wishbone bus over USB.
        It can operate without interfering with the device's USB stack.  It is simple enough to
        be able to work even if the USB stack is not enumerated, though the host may not cooperate."""

        """USB Wishbone Debug Protocol

        The protocol transfers four bytes a time in big-endian (i.e. USB) order.  It uses SETUP packets
        with the special type (0x43) as an `attention` word.  This is then followed by an ``OUT`` packet.

            .. wavedrom::
                :caption: Write to Wishbone

                { "signal": [
                    ["Request",
                        {  "name": 'data',        "wave": 'x222...22x', "data": '0x43 0x00 [ADDRESS] 0x04 0x00'   },
                        {  "name": 'data bits',   "wave": 'xxx2222xxx', "data": '7:0 15:8 23:16 31:24'},
                        {  "name": 'usb meaning', "wave": 'x222.2.2.x', "data": 'bReq bTyp wValue wIndex wLength' },
                        {  "name": 'usb byte',    "wave": 'x22222222x', "data": '1 2 3 4 5 6 7 8'                 }
                    ],
                    {},
                    ["Payload",
                        {  "name": 'data',        "wave": 'x3...x', "data": '[DATA]'},
                        {  "name": 'data bits',   "wave": 'x3333x', "data": '7:0 15:8 23:16 31:24'},
                        {  "name": 'usb meaning', "wave": 'x3...x', "data": 'OUT'  },
                        {  "name": 'usb byte',    "wave": 'x3333x', "data": '1 2 3 4'}
                    ]
                ]}

        To read data from the device, set the top bit of the `bRequestType`, followed by an ``IN`` packet.

            .. wavedrom::
                :caption: Read from Wishbone

                { "signal": [
                    ['Request',
                        {  "name": 'data',        "wave": 'x222...22x', "data": '0xC3 0x00 [ADDRESS] 0x04 0x00'   },
                        {  "name": 'data bits',   "wave": 'xxx2222xxx', "data": '7:0 15:8 23:16 31:24'},
                        {  "name": 'usb meaning', "wave": 'x222.2.2.x', "data": 'bReq bTyp wValue wIndex wLength' },
                        {  "name": 'usb byte',    "wave": 'x22222222x', "data": '1 2 3 4 5 6 7 8'                 }
                    ],
                    {},
                    ["Payload",
                        {  "name": 'data',        "wave": 'x5...x', "data": '[DATA]'},
                        {  "name": 'data bits',   "wave": 'x5555x', "data": '7:0 15:8 23:16 31:24'},
                        {  "name": 'usb meaning', "wave": 'x5...x', "data": 'IN'  },
                        {  "name": 'usb byte',    "wave": 'x5555x', "data": '1 2 3 4'}
                    ]
                ]}
        """

        byte_counter = Signal(3, reset_less=True)
        byte_counter_reset = Signal()
        byte_counter_ce = Signal()
        self.sync.usb_12 += If(byte_counter_reset, byte_counter.eq(0)).Elif(byte_counter_ce, byte_counter.eq(byte_counter + 1))

        # Unlike the UART or Ethernet bridges, we explicitly only support two commands: reading and writing.
        # This gets integrated into the USB protocol, so it's not really a state.  1 is "USB Device to Host",
        # and is therefore a "read", while 0 is "USB Host to Device", and is therefore a "write".
        cmd = Signal(1, reset_less=True)
        cmd_ce = Signal()

        # Add a bridge to allow this module (in the usb_12 domain) to access the main Wishbone bridge (potentially in some other domain).
        # Ensure this bridge is placed in the "sys" domain.
        send_to_wishbone = Signal()
        reply_from_wishbone = Signal()
        transfer_active = Signal()
        if cdc:
            self.submodules.wb_cd_bridge = wb_cd_bridge = FSM(reset_state="IDLE")
            self.submodules.usb_to_wb = usb_to_wb = PulseSynchronizer("usb_12", "sys")
            self.submodules.wb_to_uwb = wb_to_usb = PulseSynchronizer("sys", "usb_12")
            send_to_wishbone = usb_to_wb.i
            reply_from_wishbone = wb_to_usb.o
        else:
            self.comb += [
                If(send_to_wishbone | transfer_active, self.wishbone.stb.eq(1), self.wishbone.we.eq(~cmd), self.wishbone.cyc.eq(1), ),
                reply_from_wishbone.eq(self.wishbone.ack | self.wishbone.err),
            ]

        # Instead of self.source and self.sink, we let the wrapping module handle packing and unpacking the data.
        self.sink_data = Signal(8)

        # True when the "sink" value has data
        self.sink_valid = Signal()

        self.send_ack = Signal()

        # Indicates whether a "debug" packet is currently being processed
        self.n_debug_in_progress = Signal(reset=1)

        address = Signal(32, reset_less=True)
        address_ce = Signal()

        data = Signal(32, reset_less=True)
        rd_data = Signal(32, reset_less=True)
        rx_data_ce = Signal()

        # wishbone_response = Signal(32, reset_less=True)
        self.sync.usb_12 += [
            If(cmd_ce, cmd.eq(usb_core.data_recv_payload[7:8])),
            If(address_ce, address.eq(Cat(address[8:32], usb_core.data_recv_payload))),
            If(rx_data_ce, data.eq(Cat(data[8:32], usb_core.data_recv_payload)))
        ]

        # The Litex Wishbone `dat_r` line is a shared medium, meaning the value changes often.
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

        # The target address comes as the wValue and wIndex in the SETUP packet.  Once we get that data, we're ready to do the operation.
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
            wb_cd_bridge.act("IDLE", If(usb_to_wb.o, NextState("DO_OP"), ), )
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
            If(usb_core.data_send_get, byte_counter_ce.eq(1), ),
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

        # Send the ACK.  If the endpoint number is incorrect, go back and wait again.
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

"""
Register Interface:

pullup_out_read: Read the status of the USB "FS" pullup.
pullup_out_write: Write the USB "FS" pullup state

SETUP - Responding to a SETUP packet from the host
setup_read: Read the contents of the last SETUP transaction
setup_ack: Write a "1" here to advance the data_read fifo
setup_empty: "0" if there is no SETUP data.
setup_epno: The endpoint the SETUP packet was destined for

EPOUT - Data from the host to this device
epout_data_read: Read the contents of the last transaction on the EP0
epout_data_ack: Write a "1" here to advance the data_read fifo
epout_last_tok: Bits 2 and 3 of the last token, from the following table:
   USB_PID_OUT   = 0
   USB_PID_SOF   = 1
   USB_PID_IN    = 2
   USB_PID_SETUP = 3
epout_epno: Which endpoint contained the last data
epout_queued: A response is queued and has yet to be acknowledged by the host

EPIN - Requests from the host to read data from this device
epin_data_write: Write 8 bits to the EP0 queue
epin_data_empty: Return 1 if the queue is empty
epin_epno: Which endpoint the data is for.  You must write this byte to indicate data is ready to be sent.
epin_queued: A response is queued and has yet to be acknowledged by the host

ep_stall: a 32-bit field representing endpoitns to respond with STALL.
"""

class TriEndpointInterface(Module, AutoCSR):
    """Implements a CPU interface with three FIFOs:
        * SETUP
        * IN
        * OUT

    Each of the three FIFOs has a relatively similar register set.

    Args
    ----

    iobuf (:obj:`io.IoBuf`): PHY interface to the raw pins.  This object
        encapsulate the pin interface to the outside world so that
        `TriEndpointInterface` does not need to have platform-specific
        IO handling.

    debug (bool, optional): Whether to add a debug bridge to this interface.
        Adding a debug bridge generates a Wishbone Master, which can take
        a large number of resources.  In exchange, it offers transparent debug.

    cdc (bool, optional): By default, ``eptri`` assumes that the CSR bus is in
        the same 12 MHz clock domain as the USB stack.  If ``cdc`` is set to
        True, then additional buffers will be placed on the ``.we`` and ``.re``
        lines to handle this difference.

    Attributes
    ----------

    debug_bridge (:obj:`wishbone.Interface`): The wishbone interface master for debug
        If `debug=True`, this attribute will contain the Wishbone Interface
        master for you to connect to your desired Wishbone bus.
    """

    def __init__(self, iobuf, debug=False, cdc=False):

        """USB Device Tri-FIFO

        This is a three-FIFO USB device.  It presents one FIFO each for ``IN``, ``OUT``,
        and ``SETUP`` data.  This allows for up to 16 ``IN`` and 16 ``OUT`` endpoints
        without sacrificing many FPGA resources.

        USB supports four types of transfers: control, bulk, interrupt, and isochronous.
        This device does not yet support isochronous transfers, however it supports the
        other types of transfers.
        """

        """Interrupt and Bulk Transfers

        Interrupt and bulk transfers are similar from an implementation standpoint --
        they differ only in terms of how often they are transmitted.

        These transfers can be made to any endpoint, and may even be interleaved.  However,
        due to the nature of ``TriEndpointInterface`` any attempt by the host to interleave
        transfers will result in a ``NAK``, and the host will retry later when the buffer
        is empty.

        IN Transfers
        ^^^^^^^^^^^^

        To make an ``IN`` transfer (i.e. to send data to the host), write the data to
        ``IN_DATA``.  This is a FIFO, and each write to this endpoint will advance the
        FIFO pointer automatically.  This FIFO is 64 bytes deep.  USB ``DATA`` packets
        contain a CRC16 checksum, which is automatically added to any ``IN`` transfers.

        ``TriEndpointInterface`` will continue to respond ``NAK`` until you arm the buffer.
        Do this by writing the endpoint number to ``IN_CTRL.EPNO``.  This will tell the device
        that it should send the data the next time the host asks for it.

        Once the data has been transferred, the device will raise an interrupt and you
        can begin re-filling the buffer, or fill it with data for a different endpoint.

        To send an empty packet, avoid writing any data to ``IN_DATA`` and simply write
        the endpoint number to ``IN_CTRL.EPNO``.

        The CRC16 will be automatically appended to the end of the transfer.

        OUT Transfers
        ^^^^^^^^^^^^^

        To respond to an ``OUT`` transfer (i.e. to receive data from the host), enable
        a particular endpoint by writing to ``OUT_CTRL.EPNO`` with the ``OUT_CTRL.ENABLE``
        bit set.  This will tell the device to stop responding ``NAK`` to that particular
        endpoint and to accept any incoming data into a 66-byte FIFO, provided the FIFO
        is empty.

        Once the host sends data, an interrupt will be raised and that particular endpoint's
        ``ENABLE`` will be set to ``0``.  This prevents any additional data from entering
        the FIFO while the device examines the data.

        The FIFO will contain two extra bytes, which are the two-byte CRC16 of the packet.
        You can safely discard these bytes.  Because of this, a zero-byte transfer will
        be two-bytes, and a full 64-byte transfer will be 66 bytes.

        To determine which endpoint the ``OUT`` packet was sent to, refer to
        ``OUT_STATUS.EPNO``.  This field is only updated when a successful packet is received,
        and will not change until the ``OUT`` FIFO is re-armed.

        The ``OUT`` FIFO will continue to respond to the host with with ``NAK`` until the
        ``OUT_EV_PENDING.DONE`` bit is cleared.

        Additionally, to continue receiving data on that particular endpoint, you will need
        to re-enable it by writing the endpoint number, along with the ``OUT_CTRL.ENABLE``
        to ``OUT_CTRL``.
        """

        """Control Transfers

        Control transfers are complicated, and are the first sort of transfer that
        the host uses.  Such transfers have three distinct phases.

        The first phase is the ``SETUP`` phase, where the host sends an 8-byte ``SETUP``
        packet.  These ``SETUP`` packets must always be acknowledged, so any such packet
        from the host will get loaded into the ``SETUP`` FIFO immediately, and an interrupt
        event raised.  If, for some reason, the device hasn't drained this ``SETUP``
        FIFO from a previous transaction, the FIFO will be cleared automatically.

        Once the ``SETUP`` packet is handled, the host will send an ``IN`` or ``OUT``
        packet.  If the host sends an ``OUT`` packet, then the ``OUT`` buffer must be
        cleared, the ``OUT.DONE`` interrupt handled, and the ``OUT_CTRL.ENABLE`` bit
        must be set for the appropriate endpoint, usually EP0.  The device will not
        accept any data as long as these three conditions are not met.

        If the host sends an ``IN`` packet, the device will respond with ``NAK`` if
        no data has queued.  To queue data, fill the ``IN_DATA`` buffer, then write
        ``0`` to ``IN_CTRL``.

        You can continue to fill the buffer (for ``IN`` packets) or drain the buffer
        and re-enable the endpoint (for ``OUT`` packets) until the host has finished
        the transfer.

        When the host has finished, it will send the opposite packet type.  If it
        is making ``IN`` transfers, it will send a single ``OUT`` packet, or if it
        is making ``OUT`` transfers it will send a single ``IN`` packet.
        You must handle this transaction yourself.

        Stalling an Endpoint
        ^^^^^^^^^^^^^^^^^^^^

        When the host sends a request that cannot be processed -- for example requesting
        a descriptor that does not exist -- the device must respond with ``STALL``.

        Each endpoint keeps track of its own ``STALL`` state, though a ``SETUP`` packet
        will clear the ``STALL`` state for the specified endpoint (usually EP0).

        To set or clear the ``STALL`` bit of an ``IN`` endpoint, write its endpoint number
        to ``IN_CTRL.EPNO`` with the ``IN_CTRL.STALL`` bit either set or clear.  If
        this bit is set, then the device will respond to the next ``IN`` packet from the
        host to that particular endpoint with ``STALL``.  If the bit is clear, then
        the next ``IN`` packet will be responded to with ``ACK`` and the contents of
        the ``IN`` FIFO.

        To stall an ``OUT`` endpoint, write to ``OUT_CTRL.EPNO`` with the ``OUT_CTRL.STALL``
        bit set.  To unstall, write to ``OUT_CTRL.EPNO`` with the ``OUT_CTRL.STALL`` bit
        cleared.  Note that ``OUT_CTRL.ENABLE`` should not be set at the same time as
        ``OUT_CTRL.STALL``, as this will cause a conflict.
        """

        # USB Core
        self.submodules.usb_core = usb_core = UsbTransfer(iobuf)

        self.submodules.pullup = GPIOOut(usb_core.iobuf.usb_pullup)
        self.iobuf = usb_core.iobuf

        # Generate debug signals, in case debug is enabled.
        debug_packet_detected = Signal()

        # Wire up debug signals if required
        if debug:
            self.submodules.debug_bridge = debug_bridge = USBWishboneBridge(self.usb_core, cdc=cdc)
            self.comb += [
                debug_packet_detected.eq(~self.debug_bridge.n_debug_in_progress),
            ]

        ems = []

        # When the USB host sends a USB reset, set our address back to 0.
        self.address = ResetInserter()(CSRStorage("address",
            fields=[CSRField("addr", 7, description="Write the USB address from USB ``SET_ADDRESS`` packets.")],
            description="""
                Sets the USB device address, in order to ignore packets
                going to other devices on the bus. This value is reset when the host
                issues a USB Device Reset condition.
            """))
        self.comb += self.address.reset.eq(usb_core.usb_reset)

        self.next_ev = CSRStatus("next_ev",
            fields=[
                CSRField("in", 1, description="``1`` if the next event is an ``IN`` event"),
                CSRField("out", 1, description="``1`` if the next event is an ``OUT`` event"),
                CSRField("setup", 1, description="``1`` if the next event is an ``SETUP`` event"),
                CSRField("reset", 1, description="``1`` if the next event is a ``RESET`` event"),
            ],
            description="""
                In ``eptri``, there are three endpoints.  It is possible for an IRQ to fire
                and have all three bits set.  Under these circumstances it can be difficult
                to know which event to process first.  Use this register to determine which
                event needs to be processed first.
                Only one bit will ever be set at a time.
            """,
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

        in_next = Signal()
        out_next = Signal()
        self.sync += [
            If(usb_core.usb_reset,
                in_next.eq(0),
                out_next.eq(0),
            # If the in_handler is set but not the out_handler, that one is next
            ).Elif(in_handler.ev.packet.pending & ~out_handler.ev.packet.pending,
                in_next.eq(1),
                out_next.eq(0),
            # If the out_handler is set first, mark that as `next`
            ).Elif(~in_handler.ev.packet.pending & out_handler.ev.packet.pending,
                in_next.eq(0),
                out_next.eq(1),
            # If neither is set, then clear the bits.
            ).Elif(~in_handler.ev.packet.pending & ~out_handler.ev.packet.pending,
                in_next.eq(0),
                out_next.eq(0),
            ),
            # If both are set, don't do anything.
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

        # If a debug packet comes in, the DTB should be 1.
        # Otherwise, the DTB should be whatever the in_handler says it is.
        self.comb += usb_core.dtb.eq(in_handler.dtb | debug_packet_detected)
        usb_core_reset = Signal()

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

        if debug:
            stage.act("DEBUG",
                usb_core.data_send_payload.eq(self.debug_bridge.sink_data),
                usb_core.data_send_have.eq(self.debug_bridge.sink_valid),
                usb_core.sta.eq(0),
                If(usb_core.endp == 0, usb_core.arm.eq(self.debug_bridge.send_ack | self.debug_bridge.sink_valid),).Else( usb_core.arm.eq(0)),
                If(~debug_packet_detected,
                    NextState("IDLE")
                )
            )
        else:
            stage.act("DEBUG", NextState("IDLE"))

        stage.act("SETUP",
            # SETUP packet
            setup_handler.data_recv_payload.eq(usb_core.data_recv_payload),
            setup_handler.data_recv_put.eq(usb_core.data_recv_put),

            # We aren't allowed to STALL a SETUP packet
            usb_core.sta.eq(0),

            # Always ACK a SETUP packet
            usb_core.arm.eq(1),

            If(debug_packet_detected, NextState("DEBUG")),
            If(usb_core.end, NextState("IDLE"), ),
        )

        stage.act("IN",
            If(usb_core.tok == PID.IN,
                # IN packet (device-to-host)
                usb_core.data_send_have.eq(in_handler.data_out_have),
                usb_core.data_send_payload.eq(in_handler.data_out),
                in_handler.data_out_advance.eq(usb_core.data_send_get),

                usb_core.sta.eq(in_handler.stalled),
                usb_core.arm.eq(in_handler.response),

                # After an IN transfer, the host sends an OUT packet.  We must ACK this and then return to IDLE.
                If(usb_core.end, NextState("IDLE"), ),
            ),
        )

        stage.act("OUT",
            If(usb_core.tok == PID.OUT,
                # OUT packet (host-to-device)
                out_handler.data_recv_payload.eq(usb_core.data_recv_payload),
                out_handler.data_recv_put.eq(usb_core.data_recv_put),

                usb_core.sta.eq(out_handler.stalled),
                usb_core.arm.eq(out_handler.response),

                # After an OUT transfer, the host sends an IN packet.  We must ACK this and then return to IDLE.
                If(usb_core.end, NextState("IDLE"), ),
            ),
        )

        self.comb += usb_core.reset.eq(usb_core.error | usb_core_reset)

class SetupHandler(Module, AutoCSR):
    """Handle ``SETUP`` packets

    ``SETUP`` packets must always respond with ``ACK``.  They are followed by a ``DATA0``
    packet, and may be followed by additional DATA stages.

    Since SETUP packets must always be handled, there is a separate FIFO that
    handles this data.  Hence the name `eptri`.

    The device must always acknowledge the ``SETUP`` packet right away, but need
    not send the acknowledgement stage right away.  You can use this to parse
    the data at a leisurely pace.

    When the device receives a ``SETUP`` transaction, an interrupt will fire
    and the ``SETUP_STATUS`` register will have ``SETUP_STATUS.HAVE`` set to ``1``.
    Drain the FIFO by reading from ``SETUP_DATA``, then setting
    ``SETUP_CTRL.ADVANCE``.

    Attributes
    ----------

    reset : Signal
        Asserting this resets the entire SetupHandler object.  You should do this at boot, or if
        you're switching applications.

    begin : Signal
        Assert this when a ``SETUP`` token is received.  This will clear out the current buffer
        (if any) and prepare the endpoint to receive data.

    epno : Signal(4)
        The endpoint number the SETUP packet came in on (probably is always ``0``)

    is_in : Signal
        This is a ``1`` if the ``SETUP`` packet will be followed by an ``IN`` stage.

    usb_reset : Signal
        This signal feeds into the EventManager, which is used to indicate to the device
        that a USB reset has occurred.

    """

    def __init__(self, usb_core):

        self.reset = Signal()
        self.begin = Signal()
        self.epno = epno = Signal()
        self.usb_reset = Signal()

        # Register Interface
        self.data = data = CSRStatus("data",
            fields=[CSRField("data", 8, description="The next byte of ``SETUP`` data")],
            description="Data from the last ``SETUP`` transactions.  It will be 10 bytes long, because it will include the CRC16.  This is a FIFO, and the queue is advanced automatically."
        )

        self.ctrl = ctrl = CSRStorage("ctrl",
            fields=[CSRField("reset", offset=5, description="Write a ``1`` here to reset the `SETUP` handler.", pulse=True), ],
            description="Controls for managing how to handle ``SETUP`` transactions."
        )

        self.status = status = CSRStatus("status",
            fields=[
                CSRField("epno", 4, description="The destination endpoint for the most recent SETUP token."),
                CSRField("have", description="``1`` if there is data in the FIFO."),
                CSRField("pend", description="``1`` if there is an IRQ pending."),
                CSRField("is_in", description="``1`` if an IN stage was detected."),
                CSRField("data", description="``1`` if a DATA stage is expected."),
            ],
            description="Status about the most recent ``SETUP`` transactions, and the state of the FIFO."
        )

        self.submodules.ev = EventManager()
        self.ev.submodules.packet = EventSourcePulse(name="ready", description="Indicates a ``SETUP`` packet has arrived and is waiting in the ``SETUP`` FIFO.")
        self.ev.submodules.reset = EventSourceProcess(name="reset", description="Indicates a USB ``RESET`` condition has occurred, and the ``ADDRESS`` is now ``0``.")
        self.ev.finalize()
        self.trigger = trigger = self.ev.packet.trigger
        self.pending = pending = self.ev.packet.pending
        self.comb += self.ev.reset.trigger.eq(~self.usb_reset)

        self.data_recv_payload = data_recv_payload = Signal(8)
        self.data_recv_put = data_recv_put = Signal()

        # Since we must always ACK a SETUP packet, set this to 0.
        self.response = Signal()

        class SetupHandlerInner(Module):
            def __init__(self):
                self.submodules.data = buf = _SyncFIFOBuffered(width=8, depth=10)

                # Indicates which byte of `SETUP` data we're currently on.
                data_byte = Signal(4)

                # If the incoming `SETUP` token indicates there will be a DATA stage, this will be set to 1.
                self.have_data_stage = have_data_stage = Signal()

                # If the incoming `SETUP` token is an OUT packet, this will be 1.
                self.is_in = is_in = Signal()

                self.empty = Signal()
                self.comb += self.empty.eq(~buf.readable)

                # Wire up the `STATUS` register
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

                    If(usb_core.tok == PID.SETUP, buf.din.eq(data_recv_payload), buf.we.eq(data_recv_put), ),

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

class InHandler(Module, AutoCSR):
    """Endpoint for Device->Host transactions.

    When a host requests data from a device, it sends an ``IN`` token.  The device
    should then respond with ``DATA0`, ``DATA1``, or ``NAK``.  This handler is
    responsible for managing this response, as well as supplying the USB system
    with data.

    To send data, fill the FIFO by writing bytes to ``IN_DATA``.  When you're ready
    to transmit, write the destination endpoint number to ``IN_CTRL``.

    Attributes
    ----------

    """
    def __init__(self, usb_core):
        self.dtb = Signal()

        # Keep track of the current DTB for each of the 16 endpoints
        dtbs = Signal(16, reset=0x0001)

        # A list of endpoints that are stalled
        stall_status = Signal(16)

        self.submodules.data_buf = buf = ResetInserter()(_SyncFIFOBuffered(width=8, depth=64))

        self.data = CSRStorage("data",
            fields=[CSRField("data", 8, description="The next byte to add to the queue."), ],
            description="""
                Each byte written into this register gets added to an outgoing FIFO.
                Any bytes that are written here will be transmitted in the order in which they were added.
                The FIFO queue is automatically advanced with each write.
                The FIFO queue is 64 bytes deep.
                If you exceed this amount, the result is undefined."""
        )

        self.ctrl = ctrl = CSRStorage("ctrl",
            fields=[
                CSRField("epno", 4, description="The endpoint number for the transaction that is queued in the FIFO."),
                CSRField("reset", offset=5, description="Write a ``1`` here to clear the contents of the FIFO.", pulse=True),
                CSRField("stall", description="Write a ``1`` here to stall the EP written in ``EP``.", pulse=True),
            ],
            description="Enables transmission of data in response to ``IN`` tokens, or resets the contents of the FIFO."
        )

        self.status = CSRStatus("status",
            fields=[
                CSRField("idle", description="This value is ``1`` if the packet has finished transmitting."),
                CSRField("have", offset=4, description="This value is ``0`` if the FIFO is empty."),
                CSRField("pend", offset=5, description="``1`` if there is an IRQ pending."),
            ],
            description="Status about the IN handler.  As soon as you write to `IN_DATA`, ``IN_STATUS.HAVE`` should go to ``1``."
        )

        self.submodules.ev = EventManager()
        self.ev.submodules.packet = EventSourcePulse(name="done", description="Indicates that the host has successfully transferred an ``IN`` packet, and that the FIFO is now empty.")
        self.ev.finalize()

        # Control bits
        ep_stall_mask = Signal(16)
        self.comb += [
            ep_stall_mask.eq(1 << ctrl.fields.epno),
        ]

        # Keep track of which endpoints are currently stalled
        self.stalled = Signal()
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
        self.response = Signal()

        # This value goes "1" when data is pending, and returns to "0" when it's done.
        queued = Signal()
        was_queued = Signal()

        # This goes to "1" when "queued" is 1 when a "start" occurs.  It is used
        # to avoid skipping packets when a packet is queued during a transmission.
        transmitted = Signal()

        self.dtb_reset = Signal()
        self.comb += [
            buf.reset.eq(ctrl.fields.reset | (usb_core.commit & transmitted & queued)),
        ]

        # Outgoing data will be placed on this signal
        self.data_out = Signal(8)

        # This is "1" if `data_out` contains data
        self.data_out_have = Signal()

        # Pulse this to advance the data output
        self.data_out_advance = Signal()

        # Used to detect when an IN packet finished
        is_our_packet = Signal()
        is_in_packet = Signal()

        self.comb += [
            # We will respond with "ACK" if the register matches the current endpoint number
            self.response.eq(queued & is_our_packet & is_in_packet),

            # Wire up the "status" register
            self.status.fields.have.eq(buf.readable),
            self.status.fields.idle.eq(~queued),
            self.status.fields.pend.eq(self.ev.packet.pending),

            # Cause a trigger event when the `queued` value goes to 0
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
            # When the user updates the `ctrl` register, enable writing.
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

class OutHandler(Module, AutoCSR):
    """
    Endpoint for Host->Device transaction

    When a host wants to send data to a device, it sends an ``OUT`` token.  The device
    should then respond with ``ACK``, or ``NAK``.  This handler is responsible for managing
    this response, as well as reading data from the USB subsystem.

    To enable receiving data, write a ``1`` to the ``OUT_CTRL.ENABLE`` bit.

    To drain the FIFO, read from ``OUT.DATA``.  Don't forget to re-
    enable the FIFO by ensuring ``OUT_CTRL.ENABLE`` is set after advancing the FIFO!

    Attributes
    ----------

    """
    def __init__(self, usb_core):

        self.submodules.data_buf = buf = ResetInserter()(_SyncFIFOBuffered(width=8, depth=66))

        self.data = data = CSRStatus("data",
            fields=[
                CSRField("data", 8, description="The top byte of the receive FIFO."),
            ],
            description="""
                Data received from the host will go into a FIFO.
                This register reflects the contents of the top byte in that FIFO.
                Reading from this register advances the FIFO pointer."""
        )

        self.ctrl = ctrl = CSRStorage("ctrl",
            fields=[
                CSRField("epno", 4, description="The endpoint number to update the ``enable`` and ``status`` bits for."),
                CSRField("enable", description="Write a ``1`` here to enable receiving data"),
                CSRField("reset", pulse=True, description="Write a ``1`` here to reset the ``OUT`` handler"),
                CSRField("stall", description="Write a ``1`` here to stall an endpoint"),
            ],
            description="""
                Controls for receiving packet data.  To enable an endpoint, write its value to ``epno``,
                with the ``enable`` bit set to ``1`` to enable an endpoint, or ``0`` to disable it.
                Resetting the OutHandler will set all ``enable`` bits to 0.

                Similarly, you can adjust the ``STALL`` state by setting or clearing the ``stall`` bit."""
        )

        self.status = CSRStatus("status",
            fields=[
                CSRField("epno", 4, description="The destination endpoint for the most recent ``OUT`` packet."),
                CSRField("have", description="``1`` if there is data in the FIFO."),
                CSRField("pend", description="``1`` if there is an IRQ pending."),
            ],
            description="Status about the current state of the `OUT` endpoint."
        )

        self.submodules.ev = EventManager()
        self.ev.submodules.packet = EventSourcePulse(name="done", description="""
            Indicates that an ``OUT`` packet has successfully been transferred from the host.  This bit must be cleared in order to receive additional packets.""")
        self.ev.finalize()

        self.usb_reset = Signal()

        self.stalled = Signal()
        self.enabled = Signal()
        stall_status = Signal(16)
        enable_status = Signal(16)
        ep_mask = Signal(16, reset=1)
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
        epno = Signal(4)

        # How to respond to requests:
        #  - 1 - ACK
        #  - 0 - NAK
        # Send a NAK if the buffer contains data, or if "ENABLE" has not been set.
        self.response = Signal()
        responding = Signal()
        is_out_packet = Signal()

        # Keep track of whether we're currently responding.
        self.comb += is_out_packet.eq(usb_core.tok == PID.OUT)
        self.comb += self.response.eq(self.enabled & is_out_packet & ~self.ev.packet.pending)
        self.sync += If(usb_core.poll, responding.eq(self.response))

        # Connect the buffer to the USB system
        self.data_recv_payload = Signal(8)
        self.data_recv_put = Signal()
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
            # Skip over modules already exposed, should handle potential renaming here.
            #if hasattr(i, c.name):
            #    pass

            # Attach csr as module attribute
            setattr(i, c.name,c)

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
                setattr(c.re0, "name", c.name + '_re0')

                # Our personal .re signal will then update .re0 alongside .storage
                setattr(c, "re", Signal(name=c.name + '_re'))
                c.sync += c.re0.eq(c.re)

                if hasattr(c, "fields"):
                    setattr(c, "dat_w", Record([]))
                    for a in c.fields.fields:
                        s = Signal(a.size,name=f'{c.name}_{a.name}0')

                        c.sync += If(c.re, c.storage[a.offset:a.offset + a.size].eq(s))
                        setattr(c.dat_w, a.name, s)
                else:
                    # if the CSRStorage doesn't have any fields, just provide .dat_w
                    setattr(c, "dat_w", Signal(c.size))
                    c.sync += If(c.re, c.storage.eq(c.dat_w))

class CDCUsb(Module, AutoCSR):
    """DummyUSB Self-Enumerating USB Controller

    This implements a device that simply responds to the most common SETUP packets.
    It is intended to be used alongside the Wishbone debug bridge.
    """

    def __init__(self, iobuf, debug=False, vid=0x1209, pid=0x5bf2, product="OrangeCrab CDC", manufacturer="GsD"):

        self.submodules.phy = phy = ClockDomainsRenamer("usb_12")(CDCUsbPHY(iobuf, debug=debug, vid=vid, pid=pid, product=product, manufacturer=manufacturer))

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

        self.sink   = Endpoint([("data", 8)])
        self.source = Endpoint([("data", 8)])

        self.rts = Signal()
        self.dtr = Signal()

        self.async_rst = Signal()

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
        tx_fifo = ClockDomainsRenamer({"write":"sys","read":"usb_12"})(AsyncFIFO([("data", 8)], 4, buffered=False))
        #tx_fifo = ResetInserter()(ClockDomainsRenamer({"write":"sys","read":"sys"})(AsyncFIFO([("data", 8)], 4, buffered=False)))
        #tx_fifo = SyncFIFO([("data", 8)], 4, buffered=True)
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
        rx_fifo = ClockDomainsRenamer({"write":"usb_12","read":"sys"})(AsyncFIFO([("data", 8)], 4, buffered=False))
        #rx_fifo = ResetInserter()(ClockDomainsRenamer({"write":"sys","read":"sys"})(AsyncFIFO([("data", 8)], 4, buffered=False)))
        #rx_fifo = SyncFIFO([("data", 8)], 4, buffered=True)
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
    """DummyUSB Self-Enumerating USB Controller

    This implements a device that simply responds to the most common SETUP packets.
    It is intended to be used alongside the Wishbone debug bridge.
    """

    def __init__(self, iobuf, debug, vid, pid, product, manufacturer):

        # Create the eptri USB interface
        usb = TriEndpointInterface(iobuf, debug=debug)
        #usb.finalize()
        self.submodules.eptri = usb = CSRTransform(self)(usb)

        self.sink   = Endpoint([("data", 8)])
        self.source = Endpoint([("data", 8)])

        self.rts = Signal()
        self.dtr = Signal()

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
            assert(len(s) <= 126)
            usbstr[0] = (len(s)*2)+2
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
        #mem.add(0xA120, 0x0000, [0x00,0x00]) # SerialState

        out_buffer = self.specials.out_buffer = Memory("out_buffer", 8, len(mem.contents), mem.contents)
        self.specials.out_buffer_rd = out_buffer_rd = out_buffer.get_port(write_capable=False, clock_domain="usb_12")
        self.autocsr_exclude = ['out_buffer']

        # Needs to be able to index Memory
        response_addr = Signal(9)
        response_len = Signal(6)
        response_ack = Signal()
        bytes_remaining = Signal(6)
        bytes_addr = Signal(9)

        new_address = Signal(7)

        configured = Signal()
        configured_delay = Signal(16, reset=2**16-1)

        self.configure_set = Signal()

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
        usbPacket = Signal(32)
        wRequestAndType = Signal(16)
        wValue = Signal(16)
        wLength = Signal(8)
        self.comb += [
            wRequestAndType.eq(usbPacket[16:32]),
            wValue.eq(usbPacket[0:16]),
        ]
        setup_index = Signal(4)

        # Respond to various descriptor requests
        cases = {}
        for key in mem.offsets:
            cases[key] = [
                response_len.eq(mem.lengths[key]),
                response_addr.eq(mem.offsets[key]),
            ]
        self.comb += Case(usbPacket, cases)

        self.submodules.config = config = FSM(reset_state="IDLE")

        toggle = Signal()

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

        delayed_re = Signal()
        config.act("FILL-TX",
            usb.in_data.dat_w.data.eq(self.source.data),

            usb.in_data.re.eq(delayed_re & self.source.valid),
            NextValue(delayed_re,0),

            self.source.ready.eq(delayed_re & self.source.valid),

            If(self.source.valid,
                NextValue(delayed_re,self.source.valid),
            ).Else(
                usb.in_ctrl.dat_w.epno.eq(2),
                usb.in_ctrl.re.eq(1),
                NextState("WAIT-TRANSACTION"),
            )
        )

        # OUT data always captures 2 extra bytes from CRC
        # Since we don't know in advance how long the transaction was we need to account for this now
        data_d1 = Signal(8)
        re_d1 = Signal()

        data_d2 = Signal(8)
        re_d2 = Signal()

        config.act("DRAIN-RX",
            self.sink.data.eq(data_d2),

            usb.out_data.we.eq(delayed_re & usb.out_status.fields.have & self.sink.ready),
            NextValue(delayed_re,0),

            self.sink.valid.eq(re_d2 & usb.out_status.fields.have & self.sink.ready),

            If(usb.out_status.fields.have,
                NextValue(delayed_re,usb.out_status.fields.have),

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
                    NextValue(delayed_re,0),

                    NextState("IDLE"),
            )
        )

        config.act("SETUP",
           # read out setup packets to determine what to do
           If(usb.setup_status.fields.have,
                NextValue(setup_index,setup_index + 1),
                Case(setup_index, {
                    0: NextValue(usbPacket,Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    1: NextValue(usbPacket,Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    2: NextValue(usbPacket,Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    3: NextValue(usbPacket,Cat(usb.setup_data.fields.data, usbPacket[0:24])),
                    # 4: wIndex.eq(data_recv_payload_delayed),
                    # 5: wIndex.eq(Cat(wIndex[0:8], data_recv_payload_delayed)),
                    6: NextValue(wLength,usb.setup_data.fields.data),
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
                    NextValue(new_address,wValue[8:15]),
                    NextState("WAIT-TRANSACTION"),
                ).Elif(wRequestAndType == 0x2122,
                    # Set Address
                    NextValue(self.rts,wValue[9]),
                    NextValue(self.dtr,wValue[8]),
                    NextState("WAIT-TRANSACTION"),
                ).Elif((usb.setup_status.fields.is_in) & (response_len > 0),
                    NextState("SETUP-IN"),
                    If(response_len > wLength,
                        NextValue(bytes_remaining,wLength),
                    ).Else(
                        NextValue(bytes_remaining,response_len),
                    ),
                    NextValue(bytes_addr,response_addr),
                ),
            )
        )

        config.act("SETUP-IN",
            usb.in_data.dat_w.data.eq(out_buffer_rd.dat_r),

            usb.in_data.re.eq(delayed_re),
            NextValue(delayed_re,0),

            If(bytes_remaining,
                NextValue(delayed_re,1),
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

CPU_VARIANTS = ["minimal", "standard"]

GCC_FLAGS = {
    #                               /-------- Base ISA
    #                               |/------- Hardware Multiply + Divide
    #                               ||/----- Atomics
    #                               |||/---- Compressed ISA
    #                               ||||/--- Single-Precision Floating-Point
    #                               |||||/-- Double-Precision Floating-Point
    #                               imacfd
    "minimal":          "-march=rv32i      -mabi=ilp32 ",
    "standard":         "-march=rv32im     -mabi=ilp32 ",
}

class PicoRV32(Module):
    name                 = "picorv32"
    human_name           = "PicoRV32"
    variants             = CPU_VARIANTS
    data_width           = 32
    endianness           = "little"
    linker_output_format = "elf32-littleriscv"
    nop                  = "nop"
    interrupts           = {}
    mem_map              = {}
    io_regions           = {0x80000000: 0x80000000} # origin, length
    gcc_flags            = None

    @property
    def gcc_flags(self):
        flags =  "-mno-save-restore "
        flags += GCC_FLAGS[self.variant]
        flags += "-D__picorv32__ "
        return flags

    @property
    def reserved_interrupts(self):
        return {
            "timer":                0,
            "ebreak_ecall_illegal": 1,
            "bus_error":            2
        }

    def __init__(self, platform, variant="standard"):
        self.platform     = platform
        self.variant      = variant
        self.trap         = Signal()
        self.reset        = Signal()
        self.interrupt    = Signal(32)
        self.idbus        = idbus = WishboneInterface()
        self.periph_buses = [idbus]
        self.memory_buses = []

        mem_valid = Signal()
        mem_instr = Signal()
        mem_ready = Signal()
        mem_addr  = Signal(32)
        mem_wdata = Signal(32)
        mem_wstrb = Signal(4)
        mem_rdata = Signal(32)

        # PicoRV32 parameters. To create a new variant, modify this dictionary
        # and change the desired parameters.
        self.cpu_params = dict(
            p_ENABLE_COUNTERS      = 1,
            p_ENABLE_COUNTERS64    = 1,
            # Changing REGS has no effect as on FPGAs, the registers are
            # implemented using a register file stored in DPRAM.
            p_ENABLE_REGS_16_31    = 1,
            p_ENABLE_REGS_DUALPORT = 1,
            p_LATCHED_MEM_RDATA    = 0,
            p_TWO_STAGE_SHIFT      = 1,
            p_TWO_CYCLE_COMPARE    = 0,
            p_TWO_CYCLE_ALU        = 0,
            p_CATCH_MISALIGN       = 1,
            p_CATCH_ILLINSN        = 1,
            p_ENABLE_PCPI          = 0,
            p_ENABLE_MUL           = 1,
            p_ENABLE_DIV           = 1,
            p_ENABLE_FAST_MUL      = 0,
            p_ENABLE_IRQ           = 1,
            p_ENABLE_IRQ_QREGS     = 1,
            p_ENABLE_IRQ_TIMER     = 1,
            p_ENABLE_TRACE         = 0,
            p_MASKED_IRQ           = 0x00000000,
            p_LATCHED_IRQ          = 0xffffffff,
            p_STACKADDR            = 0xffffffff,
        )

        if variant == "minimal":
            self.cpu_params.update(
                p_ENABLE_COUNTERS   = 0,
                p_ENABLE_COUNTERS64 = 0,
                p_TWO_STAGE_SHIFT   = 0,
                p_CATCH_MISALIGN    = 0,
                p_ENABLE_MUL        = 0,
                p_ENABLE_DIV        = 0,
                p_ENABLE_IRQ_TIMER  = 0,
            )

        self.cpu_params.update(
            # clock / reset
            i_clk    = ClockSignal(),
            i_resetn = ~(ResetSignal() | self.reset),

            # trap
            o_trap=self.trap,

            # memory interface
            o_mem_valid = mem_valid,
            o_mem_instr = mem_instr,
            i_mem_ready = mem_ready,

            o_mem_addr  = mem_addr,
            o_mem_wdata = mem_wdata,
            o_mem_wstrb = mem_wstrb,
            i_mem_rdata = mem_rdata,

            # look ahead interface (not used)
            o_mem_la_read  = Signal(),
            o_mem_la_write = Signal(),
            o_mem_la_addr  = Signal(32),
            o_mem_la_wdata = Signal(32),
            o_mem_la_wstrb = Signal(4),

            # co-processor interface (not used)
            o_pcpi_valid = Signal(),
            o_pcpi_insn  = Signal(32),
            o_pcpi_rs1   = Signal(32),
            o_pcpi_rs2   = Signal(32),
            i_pcpi_wr    = 0,
            i_pcpi_rd    = 0,
            i_pcpi_wait  = 0,
            i_pcpi_ready = 0,

            # irq interface
            i_irq = self.interrupt,
            o_eoi = Signal(32)) # not used

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

    def set_reset_address(self, reset_address):
        assert not hasattr(self, "reset_address")
        self.reset_address = reset_address
        self.cpu_params.update(
            p_PROGADDR_RESET = reset_address,
            p_PROGADDR_IRQ   = reset_address + 0x00000010
        )

    @staticmethod
    def add_sources(platform):
        platform.add_source(os.path.abspath(os.path.join(os.path.dirname(__file__), "picorv32.v")))

    def do_finalize(self):
        assert hasattr(self, "reset_address")
        self.specials += Instance("picorv32", **self.cpu_params)

def SoCConstant(value):
    return value

class SoCRegion:
    def __init__(self, origin=None, size=None, mode="rw", cached=True, linker=False):
        self.logger    = logging.getLogger("SoCRegion")
        self.origin    = origin
        self.size      = size
        if size != 2**log2_int(size, False):
            self.logger.info("Region size {} internally from {} to {}.".format(
                colorer("rounded", color="cyan"),
                colorer("0x{:08x}".format(size)),
                colorer("0x{:08x}".format(2**log2_int(size, False)))))
        self.size_pow2 = 2**log2_int(size, False)
        self.mode      = mode
        self.cached    = cached
        self.linker    = linker

    def decoder(self, bus):
        origin = self.origin
        size   = self.size_pow2
        if (origin & (size - 1)) != 0:
            self.logger.error("Origin needs to be aligned on size:")
            self.logger.error(self)
            raise
        origin >>= int(math.log2(bus.data_width//8)) # bytes to words aligned
        size   >>= int(math.log2(bus.data_width//8)) # bytes to words aligned
        return lambda a: (a[log2_int(size):] == (origin >> log2_int(size)))

    def __str__(self):
        r = ""
        if self.origin is not None:
            r += "Origin: {}, ".format(colorer("0x{:08x}".format(self.origin)))
        if self.size is not None:
            r += "Size: {}, ".format(colorer("0x{:08x}".format(self.size)))
        r += "Mode: {}, ".format(colorer(self.mode.upper()))
        r += "Cached: {} ".format(colorer(self.cached))
        r += "Linker: {}".format(colorer(self.linker))
        return r

class SoCIORegion(SoCRegion): pass

class SoCCSRRegion:
    def __init__(self, origin, busword, obj):
        self.origin  = origin
        self.busword = busword
        self.obj     = obj

class SoCBusHandler(Module):
    supported_standard      = ["wishbone"]
    supported_data_width    = [32, 64]
    supported_address_width = [32]

    def __init__(self, standard, data_width=32, address_width=32, timeout=1e6, reserved_regions={}):
        self.logger = logging.getLogger("SoCBusHandler")

        # Check Standard
        if standard not in self.supported_standard:
            self.logger.error("Unsupported {} {}, supporteds: {:s}".format(
                colorer("Bus standard", color="red"),
                colorer(standard),
                colorer(", ".join(self.supported_standard))))
            raise

        # Check Data Width
        if data_width not in self.supported_data_width:
            self.logger.error("Unsupported {} {}, supporteds: {:s}".format(
                colorer("Data Width", color="red"),
                colorer(data_width),
                colorer(", ".join(str(x) for x in self.supported_data_width))))
            raise

        # Check Address Width
        if address_width not in self.supported_address_width:
            self.logger.error("Unsupported {} {}, supporteds: {:s}".format(
                colorer("Address Width", color="red"),
                colorer(data_width),
                colorer(", ".join(str(x) for x in self.supported_address_width))))
            raise

        # Create Bus
        self.standard      = standard
        self.data_width    = data_width
        self.address_width = address_width
        self.masters       = {}
        self.slaves        = {}
        self.regions       = {}
        self.io_regions    = {}
        self.timeout       = timeout
        self.logger.info("{}-bit {} Bus, {}GiB Address Space.".format(colorer(data_width), colorer(standard), colorer(2**address_width/2**30)))

        # Adding reserved regions
        for name, region in reserved_regions.items():
            if isinstance(region, int):
                region = SoCRegion(origin=region, size=0x1000000)
            self.add_region(name, region)

    def add_region(self, name, region):
        allocated = False
        if name in self.regions.keys() or name in self.io_regions.keys():
            self.logger.error("{} already declared as Region:".format(colorer(name, color="red")))
            self.logger.error(self)
            raise
        # Check if SoCIORegion
        if isinstance(region, SoCIORegion):
            self.io_regions[name] = region
            overlap = self.check_regions_overlap(self.io_regions)
            if overlap is not None:
                self.logger.error("IO Region {} between {} and {}:".format(colorer("overlap", color="red"), colorer(overlap[0]), colorer(overlap[1])))
                self.logger.error(str(self.io_regions[overlap[0]]))
                self.logger.error(str(self.io_regions[overlap[1]]))
                raise
            self.logger.info("{} Region {} at {}.".format(colorer(name, color="underline"), colorer("added", color="green"), str(region)))
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
                        self.logger.error("{} Region {}: {}.".format(
                            colorer(name),
                            colorer("not in IO region", color="red"),
                            str(region)))
                        self.logger.error(self)
                        raise
                self.regions[name] = region
                overlap = self.check_regions_overlap(self.regions)
                if overlap is not None:
                    self.logger.error("Region {} between {} and {}:".format(
                        colorer("overlap", color="red"),
                        colorer(overlap[0]),
                        colorer(overlap[1])))
                    self.logger.error(str(self.regions[overlap[0]]))
                    self.logger.error(str(self.regions[overlap[1]]))
                    raise
            self.logger.info("{} Region {} at {}.".format(
                colorer(name, color="underline"),
                colorer("allocated" if allocated else "added", color="cyan" if allocated else "green"),
                str(region)))
        else:
            self.logger.error("{} is not a supported Region.".format(colorer(name, color="red")))
            raise

    def alloc_region(self, name, size, cached=True):
        self.logger.info("Allocating {} Region of size {}...".format(colorer("Cached" if cached else "IO"), colorer("0x{:08x}".format(size))))

        # Limit Search Regions
        if cached == False:
            search_regions = self.io_regions
        else:
            search_regions = {"main": SoCRegion(origin=0x00000000, size=2**self.address_width-1)}

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

        self.logger.error("Not enough Address Space to allocate Region.")
        raise

    def check_regions_overlap(self, regions, check_linker=False):
        i = 0
        while i < len(regions):
            n0 =  list(regions.keys())[i]
            r0 = regions[n0]
            for n1 in list(regions.keys())[i+1:]:
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
        assert direction in ["m2s", "s2m"]

        if isinstance(interface, WishboneInterface):
            new_interface = WishboneInterface(data_width=self.data_width)
            if direction == "m2s":
                converter = WishboneConverter(master=interface, slave=new_interface)
            if direction == "s2m":
                converter = WishboneConverter(master=new_interface, slave=interface)
            self.submodules += converter
        else:
            raise TypeError(interface)

        fmt = "{name} Bus {converted} from {frombus} {frombits}-bit to {tobus} {tobits}-bit."
        frombus  = "Wishbone" if isinstance(interface, WishboneInterface) else "AXILite"
        tobus    = "Wishbone" if isinstance(new_interface, WishboneInterface) else "AXILite"
        frombits = interface.data_width
        tobits   = new_interface.data_width
        if frombus != tobus or frombits != tobits:
            self.logger.info(fmt.format(
                name      = colorer(name),
                converted = colorer("converted", color="cyan"),
                frombus   = colorer("Wishbone" if isinstance(interface, WishboneInterface) else "AXILite"),
                frombits  = colorer(interface.data_width),
                tobus     = colorer("Wishbone" if isinstance(new_interface, WishboneInterface) else "AXILite"),
                tobits    = colorer(new_interface.data_width)))
        return new_interface

    def add_master(self, name=None, master=None):
        if name is None:
            name = "master{:d}".format(len(self.masters))
        if name in self.masters.keys():
            self.logger.error("{} {} as Bus Master:".format(
                colorer(name),
                colorer("already declared", color="red")))
            self.logger.error(self)
            raise
        master = self.add_adapter(name, master, "m2s")
        self.masters[name] = master
        self.logger.info("{} {} as Bus Master.".format(
            colorer(name,    color="underline"),
            colorer("added", color="green")))

    def add_slave(self, name=None, slave=None, region=None):
        no_name   = name is None
        no_region = region is None
        if no_name and no_region:
            self.logger.error("Please {} {} or/and {} of Bus Slave.".format(
                colorer("specify", color="red"),
                colorer("name"),
                colorer("region")))
            raise
        if no_name:
            name = "slave{:d}".format(len(self.slaves))
        if no_region:
            region = self.regions.get(name, None)
            if region is None:
                self.logger.error("{} Region {}.".format(
                    colorer(name),
                    colorer("not found", color="red")))
                raise
        else:
             self.add_region(name, region)
        if name in self.slaves.keys():
            self.logger.error("{} {} as Bus Slave:".format(
                colorer(name),
                colorer("already declared", color="red")))
            self.logger.error(self)
            raise
        slave = self.add_adapter(name, slave, "s2m")
        self.slaves[name] = slave
        self.logger.info("{} {} as Bus Slave.".format(
            colorer(name, color="underline"),
            colorer("added", color="green")))

    def __str__(self):
        r = "{}-bit {} Bus, {}GiB Address Space.\n".format(
            colorer(self.data_width), colorer(self.standard), colorer(2**self.address_width/2**30))
        r += "IO Regions: ({})\n".format(len(self.io_regions.keys())) if len(self.io_regions.keys()) else ""
        io_regions = {k: v for k, v in sorted(self.io_regions.items(), key=lambda item: item[1].origin)}
        for name, region in io_regions.items():
           r += colorer(name, color="underline") + " "*(20-len(name)) + ": " + str(region) + "\n"
        r += "Bus Regions: ({})\n".format(len(self.regions.keys())) if len(self.regions.keys()) else ""
        regions = {k: v for k, v in sorted(self.regions.items(), key=lambda item: item[1].origin)}
        for name, region in regions.items():
           r += colorer(name, color="underline") + " "*(20-len(name)) + ": " + str(region) + "\n"
        r += "Bus Masters: ({})\n".format(len(self.masters.keys())) if len(self.masters.keys()) else ""
        for name in self.masters.keys():
           r += "- {}\n".format(colorer(name, color="underline"))
        r += "Bus Slaves: ({})\n".format(len(self.slaves.keys())) if len(self.slaves.keys()) else ""
        for name in self.slaves.keys():
           r += "- {}\n".format(colorer(name, color="underline"))
        r = r[:-1]
        return r

class SoCLocHandler(Module):
    def __init__(self, name, n_locs):
        self.name   = name
        self.locs   = {}
        self.n_locs = n_locs

    def add(self, name, n=None, use_loc_if_exists=False):
        allocated = False
        if not (use_loc_if_exists and name in self.locs.keys()):
            if name in self.locs.keys():
                self.logger.error("{} {} name {}.".format(colorer(name), self.name, colorer("already used", color="red")))
                self.logger.error(self)
                raise
            if n in self.locs.values():
                self.logger.error("{} {} Location {}.".format(colorer(n), self.name, colorer("already used", color="red")))
                self.logger.error(self)
                raise
            if n is None:
                allocated = True
                n = self.alloc(name)
            else:
                if n < 0:
                    self.logger.error("{} {} Location should be {}.".format(colorer(n), self.name, colorer("positive", color="red")))
                    raise
                if n > self.n_locs:
                    self.logger.error("{} {} Location {} than maximum: {}.".format(colorer(n), self.name, colorer("higher", color="red"), colorer(self.n_locs)))
                    raise
            self.locs[name] = n
        else:
            n = self.locs[name]
        self.logger.info("{} {} {} at Location {}.".format(
            colorer(name, color="underline"),
            self.name,
            colorer("allocated" if allocated else "added", color="cyan" if allocated else "green"),
            colorer(n)))

    def alloc(self, name):
        for n in range(self.n_locs):
            if n not in self.locs.values():
                return n
        self.logger.error("Not enough Locations.")
        self.logger.error(self)
        raise

    def __str__(self):
        r = "{} Locations: ({})\n".format(self.name, len(self.locs.keys())) if len(self.locs.keys()) else ""
        locs = {k: v for k, v in sorted(self.locs.items(), key=lambda item: item[1])}
        length = 0
        for name in locs.keys():
            if len(name) > length: length = len(name)
        for name in locs.keys():
           r += "- {}{}: {}\n".format(colorer(name, color="underline"), " "*(length + 1 - len(name)), colorer(self.locs[name]))
        return r

class SoCCSRHandler(SoCLocHandler):
    supported_data_width    = [8, 32]
    supported_address_width = [14+i for i in range(4)]
    supported_alignment     = [32]
    supported_paging        = [0x800*2**i for i in range(4)]

    def __init__(self, data_width=32, address_width=14, alignment=32, paging=0x800, reserved_csrs={}):
        SoCLocHandler.__init__(self, "CSR", n_locs=alignment // 8 * (2**address_width) // paging)
        self.logger = logging.getLogger("SoCCSRHandler")

        # Check Data Width
        if data_width not in self.supported_data_width:
            self.logger.error("Unsupported {} {}, supporteds: {:s}".format(
                colorer("Data Width", color="red"),
                colorer(data_width),
                colorer(", ".join(str(x) for x in self.supported_data_width))))
            raise

        # Check Address Width
        if address_width not in self.supported_address_width:
            self.logger.error("Unsupported {} {} supporteds: {:s}".format(
                colorer("Address Width", color="red"),
                colorer(address_width),
                colorer(", ".join(str(x) for x in self.supported_address_width))))
            raise

        # Check Alignment
        if alignment not in self.supported_alignment:
            self.logger.error("Unsupported {}: {} supporteds: {:s}".format(
                colorer("Alignment", color="red"),
                colorer(alignment),
                colorer(", ".join(str(x) for x in self.supported_alignment))))
            raise
        if data_width > alignment:
            self.logger.error("Alignment ({}) {} Data Width ({})".format(
                colorer(alignment),
                colorer("should be >=", color="red"),
                colorer(data_width)))
            raise

        # Check Paging
        if paging not in self.supported_paging:
            self.logger.error("Unsupported {} 0x{}, supporteds: {:s}".format(
                colorer("Paging", color="red"),
                colorer("{:x}".format(paging)),
                colorer(", ".join("0x{:x}".format(x) for x in self.supported_paging))))
            raise

        # Create CSR Handler
        self.data_width    = data_width
        self.address_width = address_width
        self.alignment     = alignment
        self.paging        = paging
        self.masters       = {}
        self.regions       = {}
        self.logger.info("{}-bit CSR Bus, {}-bit Aligned, {}KiB Address Space, {}B Paging (Up to {} Locations).".format(
            colorer(self.data_width),
            colorer(self.alignment),
            colorer(2**self.address_width/2**10),
            colorer(self.paging),
            colorer(self.n_locs)))

        # Adding reserved CSRs
        for name, n in reserved_csrs.items():
            self.add(name, n)

    def add_master(self, name=None, master=None):
        if name is None:
            name = "master{:d}".format(len(self.masters))
        if name in self.masters.keys():
            self.logger.error("{} {} as CSR Master:".format(colorer(name), colorer("already declared", color="red")))
            self.logger.error(self)
            raise
        if master.data_width != self.data_width:
            self.logger.error("{} Master/Handler Data Width {} ({} vs {}).".format(
                colorer(name),
                colorer("missmatch", color="red"),
                colorer(master.data_width),
                colorer(self.data_width)))
            raise
        self.masters[name] = master
        self.logger.info("{} {} as CSR Master.".format(colorer(name, color="underline"), colorer("added", color="green")))

    def add_region(self, name, region):
        # FIXME: add checks
        self.regions[name] = region

    def address_map(self, name, memory):
        if memory is not None:
            name = name + "_" + memory.name_override
        if self.locs.get(name, None) is None:
            self.logger.error("CSR {} {}.".format(colorer(name), colorer("not found", color="red")))
            self.logger.error(self)
            raise
        return self.locs[name]

    def __str__(self):
        r = "{}-bit CSR Bus, {}-bit Aligned, {}KiB Address Space, {}B Paging (Up to {} Locations).\n".format(
            colorer(self.data_width),
            colorer(self.alignment),
            colorer(2**self.address_width/2**10),
            colorer(self.paging),
            colorer(self.n_locs))
        r += SoCLocHandler.__str__(self)
        r = r[:-1]
        return r

class SoCIRQHandler(SoCLocHandler):
    def __init__(self, n_irqs=32, reserved_irqs={}):
        SoCLocHandler.__init__(self, "IRQ", n_locs=n_irqs)
        self.logger = logging.getLogger("SoCIRQHandler")

        # Check IRQ Number
        if n_irqs > 32:
            self.logger.error("Unsupported IRQs number: {} supporteds: {:s}".format(colorer(n, color="red"), colorer("Up to 32", color="green")))
            raise

        # Adding reserved IRQs
        for name, n in reserved_irqs.items():
            self.add(name, n)

    def __str__(self):
        r ="IRQ Handler (up to {} Locations).\n".format(colorer(self.n_locs))
        r += SoCLocHandler.__str__(self)
        r = r[:-1]
        return r

class SoCController(Module, AutoCSR):
    def __init__(self, with_reset = True, with_scratch = True, with_errors = True):

        if with_reset:
            self._reset = CSRStorage("reset", 1, description="""Write a ``1`` to this register to reset the SoC.""")
        if with_scratch:
            self._scratch = CSRStorage("scratch", 32, reset=0x12345678, description="""
                Use this register as a scratch space to verify that software read/write accesses to the Wishbone/CSR bus are working correctly.
                The initial reset value of 0x1234578 can be used to verify endianness.""")
        if with_errors:
            self._bus_errors = CSRStatus("bus_errors", 32, description="Total number of Wishbone bus errors (timeouts) since start.")

        # Reset
        if with_reset:
            self.reset = Signal()
            self.comb += self.reset.eq(self._reset.re)

        # Errors
        if with_errors:
            self.bus_error = Signal()
            bus_errors     = Signal(32)
            self.sync += [
                If(bus_errors != (2**len(bus_errors)-1),
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

    def __repr__(self):
        return "{}('{}')".format(self.__class__.__name__, " ".join(self.identifiers))

class IOStandard:
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return "{}('{}')".format(self.__class__.__name__, self.name)

class Drive:
    def __init__(self, strength):
        self.strength = strength

    def __repr__(self):
        return "{}('{}')".format(self.__class__.__name__, self.strength)

class Misc:
    def __init__(self, misc):
        self.misc = misc

    def __repr__(self):
        return "{}({})".format(self.__class__.__name__, repr(self.misc))

class Inverted:
    def __repr__(self):
        return "{}()".format(self.__class__.__name__)

class Subsignal:
    def __init__(self, name, *constraints):
        self.name = name
        self.constraints = list(constraints)

    def __repr__(self):
        return "{}('{}', {})".format(self.__class__.__name__, self.name, ", ".join([repr(constr) for constr in self.constraints]))

class PlatformInfo:
    def __init__(self, info):
        self.info = info

    def __repr__(self):
        return "{}({})".format(self.__class__.__name__, repr(self.info))

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
    "synth_ecp5 -abc9 {nwl} -json {build_name}.json -top {build_name}",
]

def _yosys_import_sources(platform):
    includes = ""
    reads = []
    for path in platform.verilog_include_paths:
        includes += " -I" + path
    for filename, language, library in platform.sources:
        reads.append("read_{}{} {}".format(
            language, includes, filename))
    return "\n".join(reads)

def _build_yosys(template, platform, nowidelut, build_name):
    ys = []
    for l in template:
        ys.append(l.format(
            build_name = build_name,
            nwl        = "-nowidelut" if nowidelut else "",
            read_files = _yosys_import_sources(platform)
        ))
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
    "lfe5u-12f"   : "12k",
    "lfe5u-25f"   : "25k",
    "lfe5u-45f"   : "45k",
    "lfe5u-85f"   : "85k",
    "lfe5um-25f"  : "um-25k",
    "lfe5um-45f"  : "um-45k",
    "lfe5um-85f"  : "um-85k",
    "lfe5um5g-25f": "um5g-25k",
    "lfe5um5g-45f": "um5g-45k",
    "lfe5um5g-85f": "um5g-85k",
}

_build_template = [
    "yosys {build_name}.ys",
    "nextpnr-ecp5 --json {build_name}.json --lpf {build_name}.lpf --textcfg {build_name}.config  \
    --{architecture} --package {package} --speed {speed_grade} {timefailarg} {ignoreloops} --seed {seed}",
    "ecppack {build_name}.config --bit {build_name}.bit --bootaddr {bootaddr}"
]

def _build_script(source, build_template, build_name, architecture, package, speed_grade, timingstrict, ignoreloops, bootaddr, seed):
    s = "set -e\n"

    for line in build_template:
        s += (line + "\n").format(
            build_name   = build_name,
            architecture = architecture,
            package      = package,
            speed_grade  = speed_grade,
            timefailarg  = "--timing-allow-fail" if not timingstrict else "",
            ignoreloops  = "--ignore-loops" if ignoreloops else "",
            bootaddr     = bootaddr,
            seed         = seed)

    script_file = "build.sh"
    write_file(script_file, s)

    return script_file

class InferedSDRIO(Module):
    def __init__(self, i, o, clk):
        self.clock_domains.cd_sdrio = ClockDomain("cd_sdrio", reset_less=True)
        self.comb += self.cd_sdrio.clk.eq(clk)
        self.sync.sdrio += o.eq(i)

class SDRIO(Special):
    def __init__(self, i, o, clk=ClockSignal()):
        assert len(i) == len(o) == 1
        Special.__init__(self)
        self.i            = wrap(i)
        self.o            = wrap(o)
        self.clk          = wrap(clk)
        self.clk_domain   = None if not hasattr(clk, "cd") else clk.cd

    def iter_expressions(self):
        yield self, "i",   SPECIAL_INPUT
        yield self, "o",   SPECIAL_OUTPUT
        yield self, "clk", SPECIAL_INPUT

    @staticmethod
    def lower(dr):
        return InferedSDRIO(dr.i, dr.o, dr.clk, dr.clk_domain)

class SDRInput(SDRIO):  pass
class SDROutput(SDRIO): pass

class DDRInput(Special):
    def __init__(self, i, o1, o2, clk=ClockSignal()):
        Special.__init__(self)
        self.i   = wrap(i)
        self.o1  = wrap(o1)
        self.o2  = wrap(o2)
        self.clk = wrap(clk)

    def iter_expressions(self):
        yield self, "i", SPECIAL_INPUT
        yield self, "o1", SPECIAL_OUTPUT
        yield self, "o2", SPECIAL_OUTPUT
        yield self, "clk", SPECIAL_INPUT

    @staticmethod
    def lower(dr):
        raise NotImplementedError("Attempted to use a DDR input, but platform does not support them")

class DDROutput(Special):
    def __init__(self, i1, i2, o, clk=ClockSignal()):
        Special.__init__(self)
        self.i1  = i1
        self.i2  = i2
        self.o   = o
        self.clk = clk

    def iter_expressions(self):
        yield self, "i1", SPECIAL_INPUT
        yield self, "i2", SPECIAL_INPUT
        yield self, "o", SPECIAL_OUTPUT
        yield self, "clk", SPECIAL_INPUT

    @staticmethod
    def lower(dr):
        raise NotImplementedError("Attempted to use a DDR output, but platform does not support them")

class LatticeECP5AsyncResetSynchronizerImpl(Module):
    def __init__(self, cd, async_reset):
        rst1 = Signal()
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

class LatticeECP5SDRInputImpl(Module):
    def __init__(self, i, o, clk):
        self.specials += Instance("IFS1P3BX",
            i_SCLK = clk,
            i_PD   = 0,
            i_SP   = 1,
            i_D    = i,
            o_Q    = o,
        )

class LatticeECP5SDRInput:
    @staticmethod
    def lower(dr):
        return LatticeECP5SDRInputImpl(dr.i, dr.o, dr.clk)

class LatticeECP5SDROutputImpl(Module):
    def __init__(self, i, o, clk):
        self.specials += Instance("OFS1P3BX",
            i_SCLK = clk,
            i_PD   = 0,
            i_SP   = 1,
            i_D    = i,
            o_Q    = o,
        )

class LatticeECP5SDROutput:
    @staticmethod
    def lower(dr):
        return LatticeECP5SDROutputImpl(dr.i, dr.o, dr.clk)

class LatticeECP5DDRInputImpl(Module):
    def __init__(self, i, o1, o2, clk):
        self.specials += Instance("IDDRX1F",
            i_SCLK = clk,
            i_D    = i,
            o_Q0   = o1,
            o_Q1   = o2,
        )

class LatticeECP5DDRInput:
    @staticmethod
    def lower(dr):
        return LatticeECP5DDRInputImpl(dr.i, dr.o1, dr.o2, dr.clk)

class LatticeECP5DDROutputImpl(Module):
    def __init__(self, i1, i2, o, clk):
        self.specials += Instance("ODDRX1F",
            i_SCLK = clk,
            i_D0   = i1,
            i_D1   = i2,
            o_Q    = o,
        )

class LatticeECP5DDROutput:
    @staticmethod
    def lower(dr):
        return LatticeECP5DDROutputImpl(dr.i1, dr.i2, dr.o, dr.clk)

class LatticeECP5TrellisTristateImpl(Module):
    def __init__(self, io, o, oe, i):
        nbits, sign = value_bits_sign(io)
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
    SDRInput:               LatticeECP5SDRInput,
    SDROutput:              LatticeECP5SDROutput,
    DDRInput:               LatticeECP5DDRInput,
    DDROutput:              LatticeECP5DDROutput
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
        self.false_paths = set() # FIXME: use it

    def build(self, platform, fragment,
        build_dir      = "build",
        build_name     = "top",
        run            = True,
        nowidelut      = False,
        timingstrict   = False,
        ignoreloops    = False,
        bootaddr       = 0,
        seed           = 1):

        # Create build directory
        os.makedirs(build_dir, exist_ok=True)
        cwd = os.getcwd()
        os.chdir(build_dir)

        # Finalize design
        if not isinstance(fragment, _Fragment):
            fragment = fragment.get_fragment()
        platform.finalize(fragment)

        # Generate verilog
        v_output = platform.get_verilog(fragment, name=build_name)
        named_sc, named_pc = platform.resolve_signals(v_output.ns)
        top_file = build_name + ".v"
        v_output.write(top_file)
        platform.add_source(top_file)

        # Generate design constraints file (.lpf)
        _build_lpf(named_sc, named_pc, build_name)

        # Generate Yosys script
        _build_yosys(self.yosys_template, platform, nowidelut, build_name)

        # Translate device to Nextpnr architecture/package/speed_grade
        (family, size, speed_grade, package) = nextpnr_ecp5_parse_device(platform.device)
        architecture = nextpnr_ecp5_architectures[(family + "-" + size)]

        # Generate build script
        script = _build_script(False, self.build_template, build_name, architecture, package, speed_grade, timingstrict, ignoreloops, bootaddr, seed)
        # Run
        if run:
            if subprocess.call(["bash"] + [script]) != 0:
                raise OSError("Subprocess failed")

        os.chdir(cwd)

        return v_output.ns

    def add_period_constraint(self, platform, clk, period):
        platform.add_platform_command("""FREQUENCY PORT "{clk}" {freq} MHz;""".format(freq=str(float(1 / period) * 1000), clk="{clk}"), clk=clk)

def _lookup(description, name, number):
    for resource in description:
        if resource[0] == name and (number is None or resource[1] == number):
            return resource
    raise ConstraintError("Resource not found: {}:{}".format(name, number))

def _resource_type(resource):
    t = None
    i = None
    for element in resource[2:]:
        if isinstance(element, Pins):
            assert(t is None)
            t = len(element.identifiers)
        elif isinstance(element, Subsignal):
            if t is None:
                t = []
            if i is None:
                i = []

            assert(isinstance(t, list))
            n_bits = None
            inverted = False
            for c in element.constraints:
                if isinstance(c, Pins):
                    assert(n_bits is None)
                    n_bits = len(c.identifiers)
                if isinstance(c, Inverted):
                    inverted = True

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
            assert(pins is None)
            pins = c.identifiers
        else:
            others.append(c)

    return pins, others

class ConstraintManager:
    def __init__(self, io, connectors):
        self.available = list(io)
        self.matched = []
        self.platform_commands = []
        self.connector_manager = ConnectorManager(connectors)

    def request(self, name, number=None):
        resource = _lookup(self.available, name, number)
        rt, ri = _resource_type(resource)
        if number is None:
            resource_name = name
        else:
            resource_name = name + str(number)
        if isinstance(rt, int):
            obj = Signal(rt, name_override=resource_name)
        else:
            obj = Record(rt, name=resource_name)
            for name, inverted in ri:
                if inverted:
                    getattr(obj, name).inverted = True

        for element in resource[2:]:
            if isinstance(element, Inverted):
                if isinstance(obj, Signal):
                    obj.inverted = True
            if isinstance(element, PlatformInfo):
                obj.platform_info = element.info
                break

        self.available.remove(resource)
        self.matched.append((resource, obj))
        return obj

    def lookup_request(self, name, number=None, loose=False):
        subname = None
        if ":" in name: name, subname = name.split(":")
        for resource, obj in self.matched:
            if resource[0] == name and (number is None or resource[1] == number):
                if subname is not None:
                    return getattr(obj, subname)
                else:
                    return obj

        if loose:
            return None
        else:
            raise ConstraintError("Resource not found: {}:{}".format(name, number))

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

    ("ddram", 0,
        Subsignal("a",       Pins("C4 D2 D3 A3 A4 D4 C3 B2", "B1 D1 A7 C2 B6 C1 A2 C7"),                 IOStandard("SSTL135_I")),
        Subsignal("ba",      Pins("D6 B7 A6"),                                                           IOStandard("SSTL135_I"),),
        Subsignal("ras_n",   Pins("C12"),                                                                IOStandard("SSTL135_I")),
        Subsignal("cas_n",   Pins("D13"),                                                                IOStandard("SSTL135_I")),
        Subsignal("we_n",    Pins("B12"),                                                                IOStandard("SSTL135_I")),
        Subsignal("cs_n",    Pins("A12"),                                                                IOStandard("SSTL135_I")),
        Subsignal("dm",      Pins("D16 G16"),                                                            IOStandard("SSTL135_I")),
        Subsignal("dq",      Pins("C17 D15 B17 C16 A15 B13 A17 A13", "F17 F16 G15 F15 J16 C18 H16 F18"), IOStandard("SSTL135_I"),  Misc("TERMINATION=75")),
        Subsignal("dqs_p",   Pins("B15 G18"),                                                            IOStandard("SSTL135D_I"), Misc("TERMINATION=OFF"), Misc("DIFFRESISTOR=100")),
        Subsignal("clk_p",   Pins("J18"),                                                                IOStandard("SSTL135D_I")),
        Subsignal("cke",     Pins("D18"),                                                                IOStandard("SSTL135_I")),
        Subsignal("odt",     Pins("C13"),                                                                IOStandard("SSTL135_I")),
        Subsignal("reset_n", Pins("L18"),                                                                IOStandard("SSTL135_I")),
        Subsignal("vccio",   Pins("K16 D17 K15 K17 B18 C6"),                                             IOStandard("SSTL135_II")),
        Subsignal("gnd",     Pins("L15 L16"),                                                            IOStandard("SSTL135_II")),
        Misc("SLEWRATE=FAST")
    ),

    ("usb", 0,
        Subsignal("d_p",    Pins("N1")),
        Subsignal("d_n",    Pins("M2")),
        Subsignal("pullup", Pins("N2")),
        IOStandard("LVCMOS33")
    ),
]

_connectors_r0_2 = [
    ("GPIO", "N17 M18 C10 C9 - B10 B9 - - C8 B8 A8 H2 J2 N15 R17 N16 - L4 N3 N4 H4 G4 T17"),
]

def register_clkin_log(logger, clkin, freq):
    logger.info("Registering {} {} of {}.".format(
        colorer("Differential") if isinstance(clkin, Record) else colorer("Single Ended"),
        colorer("ClkIn"),
        colorer("{:3.2f}MHz".format(freq / 1e6))
    ))

def create_clkout_log(logger, name, freq, margin, nclkouts):
    logger.info("Creating {} of {} {}.".format(
        colorer("ClkOut{} {}".format(nclkouts, name)),
        colorer("{:3.2f}MHz".format(freq / 1e6)),
        "(+-{:3.2f}ppm)".format(margin * 1e6),
    ))

def compute_config_log(logger, config):
    log    = "Config:\n"
    length = 0
    for name in config.keys():
        if len(name) > length: length = len(name)
    for name, value in config.items():
        if "freq" in name or "vco" in name:
            value = "{:3.2f}MHz".format(value / 1e6)
        if "phase" in name:
            value = "{:3.2f}°".format(value)
        log += "{}{}: {}\n".format(name, " "*(length-len(name)), value)
    log = log[:-1]
    logger.info(log)

class ECP5PLL(Module):
    nclkouts_max    = 3
    clki_div_range  = (1, 128+1)
    clkfb_div_range = (1, 128+1)
    clko_div_range  = (1, 128+1)
    clki_freq_range = (    8e6,  400e6)
    clko_freq_range = (3.125e6,  400e6)
    vco_freq_range  = (  400e6,  800e6)

    def __init__(self):
        self.logger = logging.getLogger("ECP5PLL")
        self.logger.info("Creating ECP5PLL.")
        self.reset      = Signal()
        self.locked     = Signal()
        self.clkin_freq = None
        self.vcxo_freq  = None
        self.nclkouts   = 0
        self.clkouts    = {}
        self.config     = {}
        self.params     = {}

    def register_clkin(self, clkin, freq):
        (clki_freq_min, clki_freq_max) = self.clki_freq_range
        assert freq >= clki_freq_min
        assert freq <= clki_freq_max
        self.clkin = Signal()
        if isinstance(clkin, (Signal, ClockSignal)):
            self.comb += self.clkin.eq(clkin)
        else:
            raise ValueError
        self.clkin_freq = freq
        register_clkin_log(self.logger, clkin, freq)

    def create_clkout(self, cd, freq, phase=0, margin=1e-2):
        (clko_freq_min, clko_freq_max) = self.clko_freq_range
        assert freq >= clko_freq_min
        assert freq <= clko_freq_max
        assert self.nclkouts < self.nclkouts_max
        clkout = Signal()
        self.clkouts[self.nclkouts] = (clkout, freq, phase, margin)
        self.comb += cd.clk.eq(clkout)
        create_clkout_log(self.logger, cd.name, freq, margin, self.nclkouts)
        self.nclkouts += 1

    def compute_config(self):
        config = {}
        for clki_div in range(*self.clki_div_range):
            config["clki_div"] = clki_div
            for clkfb_div in range(*self.clkfb_div_range):
                all_valid = True
                vco_freq = self.clkin_freq/clki_div*clkfb_div*1 # clkos3_div=1
                (vco_freq_min, vco_freq_max) = self.vco_freq_range
                if vco_freq >= vco_freq_min and vco_freq <= vco_freq_max:
                    for n, (clk, f, p, m) in sorted(self.clkouts.items()):
                        valid = False
                        for d in range(*self.clko_div_range):
                            clk_freq = vco_freq/d
                            if abs(clk_freq - f) <= f*m:
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
                    compute_config_log(self.logger, config)
                    return config
        raise ValueError("No PLL config found")

    def do_finalize(self):
        config = self.compute_config()
        clkfb  = Signal()
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

        self.stop  = Signal()
        self.reset = Signal()

        clk48 = platform.request("clk48")
        rst_n = platform.request("usr_btn")

        por_count = Signal(16, reset=2**16-1)
        por_done  = Signal()
        self.comb += self.cd_por.clk.eq(clk48)
        self.comb += por_done.eq(por_count == 0)
        self.sync.por += If(~por_done, por_count.eq(por_count - 1))

        sys2x_clk_ecsout = Signal()

        self.submodules.pll = pll = ECP5PLL()
        pll.register_clkin(clk48, 48e6)
        pll.create_clkout(self.cd_sys2x_i, 2*sys_clk_freq)
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

class Timer(Module, AutoCSR):
    """Timer

    Provides a generic Timer core.

    The Timer is implemented as a countdown timer that can be used in various modes:

    - Polling : Returns current countdown value to software
    - One-Shot: Loads itself and stops when value reaches ``0``
    - Periodic: (Re-)Loads itself when value reaches ``0``

    ``en`` register allows the user to enable/disable the Timer. When the Timer is enabled, it is
    automatically loaded with the value of `load` register.

    When the Timer reaches ``0``, it is automatically reloaded with value of `reload` register.

    The user can latch the current countdown value by writing to ``update_value`` register, it will
    update ``value`` register with current countdown value.

    To use the Timer in One-Shot mode, the user needs to:

    - Disable the timer
    - Set the ``load`` register to the expected duration
    - (Re-)Enable the Timer

    To use the Timer in Periodic mode, the user needs to:

    - Disable the Timer
    - Set the ``load`` register to 0
    - Set the ``reload`` register to the expected period
    - Enable the Timer

    For both modes, the CPU can be advertised by an IRQ that the duration/period has elapsed. (The
    CPU can also do software polling with ``update_value`` and ``value`` to know the elapsed duration)
    """

    def __init__(self, width=32):
        self._load = CSRStorage("load", width, description="""Load value when Timer is (re-)enabled.
            In One-Shot mode, the value written to this register specifies the Timer's duration in clock cycles.""")
        self._reload = CSRStorage("reload", width, description="""Reload value when Timer reaches ``0``.
            In Periodic mode, the value written to this register specify the Timer's period in clock cycles.""")
        self._en = CSRStorage("en", 1, description="""Enable flag of the Timer.
            Set this flag to ``1`` to enable/start the Timer.  Set to ``0`` to disable the Timer.""")
        self._update_value = CSRStorage("update_value", 1, description="""Update trigger for the current countdown value.
            A write to this register latches the current countdown value to ``value`` register.""")
        self._value = CSRStatus("value", width, description="""Latched countdown value.
            This value is updated by writing to ``update_value``.""")

        self.submodules.ev = EventManager()
        self.ev.zero       = EventSourceProcess()
        self.ev.finalize()

        value = Signal(width)
        self.sync += [
            If(self._en.storage,
                If(value == 0,
                    # set reload to 0 to disable reloading
                    value.eq(self._reload.storage)
                ).Else(
                    value.eq(value - 1)
                )
            ).Else(
                value.eq(self._load.storage)
            ),
            If(self._update_value.re, self._value.status.eq(value))
        ]
        self.comb += self.ev.zero.trigger.eq(value != 0)

class OrangeCrab:
    revision = "0.2"

    def __init__(self, name=None):
        self.device = "LFE5U-25F-8MG285C"
        self.constraint_manager = ConstraintManager(_io_r0_2, _connectors_r0_2)
        if name is None:
            name = self.__module__.split(".")[-1]
        self.name = name
        self.sources = []
        self.verilog_include_paths = []
        self.output_dir = None
        self.finalized = False
        self.toolchain = LatticeTrellisToolchain()

    def request(self, *args, **kwargs):
        return self.constraint_manager.request(*args, **kwargs)

    def lookup_request(self, *args, **kwargs):
        return self.constraint_manager.lookup_request(*args, **kwargs)

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

        self.add_period_constraint(self.lookup_request("clk48", loose=True), 1e9/48e6)

        self.finalized = True

    def add_source(self, filename, language=None, library=None):
        if language is None:
            language = "verilog"
        if library is None:
            library = "work"
        for f, _, _ in self.sources:
            if f == filename:
                return
        self.sources.append((os.path.abspath(filename), language, library))

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

    def get_verilog(self, fragment, **kwargs):
        return convert(fragment,
            self.constraint_manager.get_io_signals(),
            create_clock_domains=False,
            special_overrides=self.toolchain.special_overrides,
            attr_translate=self.toolchain.attr_translate,
            **kwargs)

    def build(self, *args, **kwargs):
        return self.toolchain.build(self, *args, **kwargs)

class Waltraud(Module):
    mem_map = {
        "rom":      0x00000000,
        "sram":     0x20000000,
        "main_ram": 0x40000000,
        "csr":      0xf0000000,
    }

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
            "timer0": 3,
        },
        # Interrupt parameters
        irq_n_irqs           = 32,
        irq_reserved_irqs    = {
            "timer0": 3,
            "uart":   4,
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

        self.submodules.irq = SoCIRQHandler(
            n_irqs        = irq_n_irqs,
            reserved_irqs = irq_reserved_irqs,
        )

        self.logger = logging.getLogger("Waltraud")
        self.logger.info("FPGA device : {}.".format(self.platform.device))
        self.logger.info("System clock: {:3.2f}MHz.".format(self.sys_clk_freq / 1e6))
        self.logger.info(colorer("-"*80, color="bright"))

        self.constants = {}
        self.add_config("CLOCK_FREQUENCY", int(self.sys_clk_freq))

        # Add SoCController
        self.submodules.ctrl = SoCController()
        self.csr.add("ctrl", use_loc_if_exists=True)

        # Add CPU
        self.submodules.cpu = PicoRV32(self.platform, "minimal")
        for n, (origin, size) in enumerate(self.cpu.io_regions.items()):
            self.bus.add_region("io{}".format(n), SoCIORegion(origin=origin, size=size, cached=False))
        self.mem_map.update(self.cpu.mem_map)
        self.cpu.set_reset_address(self.mem_map["rom"])
        for n, cpu_bus in enumerate(self.cpu.periph_buses):
            self.bus.add_master(name="cpu_bus{}".format(n), master=cpu_bus)
        self.csr.add("cpu", use_loc_if_exists=True)
        for name, loc in self.cpu.interrupts.items():
            self.irq.add(name, loc)
        if hasattr(self.ctrl, "reset"):
            self.comb += self.cpu.reset.eq(self.ctrl.reset)
        if hasattr(self.cpu, "nop"):
            self.add_constant("CONFIG_CPU_NOP", self.cpu.nop)

        # Add integrated ROM and SRAM
        self.add_rom("rom",  self.mem_map["rom"],   0x8000)
        self.add_ram("sram", self.mem_map["sram"], 0x10000)

        # Add UART
        usb_pads = self.platform.request("usb")
        usb_iobuf = IoBuf(usb_pads.d_p, usb_pads.d_n, usb_pads.pullup)
        self.submodules.uart = CDCUsb(usb_iobuf)
        self.csr.add("uart_phy", use_loc_if_exists=True)
        self.csr.add("uart", use_loc_if_exists=True)
        self.irq.add("uart", use_loc_if_exists=True)

        # Add Timer
        self.submodules.timer0 = Timer()
        self.csr.add("timer0", use_loc_if_exists=True)
        self.irq.add("timer0", use_loc_if_exists=True)

        # Add CSR bridge
        self.add_csr_bridge(self.mem_map["csr"])

        self.submodules.crg = CRG(self.platform, self.sys_clk_freq)

        self.submodules.ddrphy = ECP5DDRPHY(self.platform.request("ddram"), sys_clk_freq=self.sys_clk_freq)
        self.csr.add("ddrphy", use_loc_if_exists=True)
        self.comb += self.crg.stop.eq(self.ddrphy.init.stop)
        self.comb += self.crg.reset.eq(self.ddrphy.init.reset)
        self.add_sdram("sdram", self.ddrphy, MT41K64M16(self.sys_clk_freq, "1:2"), self.mem_map["main_ram"], size=0x40000000, l2_cache_size=2048)

    def add_constant(self, name, value=None):
        name = name.upper()
        if name in self.constants.keys():
            self.logger.error("{} Constant already {}.".format(colorer(name), colorer("declared", color="red")))
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

    def add_rom(self, name, origin, size, contents=[]):
        self.add_ram(name, origin, size, contents, mode="r")

    def initialize_rom(self, data):
        self.rom.mem.init = data

    def add_csr_bridge(self, origin):
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

    def add_sdram(self, name, phy, module, origin, size=None,
        l2_cache_size           = 8192,
        l2_cache_min_data_width = 128,
        l2_cache_reverse        = True,
        l2_cache_full_memory_we = True):

        # LiteDRAM core
        self.submodules.sdram = LiteDRAMCore(
            phy             = phy,
            geom_settings   = module.geom_settings,
            timing_settings = module.timing_settings,
            clk_freq        = self.sys_clk_freq,
        )
        self.csr.add("sdram")

        # Compute/Check SDRAM size
        sdram_size = 2**(module.geom_settings.bankbits + module.geom_settings.rowbits + module.geom_settings.colbits) * phy.settings.databits // 8
        if size is not None:
            sdram_size = min(sdram_size, size)

        # Add SDRAM region
        self.bus.add_region("main_ram", SoCRegion(origin=origin, size=sdram_size))

        # Request a LiteDRAM native port.
        port = self.sdram.crossbar.get_port()
        port.data_width = 2**int(math.log2(port.data_width))

        # Create Wishbone Slave.
        wb_sdram = WishboneInterface()
        self.bus.add_slave("main_ram", wb_sdram)

        # L2 Cache
        if l2_cache_size != 0:
            # Insert L2 cache inbetween Wishbone bus and LiteDRAM
            l2_cache_size = max(l2_cache_size, int(2 * port.data_width / 8))
            l2_cache_size = 2**int(math.log2(l2_cache_size))
            l2_cache_data_width = max(port.data_width, l2_cache_min_data_width)
            l2_cache            = WishboneCache(
                cachesize = l2_cache_size // 4,
                master    = wb_sdram,
                slave     = WishboneInterface(l2_cache_data_width),
                reverse   = l2_cache_reverse,
            )
            if l2_cache_full_memory_we:
                l2_cache = FullMemoryWE()(l2_cache)
            self.submodules.l2_cache = l2_cache
            litedram_wb = self.l2_cache.slave
        else:
            litedram_wb = WishboneInterface(port.data_width)
            self.submodules += WishboneConverter(wb_sdram, litedram_wb)
        self.add_config("L2_SIZE", l2_cache_size)

        # Wishbone Slave <--> LiteDRAM bridge
        self.submodules.wishbone_bridge = LiteDRAMWishbone2Native(litedram_wb, port, base_address = self.bus.regions["main_ram"].origin)

    def do_finalize(self):
        self.logger.info(colorer("-"*80, color="bright"))
        self.logger.info(self.bus)
        self.logger.info(self.csr)
        self.logger.info(self.irq)
        self.logger.info(colorer("-"*80, color="bright"))

        if len(self.bus.masters) and len(self.bus.slaves):
            # If 1 bus_master, 1 bus_slave and no address translation, use InterconnectPointToPoint.
            if ((len(self.bus.masters) == 1) and (len(self.bus.slaves) == 1) and (next(iter(self.bus.regions.values())).origin == 0)):
                self.submodules.bus_interconnect = WishboneInterconnectPointToPoint(
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
            self.bus.logger.info("Interconnect: {} ({} <-> {}).".format(colorer(self.bus_interconnect.__class__.__name__), colorer(len(self.bus.masters)), colorer(len(self.bus.slaves))))

        self.add_constant("CONFIG_BUS_STANDARD",      self.bus.standard.upper())
        self.add_constant("CONFIG_BUS_DATA_WIDTH",    self.bus.data_width)
        self.add_constant("CONFIG_BUS_ADDRESS_WIDTH", self.bus.address_width)

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
                origin  = (self.bus.regions["csr"].origin + self.csr.paging*mapaddr),
                busword = self.csr.data_width,
                obj     = csrs,
            ))

        # Add Memory regions
        for name, memory, mapaddr, mmap in self.csr_bankarray.srams:
            self.csr.add_region(name + "_" + memory.name_override, SoCCSRRegion(
                origin  = (self.bus.regions["csr"].origin + self.csr.paging*mapaddr),
                busword = self.csr.data_width,
                obj     = memory,
            ))

        # Sort CSR regions by origin
        self.csr.regions = {k: v for k, v in sorted(self.csr.regions.items(), key=lambda item: item[1].origin)}

        # Add CSRs / Config items to constants
        for name, constant in self.csr_bankarray.constants:
            self.add_constant(name + "_" + constant.name, constant.value.value)

        for name, loc in sorted(self.irq.locs.items()):
            if name in self.cpu.interrupts.keys():
                continue
            if hasattr(self, name):
                module = getattr(self, name)
                if not hasattr(module, "ev"):
                    self.logger.error("EventManager {} in {} SubModule.".format(colorer("not found", color="red"), colorer(name)))
                    raise
                self.comb += self.cpu.interrupt[loc].eq(module.ev.irq)
            self.add_constant(name + "_INTERRUPT", loc)

        # Retro-compatibility
        for region in self.bus.regions.values():
            region.length = region.size
            region.type   = "cached" if region.cached else "io"
            if region.linker:
                region.type += "+linker"

    def build(self, *args, **kwargs):
        self.build_name = kwargs.pop("build_name", self.platform.name)
        kwargs.update({"build_name": self.build_name})
        return self.platform.build(self, *args, **kwargs)

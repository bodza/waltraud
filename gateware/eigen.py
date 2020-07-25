import builtins as _builtins
from collections import defaultdict, Iterable, OrderedDict
from copy import copy
from enum import IntEnum
from functools import reduce
from itertools import combinations
from math import gcd
from operator import itemgetter, or_
import re as _re

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
        return gcd(gcd_multiple(numbers[:s]), gcd_multiple(numbers[s:]))

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
            self.nbits = _builtins.max(bits_for(min, self.signed), bits_for(max, self.signed))
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

import math
from typing import List, Union

import uuid

from itertools import combinations

from z3 import Bool, BoolRef
from z3 import Or, And, Not, Xor, Implies

def pad(l, length)->BoolRef:                           #adds a padding in the number as boolean
    assert length > 0 and length >= len(l), '\nl:\t{}\nlength:\t{}'.format(l, length)

    return [False for _ in range(length - len(l))] + l

def __is_bool(val: Union[bool, BoolRef]) -> bool:                                            #checks if it's bool or boolRef
    return isinstance(val, bool) or isinstance(val, BoolRef)

def get_bool_lists(*ll):                                                                 #a list of int into a list of boolList
    ll = list(ll)
    for i in range(len(ll)):
        if isinstance(ll[i], int):
            ll[i] = int2boolList(ll[i])
        elif not isinstance(ll[i], list):
            assert __is_bool(ll[i])
            ll[i] = [ll[i]]
    return ll

def bool2int(l) -> int:                                                 #bool to int (example, [F,T,F,T]->5)
    result = 0
    l_b = []
    for _, l_i in enumerate(l):
        if str(l_i) == "True":
            l_b.append(True)
        else:
            l_b.append(False)

    for digits in l_b:
        result = (result << 1) | bool(int(digits))
    return result

def int2boolList(n) -> List[bool]:                                                     #int to bool (example, 5->[T;F;T])
    result = []
    base2 = format(n, "b")
    for bit in base2:
        if bit == "1":
            result.append(True)
        else:
            result.append(False)
    return result

def all_F(l) -> BoolRef:                                           #all False
    return And([Not(b) for b in l])

def at_least_one_T(bools:List[Bool]) -> BoolRef:                                      #al least 1 (min 1 T)
    return Or(bools)

def at_most_one_T(bools) -> BoolRef:                                       #at most 1  (max 1 T)
    ### HEULE ENCODING
    l = len(bools)
    result = []
    if l <= 3:  ###base case
        return And([Not(And(b1, b2)) for b1, b2 in combinations(bools, 2)])
    ###recursive case
    y = Bool(f"yamo_{str(uuid.uuid4())}")
    first = bools[:2].append(y)
    result = [Not(And(b1, b2)) for b1, b2 in combinations(first, 2)]

    second = bools[2:].append(Not(y))
    result += at_most_one_T(second)

    return And(result)

def exactly_one_T(bools) -> BoolRef:                                      # 1 T
    return And(at_most_one_T(bools) + [at_least_one_T(bools)])

def ne(l1, l2) -> BoolRef:                                                            #not equal
    l1, l2 = get_bool_lists(l1, l2)
    min_len = min(len(l1), len(l2))
    start_idx = [len(l1) - min_len, len(l2) - min_len]

    c1 = at_least_one_T(l1[:start_idx[0]])
    c2 = at_least_one_T(l2[:start_idx[1]])
    return Or([c1, c2] + [Xor(l1i, l2i) for l1i, l2i in zip(l1, l2)])

def eq(l1, l2) -> BoolRef:                                        #equal
    l1, l2 = get_bool_lists(l1, l2)
    max_len = max(len(l1), len(l2))
    l1 = pad(l1, max_len)
    l2 = pad(l2, max_len)

    return And([Not(Xor(l1[i], l2[i])) for i in range(max_len)])

def __gte_same_len(l1, l2) -> BoolRef:      #l1>=l2 with same len
    ### AND-CSE Encoding: Common SubExpression Elimination
    if len(l1) == 1:
        return Or(l1[0], Not(l2[0]))

    x = [Bool(f"xge_{str(uuid.uuid4())}") for i in range(len(l1) - 1)]

    first = Or(l1[0], Not(l2[0]))
    second = (x[0] == Not(Xor(l1[0], l2[0])))
    third = []
    for i in range(len(l1) - 2):
        third.append(x[i + 1] == (And(x[i], Not(Xor(l1[i + 1], l2[i + 1])))))
    fourth = []
    for i in range(len(l1) - 1):
        fourth.append(Implies(x[i], Or(l1[i + 1], Not(l2[i + 1]))))

    return And(first, second, And(third), And(fourth))

def gte(l1, l2) -> BoolRef:                                            #l1>=l2
    l1, l2 = get_bool_lists(l1, l2)
    min_len = min(len(l1), len(l2))
    start_idx = [len(l1) - min_len, len(l2) - min_len]

    c1 = at_least_one_T(l1[:start_idx[0]])
    c2 = all_F(l2[:start_idx[1]])

    return Or(c1, And(c2, __gte_same_len(l1[start_idx[0]:], l2[start_idx[1]:])))

def __gt_same_len(l1:List[Bool], l2:List[Bool]) -> BoolRef:        #l1>l2 same len
    ### AND-CSE Encoding: Common SubExpression Elimination
    if len(l1) == 1:
        return And(l1[0], Not(l2[0]))

    x = [Bool(f"x_{i}") for i in range(len(l1) - 1)]

    first = And(l1[0], Not(l2[0]))
    second = (x[0] == Not(Xor(l1[0], l2[0])))
    third = []
    for i in range(len(l1) - 2):
        third.append(x[i + 1] == (And(x[i], Not(Xor(l1[i + 1], l2[i + 1])))))
    fourth = []
    for i in range(len(l1) - 1):
        fourth.append(And(x[i], And(l1[i + 1], Not(l2[i + 1]))))

    return Or(first, And(second, And(third), Or(fourth)))

def gt(l1:List[Bool], l2:List[Bool]) -> BoolRef:                                      #l1>l2
    l1, l2 = get_bool_lists(l1, l2)
    min_len = min(len(l1), len(l2))
    start_idx = [len(l1) - min_len, len(l2) - min_len]

    c1 = at_least_one_T(l1[:start_idx[0]])
    c2 = all_F(l2[:start_idx[1]])

    return Or(c1, And(c2, __gt_same_len(l1[start_idx[0]:], l2[start_idx[1]:])))

def lte(l1, l2) -> BoolRef:                                  #l1<=l2                             
    return gte(l1=l2, l2=l1)

def lt(l1, l2) -> BoolRef:                                   #l1<l2
    return gt(l1=l2, l2=l1)

def sum_b(l1, l2) -> BoolRef:                                #binary sum (into a Z3 formula)
    l1, l2 = get_bool_lists(l1, l2)
    max_len = max(len(l1), len(l2))
    l1 = pad(l1, max_len)
    l2 = pad(l2, max_len)
    result = []

    carry_in = False
    carry_out = False

    for i in range(max_len - 1, -1, -1):
        a = l1[i]
        b = l2[i]
        result.append(Xor(Xor(a, b), carry_in))

        carry_out = Or(And(Xor(a, b), carry_in), And(a, b))
        carry_in = carry_out
    result.append(carry_in)
    result = result[::-1]

    return result

def sub_b(l1, l2) -> BoolRef:                                #binary subtraction
    l1, l2 = get_bool_lists(l1, l2)
    max_len = max(len(l1), len(l2))
    l1 = pad(l1, max_len)
    l2 = pad(l2, max_len)
    result = []

    borr_in = False
    borr_out = False

    for i in range(len(l1) - 1, -1, -1):
        a = l1[i]
        b = l2[i]
        result.append(Xor(Xor(a, b), borr_in))

        borr_out = Or(And(Not(Xor(a, b)), borr_in), And(Not(a), b))
        borr_in = borr_out

    result = result[::-1]
    return result

def sum_b_list(l) -> BoolRef:
    result=l[0]
    for i in range(1,len(l)):
        result = sum_b(result,l[i])
    return result

def enable(l,en)->BoolRef:
    return [And(i,en) for i in l]

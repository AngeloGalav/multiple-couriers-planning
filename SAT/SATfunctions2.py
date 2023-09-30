import math
from typing import List, Union

import uuid

from itertools import combinations

from z3 import Bool, BoolRef
from z3 import Or, And, Not, Xor, Implies

#adds a padding in the number as boolean
def pad(l, length)->BoolRef:                           
    assert length > 0 and length >= len(l), '\nl:\t{}\nlength:\t{}'.format(l, length)

    return [False for _ in range(length - len(l))] + l

#checks if it's bool or boolRef
def __is_bool(val: Union[bool, BoolRef]) -> bool:                                            
    return isinstance(val, bool) or isinstance(val, BoolRef)

#a list of int into a list of boolList
def get_bool_lists(*ll):
    ll = list(ll)
    for i in range(len(ll)):
        if isinstance(ll[i], int):
            ll[i] = int2boolList(ll[i])
        elif not isinstance(ll[i], list):
            assert __is_bool(ll[i])
            ll[i] = [ll[i]]
    return ll

#bool to int (example, [F,T,F,T]->5)
def bool2int(l) -> int:                                                 
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

#int to bool (example, 5->[T;F;T])
def int2boolList(n) -> List[bool]:                                                     
    result = []
    base2 = format(n, "b")
    for bit in base2:
        if bit == "1":
            result.append(True)
        else:
            result.append(False)
    return result

#all False
def all_F(l) -> BoolRef:                                           
    return And([Not(b) for b in l])

#al least 1 (min 1 T)
def at_least_one_T(bools) -> BoolRef:                                      
    return Or(bools)

#at most 1  (max 1 T)
def at_most_one_T(bools) -> BoolRef:
    if len(bools) <= 4: # base case
        return And([Not(And(b1, b2)) for b1, b2 in combinations(bools, 2)])
    
    # recursive step
    y = Bool(f"yamo_{str(uuid.uuid4())}")
    first = bools[:3]
    first.append(y)
    c_first = at_most_one_T(first)

    last = bools[3:]
    last.insert(0, Not(y))
    c_last = at_most_one_T(last)

    return And(c_first, c_last)

# 1 T
def exactly_one_T(bools) -> BoolRef:                                      
    return And(at_most_one_T(bools), at_least_one_T(bools))

#not equal
def ne(l1, l2) -> BoolRef:                                                            
    l1, l2 = get_bool_lists(l1, l2)
    min_len = min(len(l1), len(l2))
    start_idx = [len(l1) - min_len, len(l2) - min_len]

    c1 = at_least_one_T(l1[:start_idx[0]])
    c2 = at_least_one_T(l2[:start_idx[1]])
    return Or([c1, c2] + [Xor(l1i, l2i) for l1i, l2i in zip(l1, l2)])

#equal
def eq(l1, l2) -> BoolRef:                                        
    l1, l2 = get_bool_lists(l1, l2)
    max_len = max(len(l1), len(l2))
    l1 = pad(l1, max_len)
    l2 = pad(l2, max_len)

    return And([l1[i] == l2[i] for i in range(max_len)])

#l1>=l2 with same len
def __gte_same_len(l1, l2) -> BoolRef:
    if len(l1) == 1:
        return Or(l1[0], Not(l2[0]))

    # given two encodings [a0, ..., ak] and [b0, ..., bk]
    # x[i] is true <--> aj = bj forall j <= i
    x = [Bool(f"xgtsl_{str(uuid.uuid4())}") for i in range(len(l1) - 1)]
    xConstr = []
    xConstr.append(x[0] == (l1[0] == l2[0]))
    for i in range(len(l1) - 2):
        xConstr.append(x[i + 1] == (And(x[i], l1[i + 1] == l2[i + 1])))

    # gtConstr[i] holds if all bits until i are the same (x[i] is true) and ai+1 = true and bi+1 = false
    # if atleast one of these constraints holds or all bits are the same 
    # (x[k-1] and (l1[k]==l2[k])) then a > b
    gteConstr = []
    gteConstr.append(And(l1[0], Not(l2[0])))
    for i in range(len(l1) - 1):
        gteConstr.append(And(x[i], And(l1[i + 1], Not(l2[i + 1]))))
    gteConstr.append(And(x[-1], l1[-1] == l2[-1]))

    return And(And(xConstr), Or(gteConstr))

#l1>=l2
def gte(l1, l2) -> BoolRef:                                            
    l1, l2 = get_bool_lists(l1, l2)
    min_len = min(len(l1), len(l2))
    start_idx = [len(l1) - min_len, len(l2) - min_len]

    c1 = at_least_one_T(l1[:start_idx[0]])
    c2 = all_F(l2[:start_idx[1]])

    return Or(c1, And(c2, __gte_same_len(l1[start_idx[0]:], l2[start_idx[1]:])))

#l1>l2 same len
def __gt_same_len(l1, l2) -> BoolRef:
    if len(l1) == 1:
        return And(l1[0], Not(l2[0]))

    # given two encodings [a0, ..., ak] and [b0, ..., bk]
    # x[i] is true <--> aj = bj forall j <= i
    x = [Bool(f"xgtsl_{str(uuid.uuid4())}") for i in range(len(l1) - 1)]
    xConstr = []
    xConstr.append(x[0] == (l1[0] == l2[0]))
    for i in range(len(l1) - 2):
        xConstr.append(x[i + 1] == (And(x[i], l1[i + 1] == l2[i + 1])))

    # gtConstr[i] holds if all bits until i are the same (x[i] is true) and ai+1 = true and bi+1 = false
    # if atleast one of these constraints holds, then a > b
    gtConstr = []
    gtConstr.append(And(l1[0], Not(l2[0])))
    for i in range(len(l1) - 1):
        gtConstr.append(And(x[i], And(l1[i + 1], Not(l2[i + 1]))))

    return And(And(xConstr), Or(gtConstr))

#l1>l2
def gt(l1, l2) -> BoolRef:                                      
    l1, l2 = get_bool_lists(l1, l2)
    min_len = min(len(l1), len(l2))
    start_idx = [len(l1) - min_len, len(l2) - min_len]

    c1 = at_least_one_T(l1[:start_idx[0]])
    c2 = all_F(l2[:start_idx[1]])

    return Or(c1, And(c2, __gt_same_len(l1[start_idx[0]:], l2[start_idx[1]:])))

#l1<=l2
def lte(l1, l2) -> BoolRef:                                                              
    return gte(l1=l2, l2=l1)

#l1<l2
def lt(l1, l2) -> BoolRef:                                   
    return gt(l1=l2, l2=l1)

#binary sum (into a Z3 formula)
def sum_b(l1, l2) -> BoolRef:                                
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

#binary subtraction
def sub_b(l1, l2) -> BoolRef:
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

# inputs: list of binary encodings and max value
# output: expression maxEl = max(elems)
def max_elem(elems, maxEl):
    isPartOf = Or([eq(el, maxEl) for el in elems])
    isGreaterEqual = And([gte(maxEl, el) for el in elems])

    return And(isPartOf, isGreaterEqual)

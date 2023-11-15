from math import sqrt, log
from contracts import contract, new_contract

@preconditions(lambda i: isinstance(i, int))
def double(i):
    return 2*i

@preconditions(
    lambda i: isinstance(i, int) and i > 0,
    )
def double(i):
    return 2*i

@preconditions(
    lambda a: isinstance(a, float) and a >= 0,
    lambda b: isinstance(b, float) and b >= 0,
    )
def area(a, b):
    return a*b

scores = {}
@preconditions(
    lambda color, _colors=['RED', 'GREEN', 'BLUE']: color in _colors
    )
def get_color_score(color):
    return scores[color]

@deal.pre(lambda *args: all(arg > 0 for arg in args))
def sum_positive(*args):
    return sum(args)
sum_positive(1, 2, 3, 4)
sum_positive(1, 2, -3, 4)

@deal.post(lambda x: x > 0)
def always_positive_sum(*args):
    return sum(args)
always_positive_sum(2, -3, 4)#3
always_positive_sum(2, -3, -4) # PostContractError:

@deal.ensure(lambda x, result: x != result)
def double(x):
    return x * 2
double(2)# 4
double(0) # PostContractError: expected x != result (where result=0, x=0)

@contract(x='int,>=0',returns='int,>=0')
def perfect_sqrt(x):
    retval = sqrt(x)
    iretval = int(retval)
    return iretval if iretval == retval else retval

def max_length(strings: list[str]) -> int:
    """Return the maximum length of a string in the given list of strings.
    Preconditions:
      - strings != []
    """
    assert strings != []  # Check the precondition
    max_so_far = -1
    for s in strings:
        if len(s) > max_so_far:
            max_so_far = len(s)
    return max_so_far

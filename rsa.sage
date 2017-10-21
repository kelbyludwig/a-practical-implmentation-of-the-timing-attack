#
# globals for our experiments
#

# our modulus and ring
p = next_prime(randint(2^256, 2^257))
q = next_prime(p)
N = p * q

#
# our montgomery reduction parameters
#

# option 1 for montgomery parameters
# note: using these parameters will greatly increase the number of reductions
# required across experiments!
# n = len(N.bits())
# b = 2
# R = b ^ n

# option 2 montgomery parameters
Rb = ((len(N.bits()) // 8) + 1) * 8
R = 1 << Rb
n = len(Integer(R).bits())

g, s, t = xgcd(R, N)
Ninv = -t
Rinv = s

assert(gcd(N, R) == 1)
assert(g == 1)
assert(R*Rinv - N*Ninv == 1)

#
# montgomery multiplication and exponentiation code
#

def to_mont(x):
    return Integer((x * R) % N)


def mon_prod(a, b):
    t = (a * b) % R
    m = (t * Ninv) % R
    u = (a * b + m * N) / R
    if u >= N:
        return 1, Integer(u - N)
    else:
        return 0, Integer(u)


def mon_mult(a, b):
    ab = to_mont(a)
    bb = to_mont(b)
    _, xb = mon_prod(ab, bb)
    _, x = mon_prod(xb, 1)
    return x


def mon_exp(a, x, return_count=False):
    """
    mon_exp computes a^x (mod N) using the "square-and-multiply" algorithm on
    numbers in the montgomery form. Providing the parameter `return_count=True`
    will return the tuple (cnt, a^x (mod N)), where cnt is the number of extra
    reductions that were performed over the course of computing the
    exponentiation.

    Because I YOLO Sage'd this, it is probably not more efficient than normal
    "square-and-multiply" exponentiation. meh.
    """
    ab = to_mont(a)
    xb = (1 * R) % N
    bts = Integer(x).bits()
    ex_count = 0
    for bi in reversed(bts):
        ex1, xb = mon_prod(xb, xb)
        if bi == 1:
            ex2, xb = mon_prod(ab, xb)
        ex_count += ex1 + ex2
    ex, ret = mon_prod(xb, 1)
    if return_count:
        return ex_count+ex, ret
    return ret


def experiment_target_mult2():
    """
    This experiment compares the number of extra reductions across four
    different oracle calls. These four calls are combinations of two messages
    (one that requires an extra reduction when cubed and one that does not) and
    two secrets (one that has a 1 in the second msb and one that has a 0).

    This experiment is not directly related to the "A practical
    implmentation..." paper but something I was just curious about.
    """
    secret1 = randint(0, N)
    bitlen = len(Integer(secret1).bits())
    bit2mask = 1 << (bitlen-2)
    while (secret1 & bit2mask) != 0:
        secret1 = randint(0, N)
    secret2 = secret1 | bit2mask
    print("secret1: %s" % bin(secret1))
    print("secret2: %s" % bin(secret2))
    
    requires_extra_reduction_mes, no_extra_reduction_mes = 0, 0
    while requires_extra_reduction_mes == 0 or no_extra_reduction_mes == 0: 
        x = randint(0, N)
        expp, _ = mon_exp(x, 3, True)
        if expp == 1:
            requires_extra_reduction_mes = x
        if expp == 0:
            no_extra_reduction_mes = x

    ex1, _ = mon_exp(requires_extra_reduction_mes, secret1, True)
    ex2, _ = mon_exp(requires_extra_reduction_mes, secret2, True)
    ex3, _ = mon_exp(no_extra_reduction_mes, secret1, True)
    ex4, _ = mon_exp(no_extra_reduction_mes, secret2, True)

    print("requires extra + secret with 0 as second bit:          %d" % ex1)
    print("requires extra + secret with 1 as second bit:          %d" % ex2)
    print("doest not require extra + secret with 0 as second bit: %d" % ex3)
    print("doest not require extra + secret with 1 as second bit: %d" % ex4)


def experiment_target_mult1():
    """
    This experiment demonstrates one of the results from the paper "A practical
    implementation of the timing attack" by Dhem et. al.

    Given a RSA "signing" oracle with a randomly generated secret, this experiment
    generates two sets of messages "extra_set" and "no_extra_set". Messages in
    "extra_set" require an extra montgomery reduction when cubed using the same
    modulus as the oracle. Messages in "no_extra_set" do not require an extra
    reduction.

    In this experiment, the oracle will return the number of extra reductions
    needed to perform exponentiation under the secret. This allows to us
    simulate additional time required by the oracle for a given message.

    After each set contains enough samples, each set is submitted to the oracle
    and the average number of extra reductions are logged for each set. This
    experiment demonstrates that it is highly likely that the "extra_set" will
    require more extra reductions on average during exponentiation.
    """
    # randomly generate a secret
    secret = randint(0, N)

    # generate messages and place them into two sets: one set contains messages
    # that require an "extra reduction" when cubed, and the other set does not.
    extra_set = set([])
    no_extra_set = set([])
    num_samples = 1000
    while len(extra_set) <= num_samples or len(no_extra_set) <= num_samples:
        x = randint(0, N)
        expp, _ = mon_exp(x, 3, True)
        if len(extra_set) <= num_samples and expp == 1:
            extra_set.add(x)
        if len(no_extra_set) <= num_samples and expp == 0:
            no_extra_set.add(x)

    # measure the average number of reductions required for messages in the
    # "extra_set"
    mean_extra = 0.0
    for e in extra_set:
        xx, _ = mon_exp(e, secret, True)
        mean_extra += xx
    mean_extra = mean_extra / len(extra_set)
    print("mean reductions for extra_set %s" % mean_extra)

    # measure the average number of reductions required for messages in the
    # "no_extra_set"
    no_mean_extra = 0.0
    for e in no_extra_set:
        xx, _ = mon_exp(e, secret, True)
        no_mean_extra += xx
    no_mean_extra = no_mean_extra / len(no_extra_set)
    print("mean reductions for no_extra_set %s" % no_mean_extra)


def test_for_correctness():
    """
    test to confirm my montmul and montexp functions are working properly.
    """
    for _ in range(1000):
        a = randint(0, N)
        b = randint(0, N)
        exp = (a * b) % N
        res = mon_mult(a, b)
        assert(exp == res)
        exp = pow(a, b, N)
        res = mon_exp(a, b)
        assert(exp == res)

import math
import primes
from random import randint
from Crypto.Util.number import getRandomRange, bytes_to_long, long_to_bytes, size, inverse, GCD
from fractions import gcd
import hashlib

def invmod(a, p, maxiter=1000000):
    """The multiplicitive inverse of a in the integers modulo p:
         a * b == 1 mod p
       Returns b.
       (http://code.activestate.com/recipes/576737-inverse-modulo-p/)"""
    if a == 0:
        raise ValueError('0 has no inverse mod %d' % p)
    r = a
    d = 1
    for i in xrange(min(p, maxiter)):
        d = ((p // r + 1) * d) % p
        r = (d * a) % p
        if r == 1:
            break
    else:
        raise ValueError('%d has no inverse mod %d' % (a, p))
    return d

def inModN(a,n):
    return a < n and a > 0

def inModNStar(a,n):
    g = gcd(a,n)
    return g == 1 and inModN(a,n)

def getRandomModN(n):
    a = 0
    while not inModN(a,n):
        a = randint(1,n-1)
    return a

def getRandomModNStar(n):
    a = 0
    while not inModNStar(a,n):
        a = randint(1,n-1)
    return a

def getRandomModNPrime(n):
    a = 0
    while not inModNStar(a,n) and inModN(a,n):
        a = primes.generate_prime(long(round(math.log(n, 2))))
    return a

def hash(a,b):
    h = hashlib.sha224()
    h.update(str(a))
    h.update(str(b))
    return bytes_to_long(h.hexdigest())

def modpow(base, exponent, modulus):
    """Modular exponent:
         c = b ^ e mod m
       Returns c.
       (http://www.programmish.com/?p=34)"""
    result = 1
    while exponent > 0:
        if exponent & 1 == 1:
            result = (result * base) % modulus
        exponent = exponent >> 1
        base = (base * base) % modulus
    return result

class PrivateKey(object):

    def __init__(self, p, q, n):
        self.l = (p-1) * (q-1)
        self.m = invmod(self.l, n)

    def __repr__(self):
        return '<PrivateKey: %s %s>' % (self.l, self.m)

class PublicKey(object):

    @classmethod
    def from_n(cls, n):
        return cls(n)

    def __init__(self, n):
        self.n = n
        self.n_sq = n * n
        self.g = n + 1

    def __repr__(self):
        return '<PublicKey: %s>' % self.n

def generate_keypair(bits):
    p = primes.generate_prime(bits / 2)
    q = primes.generate_prime(bits / 2)
    n = p * q
    return PrivateKey(p, q, n), PublicKey(n)

def encrypt(pub, plain):
    while True:
        r = primes.generate_prime(long(round(math.log(pub.n, 2))))
        if r > 0 and r < pub.n:
            break
    x = pow(r, pub.n, pub.n_sq)
    cipher = (pow(pub.g, plain, pub.n_sq) * x) % pub.n_sq
    return cipher

def encryptFactors(pub, plain):
    while True:
        r = primes.generate_prime(long(round(math.log(pub.n, 2))))
        if r > 0 and r < pub.n:
            break
    x = pow(r, pub.n, pub.n_sq)
    cipher = (pow(pub.g, plain, pub.n_sq) * x) % pub.n_sq
    return cipher, r

def genZKP(pub, plain, cipher, r):
    proof = {}
    proof["n"] = pub.n
    proof["n2"] = pub.n_sq
    proof["g"] = pub.g
    versions = {}
    x = getRandomModN(pub.n)
    s = getRandomModNStar(pub.n)
    u = (pow(pub.g, x, pub.n_sq) * pow(s, pub.n, pub.n_sq)) % pub.n_sq

    e = hash(x,s) % pub.n

    comp = (x - e*plain) % pub.n
    v = comp % pub.n
    w = (s * pow(invmod(r,pub.n), e, pub.n) * pow(pub.g, comp, pub.n) / pow(pub.g, pub.n, pub.n)) % pub.n

    proof["x"] = x
    proof["s"] = s
    proof["u"] = u
    proof["e"] = e
    proof["v"] = v
    proof["w"] = w

    result = (pow(pub.g, v, pub.n_sq)*pow(cipher, e, pub.n_sq)*pow(w, pub.n, pub.n_sq)) % pub.n_sq
    # print "cipher: ",cipher
    # print "u     : ",u
    # print "result: ",result
    #
    # print "u == result: ",u == result
    return proof

def genZKPset(pub, plain, cipher, r):
    proof = {}
    proof["n"] = pub.n
    proof["n2"] = pub.n_sq
    proof["g"] = pub.g
    proof["S"] = []
    if (plain == 0):
        mj = 1
    else:
        mj = 0

    p = getRandomModNStar(pub.n)
    ej = getRandomModN(pub.n)
    vj = getRandomModNStar(pub.n)

    ui = pow(p,pub.n,pub.n_sq)
    uj = (pow(vj,pub.n,pub.n_sq) * pow((pow(pub.g,mj,pub.n_sq) / cipher),ej,pub.n_sq)) % pub.n_sq

    e = hash(ej,vj) % pub.n

    ei = (e - ej) % pub.n
    vi = (p * pow(r,ei,pub.n) * (pow(g,ei,pub.n) / pow(g,pub.n,pub.n))) % pub.n
    proof["e"] = e

    i = {
        "u": ui,
        "v": vi
        "e": ei
        "m": plain
    }
    j = {
        "u": uj,
        "v": vj
        "e": ej
        "m": mj
    }

    if (plain == 0):
        proof["S"].append(i)
        proof["S"].append(j)
    else:
        proof["S"].append(j)
        proof["S"].append(i)

    print mj
    print pow(vj,pub.n,pub.n)
    print (uj * pow((c/pow(pub.g,mj,pub.n_sq)), ej , pub.n_sq)) % pub.n_sq

    print plain
    print pow(vi,pub.n,pub.n)
    print (ui * pow((c/pow(pub.g,mi,pub.n_sq)), ei , pub.n_sq)) % pub.n_sq


    return proof

def e_add(pub, a, b):
    """Add one encrypted integer to another"""
    return a * b % pub.n_sq

def e_add_const(pub, a, n):
    """Add constant n to an encrypted integer"""
    return a * modpow(pub.g, n, pub.n_sq) % pub.n_sq

def e_mul_const(pub, a, n):
    """Multiplies an ancrypted integer by a constant"""
    return modpow(a, n, pub.n_sq)

def decrypt(priv, pub, cipher):
    x = pow(cipher, priv.l, pub.n_sq) - 1
    plain = ((x // pub.n) * priv.m) % pub.n
    return plain

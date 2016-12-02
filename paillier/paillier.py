import math
import primes
from random import randint

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
    proof["variations"] = []
    proof["n"] = pub.n
    proof["n2"] = pub.n_sq
    for i in xrange(1):
        variation = {}
        x = randint(1,pub.n-1)
        variation["x"] = x
        s = randint(1,pub.n-1)
        variation["s"] = s
        e = randint(1,pub.n-1)
        variation["e"] = e
        v = (x - e*plain) % pub.n
        variation["v"] = v
        w = (s * pow(r, -1*e, pub.n) * pow(pub.g, v / pub.n, pub.n)) % pub.n
        variation["w"] = w
        u = pow(g, x, pub.n_sq) * pow(s, pub.n, pub.n_sq)
        print "x",x
        print "s",s
        print "e",e
        print "v",v
        print "w",w
        print "u",u
        print "proof",(pow(g, v, pub.n_sq)*pow(cipher, e, pub.n_sq)*pow(w, pub.n, pub.n_sq)) % pub.n_sq
        proof["variations"].append(variation)
    return proof


    ren = pow(r, pub.n, pub.n_sq)
    cipher = (pow(pub.g, plain, pub.n_sq) * ren) % pub.n_sq
    return cipher, r

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

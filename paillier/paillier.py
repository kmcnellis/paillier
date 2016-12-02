import math
import primes
from random import randint
import rsa
from fractions import gcd

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
    while not inModN(a):
        a = randint(1,n-1)
    return a

def getRandomModNStar(n):
    a = 0
    while not inModNStar(a,n):
        a = randint(1,n-1)
    return a

def getRandomModNPrime(n):
    a = 0
    while not inModNStar(a,n) and inModN(a):
        a = primes.generate_prime(long(round(math.log(n, 2))))
    return a

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

def blind(key, pubkey, plainText):
    x = pow(key, pubkey.e, pubkey.n)
    plain = rsa.transform.bytes2int(plainText)
    cipher = (plain * x) % pubkey.n
    return rsa.transform.int2bytes(cipher)

def unblind(key, pubkey, cipherText):
    reverse = invmod(key,pubkey.n)
    cipher = rsa.transform.bytes2int(cipherText)
    plain = (cipher * reverse) % pubkey.n
    return rsa.transform.int2bytes(plain)

def signBlind(privkey, cipherText):
    cipher = rsa.transform.bytes2int(cipherText)
    signed = pow(cipher, privkey.e, privkey.n)
    return rsa.transform.int2bytes(signed)

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

def genZKPnumbers(pub, plain, cipher, r):
    x = getRandomModN(pub.n)
    s = getRandomModNStar(pub.n)
    u = (pow(pub.g, x, pub.n_sq) * pow(s, pub.n, pub.n_sq)) % pub.n_sq

    return x,s,u

def genZKP(pub, plain, cipher, r,x,s,e):
    proof = {}
    proof["variations"] = []
    proof["n"] = pub.n
    proof["n2"] = pub.n_sq
    proof["g"] = pub.g
    for i in xrange(1):
        variation = {}
        x = getRandomModN(pub.n)
        s = getRandomModNStar(pub.n)
        u = (pow(pub.g, x, pub.n_sq) * pow(s, pub.n, pub.n_sq)) % pub.n_sq

        e = randint(1,pub.n-1)
        v = (x - e*plain) % pub.n
        w = (s * pow(invmod(r,pub.n), e, pub.n) * pow(pub.g, v / pub.n, pub.n)) % pub.n

        variation["x"] = x
        variation["s"] = s
        variation["u"] = u
        variation["e"] = e
        variation["v"] = v
        variation["w"] = w
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

'''
tau_c = 1 works, but all the other tau_c not work.... 5.12.2023
'''

from Crypto.PublicKey import RSA
from Crypto.Hash import SHA256
import os
import hashlib
import random

import sys
sys.path.append('../structs/')
sys.path.append('../../../structs/') # it should be the path that run this code, from SP.py or FA.py

from fast_pow import *

import time
import gmpy2


def RSA_blind_signature_setup(service_name):
    # Set up RSA key pair
    key = RSA.generate(2048)

    # Create directory if it doesn't exist
    dir_path_token = f"./service_{service_name}/RSAkeys"
    if not os.path.exists(dir_path_token):
        os.makedirs(dir_path_token)

    # Write RSA key pair to file
    with open(f'./service_{service_name}/RSAkeys/RSA_sk.pem', 'wb') as f:
        f.write(key.export_key('PEM'))

    n, e = key.publickey().n, key.publickey().e
    # Write n and e to another file
    with open(f'./service_{service_name}/RSAkeys/RSA_pk.pem', 'wb') as f:
        f.write(RSA.construct((n, e)).export_key('PEM'))



# def tau_c_generation(c):
#     '''
#     c is service key in our case
#     tau_c = 2^{k-1} + 2h(c)+1, where h(c) is the hash value of c, the length of c is k-2
#     '''
#     k = len(c)+2
#     hash_object = hashlib.sha256(str(c).encode('utf-8'))
#     hash_c = hash_object.hexdigest()
#     tau_c = pow(2,k-1) + 2*int(hash_c,16) + 1
#     return tau_c


# def lcm_generation(public_key): # the lcm of p-1 and q-1, which is the lambda in the original paper
#     p, q = public_key.p, public_key.q
#     lcm = gmpy2.lcm(p-1, q-1)
#     return lcm



# def tau_c_generation_gmpy2(c):
#     '''
#     c is service key in our case
#     tau_c = 2^{k-1} + 2h(c)+1, where h(c) is the hash value of c, the length of c is k-2
#     '''
#     k = len(c) + 2
#     hash_object = hashlib.sha256(str(c).encode('utf-8'))
#     hash_c = hash_object.hexdigest()
#     tau_c = gmpy2.add(gmpy2.add(pow(2, k-1), gmpy2.mul(2, int(hash_c, 16))), 1)
#     tau_c = int(tau_c)
#     return tau_c


def random_r_generation(n):
    '''
    generate a random number r
    '''
    r = random.randint(1, n - 1)
    return r


# def RSA_blind(m,r,tau_c,n,e):
#     '''
#     partial blind signature

#     blind the message m
#     input the message m, random number r, and a common string c

#     return the blinded message m_prime
#     - if you want to use the traditional blind signature, just keep the common string \tau(c) as 1
#     '''
#     m_prime = (m * pow(r,e*tau_c)) % n
#     return m_prime


def RSA_blind_gmpy2(m,r,public_key):
    """
    Calculate the value of (r ** e * m) % n
    """
    rsa_key = public_key
    n, e = rsa_key.n, rsa_key.e

    # time_0 = time.time()
    # Calculate the SHA-256 hash value and convert it to an integer
    h = int.from_bytes(hashlib.sha256(m).digest(), 'big')
    # h = int(m)
    # e_tau_c = gmpy2.mul(e, tau_c)
    # e_tau_c = int(gmpy2.mul(e, tau_c))
    # Calculate the value of (r ** e * h) % n
    rh = gmpy2.mul(pow_mod(r, e, n), h)
    result = rh % n
    # time_1 = time.time()
    # print("result of the blinded msg using gmpy2: ", result)
    # print("blind msg time using gmpy2: ", time_1 - time_0)
    return result


# def RSA_blind_sign(m_prime,tau_c,d,n):
#     '''
#     blind signature generation
#     input the blinded message m_prime, common string c, and RSA private key d
#     return the signature s_prime

#     again, if you want to use the traditional blind signature, just keep the common string \tau(c) as 1
#     '''
#     d_c = d*(1/tau_c)
#     s_prime = pow(m_prime,d_c) % n
#     return s_prime


def RSA_blind_sign_gmpy2(m_prime,secret_key):
    '''
    blind signature generation
    input the blinded message m_prime, common string c, and RSA private key d
    return the signature s_prime

    again, if you want to use the traditional blind signature, just keep the common string \tau(c) as 1
    '''
    p, q = secret_key.p, secret_key.q
    # lcm = gmpy2.lcm(p-1, q-1)

    # m_prime = int(m_prime)
    d, n = secret_key.d, secret_key.n
    # d_c = gmpy2.div(d, tau_c) % lcm
    # d_c = int(d_c)
    # d_c = (d // tau_c) % int(lcm)
    # d_c = (1 / (1/(d*tau_c))) % int(lcm)
    # d_c = (d // tau_c) % int(lcm)
    s_prime = pow_mod(m_prime,d,n)
    return s_prime

# def RSA_unblind(s_prime,r,n):
#     '''
#     unblind the signature
#     input the signature s_prime, random number r, and RSA public key n
#     return the unblinded signature s
#     '''
#     s = (s_prime * pow(r,-1)) % n
#     return s


def RSA_unblind_gmpy2(s_prime,r,public_key):
    '''
    unblind the signature
    input the signature s_prime, random number r, and RSA public key n
    return the unblinded signature s
    '''
    n = public_key.n
    r_inv = gmpy2.invert(r, n)
    # calculate s' = s * r^-1 mod n
    s = gmpy2.mul(s_prime, r_inv) % n
    return s


# def RSA_sig_verify(m,s,tau_c,secret_key):
#     '''
#     signature verification
#     input the message m, signature s, common string c, and RSA public key (n,e)
#     return the verification result
#     '''
#     n, e = secret_key.n, secret_key.e
#     if pow(s,e*tau_c) % n == m:
#         return True
#     else:
#         return False



def RSA_sig_verify_gmpy2(m,s,public_key):
    """
    Verifies an RSA signature for a given message and public key.

    Args:
    m (bytes): The message that was signed.
    s (bytes): The RSA signature for the message.
    public_key (key): The RSA public key used to sign the message.

    Returns:
    bool: True if the signature is valid for the message, False otherwise.
    """
    # Load the public key from its PEM-encoded form.
    # rsa_key = RSA.import_key(public_key)
    rsa_key = public_key

    # Create a PKCS1_v1_5 object for signing with the RSA key.
    # signer = PKCS1_v1_5.new(rsa_key)

    # Compute the SHA-256 hash of the message.
    hash_obj = int.from_bytes(hashlib.sha256(m).digest(), 'big')
    # hash_obj = int(m)
    print("m: ", hash_obj)
    print("s:signature of m: ", s)
    # s = int(s)
    hash_prime = pow_mod(s, rsa_key.e, rsa_key.n)

    return hash_obj==hash_prime # return True if the signature is valid, False otherwise



def main():
    service_name = '1'
    RSA_blind_signature_setup(service_name)

    '''test the above functions'''
    # generate a message m
    # m = b'xwang244'
    m = b'xwang244@ncsu.edu'

    # read the RSA key pair from file (FA do this) only the FA has the private key
    with open(f'./service_{service_name}/RSAkeys/RSA_sk.pem', 'rb') as f:
        RSA_secret_key = RSA.import_key(f.read())
        # d = key.d
        # n = key.n
    
    # read the RSA public key from file (everyone can do this, know the public key)
    with open(f'./service_{service_name}/RSAkeys/RSA_pk.pem', 'rb') as f:
        RSA_public_key = RSA.import_key(f.read())
        # e = key.e
        # n = key.n

    e = RSA_public_key.e
    n = RSA_public_key.n
    print("e: ", e)
    print("n: ", n)
    d = RSA_secret_key.d
    print("d: ", d)
    # generate a random number r
    r = random_r_generation(RSA_public_key.n)
    print("r: ", r)

    # generate a common string c which is the service tag in our case, we want to keep this service tag secret
    # so this service tag should be a string that pretty hard to guess
    # c = 'service_tag_that_hard_to_guess'
    # c = '1'

    # generate the common string \tau(c)
    # time_0 = time.time()
    # # tau_c = tau_c_generation(c)
    # tau_c = tau_c_generation_gmpy2(c)
    # time_1 = time.time()
    # print("time for tau_c_generation: ", time_1-time_0)
    # tau_c = 1
    # print("tau_c: ", tau_c)


    # blind the message m
    time_0 = time.time()
    # m_prime = RSA_blind(m,r,tau_c,n,e)
    m_prime = RSA_blind_gmpy2(m,r,RSA_public_key)
    print("m_prime: ", m_prime)
    time_1 = time.time()
    # print("time for RSA_blind: ", time_1-time_0)


    # generate the lcm
    # time_0 = time.time()
    # lcm = lcm_generation(RSA_public_key)
    # time_1 = time.time()
    # print("time for lcm_generation: ", time_1-time_0)

    # blind signature generation
    time_0 = time.time()
    s_prime = RSA_blind_sign_gmpy2(m_prime,RSA_secret_key)
    print("s_prime: ", s_prime)
    time_1 = time.time()
    # print("time for RSA_blind_sign: ", time_1-time_0)

    # unblind the signature
    time_0 = time.time()
    s = RSA_unblind_gmpy2(s_prime,r,RSA_public_key)
    time_1 = time.time()
    # print("time for RSA_unblind: ", time_1-time_0)

    # signature verification
    time_0 = time.time()
    check_sig_valid = RSA_sig_verify_gmpy2(m,s,RSA_public_key)
    print("m: ", m)
    print("s: ", s)
    print("type of m: ", type(m))
    print("type of s: ", type(s))
    if check_sig_valid:
        print("signature verification passed")
    else:
        print("signature verification failed")
    # if RSA_sig_verify(m,s,tau_c,n,e):
    #     print("signature verification passed")
    # else:
    #     print("signature verification failed")
    time_1 = time.time()
    # print("time for RSA_sig_verify: ", time_1-time_0)


if __name__ == "__main__":
    main()

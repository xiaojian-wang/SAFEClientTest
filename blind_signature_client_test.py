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
import string


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
    # print("m: ", hash_obj)
    # print("s:signature of m: ", s)
    # s = int(s)
    hash_prime = pow_mod(s, rsa_key.e, rsa_key.n)

    return hash_obj==hash_prime # return True if the signature is valid, False otherwise


def generate_random_string(length):
    characters = string.ascii_letters + string.digits
    return b''.join(random.choice(characters).encode() for _ in range(length))


def write_to_file(filename, value):
    with open(filename, 'a') as file:
        file.write(str(value) + '\n')


def main():
    run_num = 1000
    # file name with run number
    blind_time_file_name = f'./blind_time_{run_num}.txt'
    unblind_time_file_name = f'./unblind_time_{run_num}.txt'
    verify_time_file_name = f'./verify_time_{run_num}.txt'
    service_name = '1'
    dir_path_token = f"./service_{service_name}/RSAkeys"
    if not os.path.exists(dir_path_token):
        RSA_blind_signature_setup(service_name)

    dir_path_token = f"./service_forall/RSAkeys"
    if not os.path.exists(dir_path_token):
        RSA_blind_signature_setup('forall') # for base station

    '''test the above functions'''
    # generate a message m
    # m = b'xwang244'
    # m = b'xwang244@ncsu.edu'


    '''only this key need read by user '''
    with open(f'./service_{service_name}/RSAkeys/RSA_pk.pem', 'rb') as f: # read and binary
        service_public_key = RSA.import_key(f.read())
        # print("public_key: ", public_key)
    # Get n and e values
    n_s = service_public_key.n # RSA service public key n
    e_s = service_public_key.e # RSA service public key e

    '''all the following key should read by FA, not really, user also need to read bs public key''' 
    # the base station RSA private key and public key
    with open('./service_forall/RSAkeys/RSA_sk.pem', 'rb') as f:
        bs_private_key = RSA.import_key(f.read())
    # Get the RSA private key parameter d
    d_b = bs_private_key.d
    n_b = bs_private_key.n

    # Read public key from file
    with open('./service_forall/RSAkeys/RSA_pk.pem', 'rb') as f:
        bs_public_key = RSA.import_key(f.read())
    e_b = bs_public_key.e


    with open(f'./service_{service_name}/RSAkeys/RSA_sk.pem', 'rb') as f:
        service_secret_key = RSA.import_key(f.read())
    n_s = service_secret_key.n
    d_s = service_secret_key.d


    for i in range(run_num):
        m1 = generate_random_string(14)
        m2 = generate_random_string(14)
        min_n = min(n_s, n_b)
        r = random.randint(1, min_n - 1)


        # blind the two message and send to FA
        time1 = time.time()
        # user computes the blinded message m1' = m1 * r^e_b mod n_b
        m1_prime = RSA_blind_gmpy2(m1,r,bs_public_key)
        # user computes the blinded message m2' = m2 * r^e_s mod n_s
        m2_prime = RSA_blind_gmpy2(m2,r,service_public_key)
        time2 = time.time()
        blind_time = time2 - time1
        print("time for token blind: ", blind_time)
        write_to_file(blind_time_file_name, blind_time)
        


        # sign the blinded message by FA, we do not need to stat the time of this part at client end
        with open(f'./service_{service_name}/RSAkeys/RSA_sk.pem', 'rb') as f:
            service_secret_key = RSA.import_key(f.read())
        n_s = service_secret_key.n
        d_s = service_secret_key.d
        # FA sign the blind message m1_prime and m2_prime
        s1_prime = RSA_blind_sign_gmpy2(m1_prime,bs_private_key)
        s2_prime = RSA_blind_sign_gmpy2(m2_prime,service_secret_key)


        # unblind the signature from FA get the signature can actually be used
        time3 = time.time()
        s1 = RSA_unblind_gmpy2(s1_prime,r,bs_public_key)
        s2 = RSA_unblind_gmpy2(s2_prime,r,service_public_key)
        time4 = time.time()
        unblind_time = time4 - time3
        print("time for token unblind: ", unblind_time)
        write_to_file(unblind_time_file_name, unblind_time)


        time5 = time.time()
        if RSA_sig_verify_gmpy2(m1,s1,bs_public_key) and RSA_sig_verify_gmpy2(m2,s2,service_public_key):
            time6 = time.time()
        verify_time = time6 - time5
        print("time for token verification: ", verify_time)
        write_to_file(verify_time_file_name, verify_time)
        


if __name__ == "__main__":
    main()

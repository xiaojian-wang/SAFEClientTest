import gmpy2


'''same as the pow_mod function in User.py
but this function in this file is for SP to sign the blind message
the equation is s'=m'^d mod n
'''
# cannot put it into the class due to the function in the class need to correspond to an application in protocol
def pow_mod(r, e, n):
    '''
    Calculate the value of (r ** e) % n
    '''
    # print('in pow_mod function...')
    # Convert the exponent e to binary representation and reverse it
    bits = bin(e)[2:][::-1]
    # Initialize the value of power to r
    result = gmpy2.mpz(r)
    # Initialize the square to r^2
    square = gmpy2.powmod(r, 2, n)
    # Iterate through each bit of the binary representation
    for bit in bits[1:]:
        # Multiply the square to the result for each iteration
        result = (result if bit == '0' else gmpy2.mul(result, square)) % n
        # Update the square to the square of the current power
        square = gmpy2.powmod(square, 2, n)
    # print('result of the pow_mod: ', result)
    return result
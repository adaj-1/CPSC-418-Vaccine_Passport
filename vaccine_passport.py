#!/usr/bin/env python3

# good news: you get all these functions for free from prior assignment solutions
from hmac import digest_size
from encrypt_decrypt__SOLUTION import generate_iv, pad, unpad, xor
from basic_auth__SOLUTION import b2i, blake2b_256, bytes_to_int, calc_A, calc_B, calc_K_client
from basic_auth__SOLUTION import calc_K_server, calc_M1, calc_u, calc_x, client_register
from basic_auth__SOLUTION import close_sock, create_socket, find_Y, i2b, int_to_bytes
from basic_auth__SOLUTION import prim_root, receive, safe_prime, send, server_register
from basic_auth__SOLUTION import split_ip_port

import secrets
import hashlib
from Crypto.Cipher import AES


def varprint( data, label, source="Client" ):
    """A helper for printing out data. Must be copy-pasted from A2 to have the 
       right scoping."""
    global args

    if not (('args' in globals()) and args.verbose):
        return

    if label is not None:
        middle = f"{label} = "
    else:
        middle = ""

    if type(data) == bytes:
        print( f"{source}: Received {middle}<{data.hex()}>" )
    else:
        print( f"{source}: {middle}{data}" )


import argparse
from datetime import date, timedelta

from math import gcd
import re

from secrets import randbelow, token_bytes, randbits
import socket
from sys import exit

from threading import Thread
from time import sleep
from typing import Callable, Iterator, Mapping, Optional, Union

from random import randint 

from hashlib import shake_256, sha256
from Crypto.Cipher import AES


# bad news: all their external imports aren't imported into this namespace, 
#  so you'll need to reimport. Do so here.

### CLASSES

class DH_params:
    """Contains the two critical parameters for Diffie-Hellman key exchange.
       Makes it easier to pass those parameters into functions.

       Some examples of how to use this class:
       > DH     = DH_params()
       > DH2    = DH_params( pair=(DH.g, DH.N) )
       > DH_len = DH.bytes
       """

    def __init__(self, pair:Optional[tuple[int,int]]=None, bits:int=512):
        """Create a DH_params object, either on-the-fly or from existing values.

        PARAMETERS
        ==========
        pair: If creating from existing values, supply them in the form (g,N)
            where g is a primitive root of a safe prime N, both of which are ints. 
            If this isn't a two-item tuple, the contents will be ignored.
        bits: The number of bits to use when generating g and N. Only used when
            generating an g,N pair, as it can otherwise be inferred from the input.

        WARNING: Minimal error checking is done!
        """

        if (type(pair) is tuple):

            # we should be testing g and N here
            self.g, self.N = pair
            self.bits = self.N.bit_length()

        else:

            self.N    = safe_prime( bits )
            self.g    = prim_root( self.N )
            self.bits = bits

        # keep these around for book-keeping
        self.k     = calc_u( self.g, self.N )  # same calculation!
        self.bytes = (self.bits + 7) >> 3      # round up

        assert self.N > self.g

    def calc_A(self, a:Union[int,bytes]) -> int:
        """Just a thin wrapper around calc_A()."""

        return calc_A( self.g, self.N, a )

    def calc_B(self, b:Union[int,bytes], v:Union[int,bytes]) -> int:
        """Just a thin wrapper around calc_B()."""

        return calc_B( self.g, self.N, b, self.k, v )

# reference:https://sites.psu.edu/gottiparthyanirudh/writing-sample-3/
def gcdExtended(a, b): 
    # Base Case 
    if (a % b) == 0 :  
        return b,0,1
             
    gcd,x,y = gcdExtended(b, a % b) 
    x = x - ((a//b) * y)
    return gcd,y,x   

    
class RSA_key:
    """Represents an RSA modulus and keypair within the system. Makes it easier
       to generate and share these values, and gives a clean interface for
       signing/verifying and encrypting/decrypting."""

    def __init__(self, pubkey:Optional[tuple[int,int]]=None, bits:int=2048):
        """Create an RSA_key object.

        PARAMETERS
        ==========
        pubkey: Optional, allows you to use a public key transmitted to you. If 
           provided it must be a tuple of the form (e,N), where both are 
           integers.
        bits: The number of bits to use for the modulus. Used when generating
           values only, ignored otherwise.

        EXAMPLES
        ========
        > key        = RSA_key()
        > server_key = RSA_key( pubkey=(e,N) )

        WARNING: Minimal error checking is done!
        """

        # check if we were given the proper values
        if (type(pubkey) is tuple):

            # these two values should be tested for validity, in a real
            #  implementation
            self.e, self.N = pubkey

            # fill in the missing values with None, as flags
            self.p = None
            self.q = None
            self.d = None

            # we can calculate this value from N
            self.bits = self.N.bit_length()

        # not in public key mode? Generate a full key
        else:
            self.p, self.q = self.modulus( bits )
            self.N         = self.p * self.q
            self.e, self.d = self.keypair( self.p, self.q )

            self.bits = bits

        self.bytes = (self.bits + 7) >> 3
        assert self.N > self.e

    @staticmethod
    def modulus( bits:int=2048 ) -> tuple[int,int]:
        """Generate an RSA modulus of the given size.
    
        PARAMETERS
        ==========
        bits: An int specifying the number of bits that N = p*q must occupy.

        RETURNS
        =======
        A tuple of the form (p,q), where p and q are ints of the same length.

        EXAMPLES
        ========
        > p, q   = RSA_key.modulus()
        > p2, q2 = key.modulus()        # also works, but note it generates a
                                        #  new modulus rather than returning
                                        #  the existing one.
        """

        assert type(bits) == int
        assert (bits & 0x1) == 0        # must be even

        length = int(bits/2)
        p = safe_prime(length)
        q = safe_prime(length)
        return (p,q)

    @staticmethod
    def keypair( p:int, q:int ) -> tuple[int,int]:
        """Generate a suitable public/private keypair for the given p and q.
           IMPORTANT: Implement your own version of the Extended Euclidean
           Algorithm, instead of relying on external routines or pow().
           You may assert an inverse must exist.
    
        PARAMETERS
        ==========
        p, q: The two parts of an RSA modulus, as integers.

        RETURNS
        =======
        A tuple of the form (e,d), where e is a random number and d its
            multiplicative inverse for phi(n). Both are integers.

        EXAMPLES
        ========
        > key = RSA_key()
        > p, q = key.modulus()
        > e, d = RSA_key.keypair( p, q )
        """

        assert type(p) == int
        assert type(q) == int

        phi = (p - 1)* (q - 1)
        e = randint(1, phi)
        gcd, x, y = gcdExtended(e,phi)
         
        while gcd != 1:
            e = randint(1, phi)
            gcd, x, y = gcdExtended(e,phi)    
        
        d = x%phi           # mod inverse
        return (e,d)

            
    def sign( self, message:Union[int,bytes] ) -> Union[int,None]:
        """Sign a message via this RSA key, if possible.
    
        PARAMETERS
        ==========
        message: The message to be signed. Could be an int or bytes object.

        RETURNS
        =======
        If this has a private key, return the signature as an integer value.
           If it does not, return None.

        EXAMPLES
        ========
        > key = RSA_key()
        > sig = key.sign( 42 )
        """

        assert type(message) in [int, bytes]

        message = b2i(message)
        try:
            return pow(message, self.d, self.N)
        except:
            return None


    def verify( self, message:Union[int,bytes], signature:Union[int,bytes] ) \
            -> bool:
        """Verify a message signed via this RSA key, if possible.
    
        PARAMETERS
        ==========
        message: The message to be signed. Could be an int or bytes object.
        signature: The value which claims to be a signature of the message.
           Could be an int or bytes object.

        RETURNS
        =======
        True if the signature matches, False otherwise.

        EXAMPLES
        ========
        > key = RSA_key()
        > sig = key.sign( 37 )
        > key.verify( 37, sig )
        True
        """

        assert type(message) in [int, bytes]

        message = b2i(message)
        signature = b2i(signature)
        try:
            if pow(signature, self.e, self.N) == message:
                return True
            else: 
                return False
        except:
            return False

    def encrypt( self, message: Union[int,bytes] ) -> int:
        """Encrypt a message via this RSA key.
    
        PARAMETERS
        ==========
        message: The message to be encrypted. Could be an int or bytes object.

        RETURNS
        =======
        The encrypted value, as an integer.

        EXAMPLES
        ========
        > key    = RSA_key()
        > cypher = key.encrypt( 42 )
        """

        assert type(message) in [int, bytes]
        message = b2i(message)
        return pow(message, self.e, self.N)
         
        

    def decrypt( self, cypher: Union[int,bytes] ) -> Union[int,None]:
        """Decrypt a message via this RSA key.
    
        PARAMETERS
        ==========
        cypher: The encrypted message. Could be an int or bytes object.

        RETURNS
        =======
        The decrypted value, as an integer, if this contains a private
           key. Otherwise, returns None.

        EXAMPLES
        ========
        > plain = server_key.decrypt( crypt )
        """

        assert type(cypher) in [int, bytes]

        cypher = b2i(cypher)
        try:
            return pow(cypher, self.d, self.N)
        except:
            return None


def zfill(data: bytes, length: int):
    while len(data) % length != 0:
        data =  data + bytes(1)
    return data


def encode_name( given_name:str, surname:str, target:int=92 ) -> bytes:
    """Compact a person's name into a bytes sequence. See the 
       assignment sheet for details.

    PARAMETERS
    ==========
    given_name: A string representing the first name of a person.
    surname: A string representing the last name of a person.
    target: The number of bytes the compacted sequence must
      contain.

    RETURNS
    =======
    The compacted names as a bytes sequence, starting with the
    index byte.
    """
    assert (len(given_name) > 0) or (len(surname) > 0)
    assert (target > 1) and (target < 256)

    given = given_name.encode('utf-8')
    given_len = len(given)
    sur = surname.encode('utf-8')
    sur_len = len(sur)
    
    name_length = target - 1

    while (given_len + sur_len) > name_length:
        if len(given_name) > len(surname):
            given_name = given_name[:-1]
            given = given_name.encode('utf-8')
            given_len = len(given)   
        else:
            surname = surname[:-1]
            sur = surname.encode('utf-8')
            sur_len = len(sur)
    
    index_byte = bytearray(int_to_bytes(given_len, 1))
    
    if (given_len + sur_len) < name_length:
        index = randint(given_len, name_length - sur_len)
        index_byte = bytearray(int_to_bytes(index, 1))
        if index > given_len:
            padding = index - given_len
            given = given + bytes(padding)
        if name_length > (index + sur_len):
            padding = name_length - (index + sur_len)
            sur = sur + bytes(padding)
    compact = bytes(index_byte + bytearray(given) + bytearray(sur))
    return compact

def gen_plaintext( given_name:str, surname:str, birthdate:date, vax_count:int, \
        last_vax_date:date ) -> bytes:
    """With the help of encode_name(), generate the plaintext portion of the 
       QR code.

    PARAMETERS
    ==========
    given_name: A string representing the first name of a person.
    surname: A string representing the last name of a person.
    birthdate: When this person was born, as a date object.
    vax_count: The number of SARS vaccines this person has had, as an int.
    last_vax_date: When this person was last vaccinated, as a date object.

    RETURNS
    =======
    A bytes object containing the plaintext, 96 bytes long.
    """
    assert (len(given_name) > 0) or (len(surname) > 0)
    assert vax_count >= 0
    
    # first 4 bits in first byte
    if vax_count > 15:
        vax_count = 15

    # last 4 bits in first byte are the upper portion of the vax date
    zero_byte = str(format(vax_count, "b")).zfill(4)

    # 8 bits in second byte: weeks since June 11th, 2006 of last vaccine shot
    # reference: https://stackoverflow.com/questions/14191832/how-to-calculate-difference-between-two-dates-in-weeks-in-python
    monday_start = (date(2006, 6, 11) - timedelta(days = last_vax_date.weekday()))
    monday_vax = (last_vax_date - timedelta(days = last_vax_date.weekday()))  
    weeks = int((monday_vax - monday_start).days / 7)
    if weeks > 4095 or vax_count == 0:
        weeks = 4095
    weeks = str(format(weeks, "b")).zfill(12)

    zero_byte = bytearray(int_to_bytes(int(zero_byte + weeks[:-8], 2), 1))

    first_byte = bytearray(int_to_bytes(int(str(weeks[4:]), 2), 1))
 
    # next two bytes represent birthdate of person measured since January 1st, 1880
    # big endian format and capped at 65,535 days
    day_start = date(1880, 1, 1)
    days = int((birthdate - day_start).days)
    if days > 65535:
        days = 65535
    days = bytearray(int_to_bytes(days, 2))
           
    name = bytearray(encode_name(given_name,surname))
    
    return  bytes(zero_byte + first_byte + days + name)
    

def pseudoKMAC( key_hash:bytes, data:bytes, length:int, custom:bytes=b'' ) -> bytes:
    """Returns the output of the modified KMAC algorithm. See the assignment
       sheet for details.

    PARAMETERS
    ==========
    key_hash: A bytes object containing the key.
    data: A bytes object to be hashed according to the aforementioned key.
    length: The number of bytes in the resulting digest.
    custom: A bytes object used to customize the digest output. Optional.

    RETURNS
    =======
    A bytes object containing the digest.
    """
    assert length > 0

    #https://nvlpubs.nist.gov/nistpubs/specialpublications/nist.sp.800-185.pdf
    
    sars = b''
    if custom != b'':
        sars = zfill(custom,136)    
        
    key_hash = zfill(key_hash, 136)
    hash = hashlib.shake_256()
    hash.update(sars + key_hash + data + int_to_bytes(length,1))
    tag = hash.digest(length)
    return tag
 
def interleave_data( plaintext:bytes, nonce:bytes, inner_tag:bytes ) -> bytes:
    """Combine the plaintext, nonce, and inner_tag into the interleaved format
       described in the assignment write-up.

    PARAMETERS
    ==========
    plaintext: A bytes object containing the key information on the passport.
    nonce: The initialization vector to help provide semantic security, as bytes.
    inner-tag: The SHAKE256 tag used to provide a second layer of validation.

    RETURNS
    =======
    A bytes object containing the interleaved QR code, 128 bytes long.
    """
    assert len(plaintext) == 96
    assert len(nonce)     == 16
    assert len(inner_tag) == 16
    
    NT_start = 0
    NT_end = 2
    P_start = 0
    P_end = 12
    
    nonce = bytearray(nonce)
    plaintext = bytearray(plaintext)
    inner_tag = bytearray(inner_tag)
    data = bytearray()

    for _ in range(8):
        block = nonce[NT_start:NT_end] + plaintext[P_start:P_end] + inner_tag[NT_start:NT_end]  
        data = data + block
        NT_start += 2
        NT_end += 2
        P_start += 12
        P_end += 12
    return bytes(data)
    

def encrypt_data( plaintext:bytes, key_enc:bytes, key_mac:bytes ) -> bytes:
    """Encrypt the given plaintext, following a modified version of the 
       algorithm from A1. See the assignment sheet for the changes.

    PARAMETERS
    ==========
    plaintext: The message to encrypt, as bytes.
    key_enc: The key used to encrypt with, also as bytes.
    Key_mac: The key used to generate THE MAC.

    RETURNS
    =======
    The IV, cyphertext, and MAC as a single bytes sequence.
    """
    assert len(key_enc) == 32
    assert len(key_mac) == 32

    cipher = AES.new(key_enc, AES.MODE_ECB)
    #plaintext = pad(plaintext, 32)
    ciphertext = cipher.encrypt(pad(plaintext, 32))
    iv = generate_iv(16) 
    #ciphertext, tag = cipher.encrypt_and_digest(plaintext)
    MAC = pseudoKMAC(key_mac, plaintext, 32, iv)
    sars = "OH SARS QR MAC"
    sars = sars.encode('utf-8')
    hash = hashlib.shake_256()
    hash.update(pad(sars, 136) + pad(key_mac, 136) + iv + ciphertext + b'100000')
    return iv + ciphertext + hash.digest(32)


def decrypt_data( cyphertext:bytes, key_enc:bytes, key_mac:bytes ) -> Optional[bytes]:
    """Decrypt the data encrypted by encrypt_data(). Also perform all necessary 
       validation.

    PARAMETERS
    ==========
    cyphertext: The message to decrypt, as bytes.
    key_enc: The key used to encrypt with, also as bytes.
    Key_mac: The key used to generate THE MAC.

    RETURNS
    =======
    Either the plaintext, if the message could be decoded, or None if the
        validation checks fail.
    """
    assert len(key_enc) == 32
    assert len(key_mac) == 32

    cipher = AES.new(key_enc, AES.MODE_ECB)
    try:
        plaintext = cipher.decrypt(cyphertext)
        return plaintext
    except:
        return None

def create_passport( given_name:str, surname:str, birthdate:date, vax_count:int, \
        last_vax_date:date, key_hash:bytes, key_enc:bytes, RSA_key:object ) -> bytes:
    """Create a vaccine passport, using the above functions. This includes signing
       the output.

    PARAMETERS
    ==========
    given_name: A string representing the first name of a person.
    surname: A string representing the last name of a person.
    birthdate: When this person was born, as a date object.
    vax_count: The number of SARS vaccines this person has had, as an int.
    last_vax_date: When this person was last vaccinated, as a date object.
    key_hash: The server-side secret used generate the inner tag, as bytes.
    key_enc: The key used to encrypt with, also as bytes.
    RSA_key: The key used to sign the passport.

    RETURNS
    =======
    A bytes object containing the passport, 319 bytes long.
    """
    assert (len(given_name) > 0) or (len(surname) > 0)
    assert vax_count >= 0
    assert RSA_key.bytes == 160
    
    # delete this comment and insert your code here

def verify_passport( passport:bytes, key_enc:bytes, RSA_key:object, key_hash:Optional[bytes]=None \
        ) -> Optional[tuple[str,str,date,int,int]]:
    """Verify the given passport to make sure it appears legit. Do all the checks that you can,
       given the parameters.

    PARAMETERS
    ==========
    key_enc: The key used to encrypt with, as bytes.
    RSA_key: The key used to sign the passport.
    key_hash: The server-side secret used generate the inner tag, as bytes. If missing, 
        skip this check.

    RETURNS
    =======
    If the passport passes all tests, return a tuple containing the given name (string),
        surname (string), date of birth (date), number of vaccinations (int), and 
        week since their last vaccination (int). If at least one of the tests fails,
        return None.
    """
    assert len(passport) == 319
    assert RSA_key.bytes == 160

    # delete this comment and insert your code here

def request_passport( ip:str, port:int, uuid:str, secret:str, salt:bytes, \
        DH_params:object, RSA_key:object, health_id:int, birthdate:date, \
        vax_date:date ) -> Optional[tuple[int,int,bytes]]:
    """Request a passport from the web client. Carries out the modified version of
       the protocol outlined in the assignment sheet. Assume the registration process
       has already been carried out. Don't forget to send 'p'!

    PARAMETERS
    ==========
    ip: The IP address to connect to, as a string.
    port: The port to connect to, as an int.
    uuid, secret: username and pw from A2, respectively, as strings.
    salt: The salt from A2, as bytes.
    DH_params: The Diffie-Hellman parameters noted during registration, contained in 
        the object of the same name.
    RSA_key: The RSA key retrieved from the vaccine passport server, in the object of 
        the same name.
    health_id: The Ontario Health Number associated with the person requesting a passport.
    birthdate: The day the person was born, as a date object.
    vax_date: One of the days the person received a SARS-COV-1 vaccine, also as a date.

    RETURNS
    =======
    If successful, return a tuple of the form (a, K_client, passport), where a and 
        K_client are integers while passport is 319 bytes. If not, return None.

    """
    assert port > 0
    assert len(uuid) == 32
    assert len(secret) == 32
    assert len(salt) == 16
    assert 0 < health_id < 10000000000 # leading zeros are an issue

    g = getattr(DH_params, 'g')
    N = getattr(DH_params, 'N')
    
    sock = create_socket( ip, port )
    if sock is None:
        return None

    # send 'p'
    count = send( sock, b'p' )
    if count != 1:
        return close_sock( sock )
    
    # retrieve N and g
    expected = 64 * 2
    g_N = receive( sock, expected )
    if len(g_N) != expected:
        return close_sock( sock )
    
    # check they match
    if bytes_to_int(g_N[:expected>>1]) != g:
        return close_sock( sock )

    if bytes_to_int(g_N[expected>>1:]) != N:
        return close_sock( sock )

    # calculate k before conversions, as it might be more efficient
    k = calc_u( g, N )      # same action as u! 
    varprint( k, 'k' )

    # calculate x and v
    x = calc_x( salt, secret ) 
    v = calc_A( g, N, x )   # same action as A!
    
    # generate a via rejection sampling
    a = randbits( 64 )
    while a >= N:
        a = randbits( 64 )

    # calculate A
    A = calc_A( g, N, a )
    #encrypt via RSA encryption under server public key
    ENC_A = int_to_bytes(RSA_key.encrypt(A),RSA_key.bytes)

    # send ENC_A and uuid
    u_enc = uuid.encode('utf-8')
    u_len = int_to_bytes( len(u_enc), 1 )

    count = send( sock, ENC_A )
    if count != len(ENC_A):
        return close_sock( sock )
    
    count = send( sock, u_len )
    if count != len(u_len):
        return close_sock( sock )
    
    count = send( sock, u_enc )
    if count != len(u_enc):
        return close_sock( sock )
    
    # get salt, B
    expected = 16 + 64
    s_B = receive( sock, expected )
    if len(s_B) != expected:
        return close_sock( sock )

    if salt != s_B[:16]:
            return close_sock( sock )

    B = bytes_to_int( s_B[16:] )

    # compute u
    u = calc_u( A, s_B[16:] )     # TODO calc with A_bytes or ENC_A?
    
     # compute K_client
    K_client = calc_K_client( N, B, k, v, a, u, x )
    
    # get bits
    bits = receive( sock, 1 )
    if len(bits) != 1:
        return close_sock( sock )

    # find Y
    Y = find_Y( K_client, bits )

    # send Y
    count = send( sock, Y )
    if count != len(Y):
        return close_sock( sock )

    # receive M1_server
    M1 = receive( sock, 32 )
    if len(M1) != 32:
        return close_sock( sock )

    if M1 != calc_M1( A, K_client, Y ):
        return close_sock( sock )
    
    #With the shared key derived, the web client appends the OHN as a five byte number, three
    #zero bytes, birthdate (days since January 1st, 1880, as two bytes), four zero bytes, and a date
    #of vaccination (days since June 11th, 2006, as two bytes) in that order. The client encrypts
    #that via AES-256 and uses the following 32 byte value as the key.
    #H(P("OH SARS KEYEXTEND 1")jjP(NRSAjje)jjKclientjj0x20)
    
    # next two bytes represent birthdate of person measured since January 1st, 1880
    day_start = date(1880, 1, 1)
    days = int((birthdate - day_start).days)
    
    vax_start = date(2006, 6, 11)
    vax_days = int((vax_date - vax_start).days)
  
    byte_K_client = int_to_bytes(K_client, 64)
        
    #health_data = int_to_bytes(health_id, 5) + bytes(3) + int_to_bytes(days,2) + bytes(4) + int_to_bytes (vax_days,2)
    health_data = bytes(16)
    key_extend = "OH SARS KEYEXTEND 1"
    key_extend = key_extend.encode('utf-8')
    
    e_RSA = getattr(RSA_key,'e')
    N_RSA = getattr(RSA_key,'N')
    
    NE = int_to_bytes(N_RSA, RSA_key.bytes) + int_to_bytes(e_RSA, RSA_key.bytes)
    
    AES_key = pseudoKMAC(byte_K_client, pad(key_extend, 136)+ pad(NE, 136) + byte_K_client + b'100000', 32)

    cipher = AES.new(AES_key, AES.MODE_ECB)
    ciphertext = cipher.encrypt(health_data)               #TODO leading zero byte for no reason?
    
    count = send( sock, ciphertext )
    if count != len(ciphertext):
        return close_sock( sock )

    QR_code_len = receive(sock, 4)
    if len(QR_code_len) != 4:
        return close_sock( sock )
    
    QR_code_len = b2i(QR_code_len)
    QR_code = receive(sock, QR_code_len)
    if len(QR_code) != QR_code_len:
        return close_sock( sock )
    # all done with the connection
    close_sock( sock )
    

    passport = decrypt_data(QR_code, byte_K_client[:32], byte_K_client[32:]) 
    
    if len(passport) != 319:
        return None
    else:
        print( "Client: Protocol successful.")
        return ( a, K_client, passport)
    ### END

def retrieve_passport( sock:socket.socket, DH_params:object, RSA_key:object, \
        key_hash:bytes, key_enc:bytes, bits:int, registered:dict, vax_database:dict \
        ) -> Optional[tuple[int,int,int,bytes]]:
    """Handle the server side of the vaccine passport protocol. Do not worry about 
       accepting connections or handling 'p', both have already been done for you.

    PARAMETERS
    ==========
    sock: A socket object that contains the client connection.
    DH_params: The Diffie-Hellman parameters noted during registration, contained in 
        the object of the same name.
    RSA_key: The RSA key retrieved from the vaccine passport server, in the object of 
        the same name.
    key_hash: The server-side secret used generate the inner tag, as bytes.
    key_enc: The key used to encrypt with, also as bytes.
    bits: The number of bits in H(K_server||Y) that must be zero.
    registered: A database of registered UUID's. See A2 for the format.
    vax_database: A database of OHNs and their vaccine status. The format is 
        OHN -> list( given_name, surname, birth_date, tuple(vax_type,vax_lot,vax_date), 
            tuple(vax_type,vax_lot,vax_date), ... ). 
        birth_date and vax_date are date objects, all else are strings. The first three
        values are guaranteed to exist. 

    RETURNS
    =======
    If successful, return a tuple of the form (b, K_server, OHN, passport), with 
        passport as bytes and the rest as integers. If not, return None.
    """
    assert bits > 0
    assert len(registered) > 0
    assert len(vax_database) > 0

    # calculate k before conversions, as it might be more efficient
    g = getattr(DH_params, 'g')
    N = getattr(DH_params, 'N')
    k = calc_u( g, N )      # same thing as u! 

    # send g and N
    g, N = map( lambda x: i2b(x,64), [g, N] )
    data = g + N
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # get ENC_A
    ENC_A = receive( sock, RSA_key.bytes )
    if len(ENC_A) != RSA_key.bytes:
        return close_sock( sock )
    A = RSA_key.decrypt( ENC_A )
    

    # get username
    data = receive( sock, 1 )
    if len(data) != 1:
        return close_sock( sock )
    count = bytes_to_int( data )

    u_enc = receive( sock, count )
    if len(u_enc) != count:
        return close_sock( sock )

    try:
        uuid = u_enc.decode('utf-8')
    except:
        return close_sock( sock )


    g, N = map( b2i, [g, N] )

    # retrieve s, v, if possible
    if uuid in registered:
        s, v = registered[uuid]
    else:
        return close_sock( sock )

    # generate b via rejection sampling
    b = randbits( 64 << 3 )
    while b >= N:
        b = randbits( 64 << 3 )
    varprint( b, 'b', "Server" )

    # calculate B
    B = calc_B( g, N, b, k, v )
    B_bytes = int_to_bytes( B, 64 )
    varprint( B, 'B', "Server" )

    # send s,B
    data = s + B_bytes
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # compute u
    u = calc_u( A, B_bytes )
    varprint( u, 'u', "Server" )

    # compute K_server
    K_server = calc_K_server( N, A, b, v, u )
    varprint( K_server, 'K_server', "Server" )

    # send bits
    count = send( sock, bits.to_bytes(1,'big') )
    if count != 1:
        return close_sock( sock )

    # receive Y
    Y = receive( sock, 64 )
    if len(Y) != 64:
        return close_sock( sock )
    varprint( Y, 'Y', "Server" )

    # check Y
    base = bits >> 3        # copy-paste code is worth the increased risk of breakage
    mask = ~((1 << (8 - (bits&7))) - 1)

    hashVal = blake2b_256( i2b(K_server,64) + Y )
    if (hashVal[:base] != bytes(base)) or ((hashVal[base] & mask) != 0):
        return close_sock( sock )

    # compute M1
    M1 = calc_M1( A, K_server, Y )
    

    # send M1. Defer error checking until after the socket's closed
    count = send( sock, M1 )
    
    if count != len(M1):
        close_sock( sock )

    
    
    print( "Server: Protocol successful." )
    return (b2i(b), b2i(K_server), OHN, b2i(passport))
    ### END

##### MAIN

if __name__ == '__main__':

    # create some helpers for the command line
    def iso_date( string ):
        """A parser for date objects."""
        return date.fromisoformat(string)   # raises ValueError

    def hexadecimal( string ):
        """A parser to convert hex values to a byte object."""
        if len(string) == 0:        # special-case blank values
            return None
        if string[:2] == "0x":
            return bytes.fromhex(string[2:])    # also raises ValueError
        else:
            return bytes.fromhex(string)

    def RSA_parser( string ):
        """Read in values from a file to generate an RSA key."""
        try:
            reader = open(string, 'rt')
        except FileNotFoundError:
            raise ValueError(f"Could not open file '{string}'")

        target = re.compile(r'^(\w)[ \t]*[:=][ \t]*(\d+)')
        captured = dict()
        for line in reader:
            output = target.match(line)
            if output is None:
                continue
            captured[output.group(1)] = int(output.group(2))

        if ('N' not in captured) or ('e' not in captured):
            reader.close()
            raise ValueError(f"RSA key file {string} must contain at least N and e.")

        RSA = RSA_key( pubkey=(captured['e'],captured['N']) )
        if 'd' in captured:
            RSA.d = captured['d']
        if 'p' in captured:
            RSA.p = captured['p']
        if 'q' in captured:
            RSA.q = captured['q']

        reader.close()
        return RSA

    def QR_file_parser( string ):
        """Read in values from a file containing a QR code."""
        try:
            reader = open(string, 'rb')
        except FileNotFoundError:
            raise ValueError(f"Could not open file '{string}'")

        # hex or binary?
        contents = reader.read()
        try:
            return bytes.fromhex( contents.decode('utf-8') )
        except UnicodeDecodeError:
            return contents

    def QR_image_parser( string ):
        """Read in values from an image containing a QR code."""

        from PIL import Image
        try:
            input = Image.open( string )
        except:
            raise ValueError(f"The image {string} either doesn't exist, or couldn't be read.")

        from pyzbar.pyzbar import decode
        results = decode( input )
        if len(results) < 1:
            raise ValueError(f"The QR code in image {string} could not be parsed.")

        return int(results[0].data).to_bytes( 319, 'big' )  # TODO: use exceptions to catch longer codes

    def QR_webcam_parser( string ):
        """Grab images from a webcam until a QR code is found."""

        import cv2
        from pyzbar.pyzbar import decode

        cam_idx = int(string)       # throws ValueError
        cam     = cv2.VideoCapture( cam_idx )
        for _ in range(1200):       # 120 seconds w/ 0.1 second pause between each

            retVal, img = cam.read()
            if retVal:
                results = decode( img )
                if len(results) > 0:
                    return int(results[0].data).to_bytes( 319, 'big' )  # TODO: see earlier TODO

            sleep( 0.1 )

        return None


    # parse the command line args
    cmdline = argparse.ArgumentParser( description="Test out the vaccine passport algorithms." )
    
    methods = cmdline.add_argument_group( 'ACTIONS', "The four actions this program can do." )
    
    methods.add_argument( '--request_QR', action='store_true', help='Request a QR code.' )
    methods.add_argument( '--QR_server', action='store_true', help='Launch the demo server.' )
    methods.add_argument( '--quit_server', action='store_true', help='Tell the QR server to quit.' )
    methods.add_argument( '--verify_QR', action='store_true', help='Verify a QR code.' )
    
    methods = cmdline.add_argument_group( 'PERSONAL', "Information about the person requesting the QR code." )
    
    methods.add_argument( '--given_name', metavar="STRING", type=str, default="Jane", \
        help='The given name of the person requesting a passport.' )
    methods.add_argument( '--surname', metavar='STRING', type=str, default="Smith", \
        help='The surname of the person requesting a passport.' )
    methods.add_argument( '--ohn', metavar='10 DIGITS', type=int, default=1234567890, \
        help='The Ontario Health Number of the person requesting a passport.' )
    methods.add_argument( '--birth_date', metavar='ISO DATE', type=iso_date, default=date(1990,1,1), \
        help='The birth date of the person requesting a passport.' )
    methods.add_argument( '--vax_dates', metavar='ISO DATE', type=iso_date, nargs='*', default=[date(2021,9,20)], \
        help='The days the person requesting a passport was vaccinated.' )
    methods.add_argument( '--QRcode_file', metavar='FILENAME', type=QR_file_parser, \
        help="The person's QR code, stored in a text/binary file." )
    methods.add_argument( '--QRcode_image', metavar='IMAGE FILE', type=QR_image_parser, \
        help="The person's QR code, stored in an image file." )
    methods.add_argument( '--QRcode_webcam', metavar='INDEX', type=QR_webcam_parser, \
        help="The person's QR code, captured from a webcam." )
    methods.add_argument( '--QR_output', metavar='IMAGE FILE', type=argparse.FileType('wb'), \
        help="Once a QR code is retrieved, convert it to an image and store it here." )

    methods = cmdline.add_argument_group( 'SYSTEM', "Tweak system parameters." )
    
    methods.add_argument( '--addr', metavar='IP:PORT', type=str, default="127.0.4.18:3180", \
        help='The IP address and port to connect to.' )
    methods.add_argument( '--bits', metavar='INT', type=int, default=22, \
        help='The number of zero bits to challenge the requester with.' )
    methods.add_argument( '--key_hash', metavar='HEX STRING', type=hexadecimal, \
        default='d20aeab712932f1a14db957406bc266041c2fe1bde86c4a4702d3f02edeeebee', \
        help='The value of the hash key, as a hexadecimal string.' )
    methods.add_argument( '--key_enc', metavar='HEX STRING', type=hexadecimal, \
        default='c48ac8c8e27677a1e33ed165ef9b06a6d0522abf001da8a2e629d015a28849e9', \
        help='The value of the obfuscation key, as a hexadecimal string.' )
    methods.add_argument( '--RSA_key', metavar='FILENAME', type=RSA_parser, \
        help="The value of the server's RSA key, stored in a key: value file." )
    methods.add_argument( '--timeout', metavar='SECONDS', type=int, default=600, \
        help='How long until the program automatically quits. Negative or zero disables this.' )
    methods.add_argument( '-v', '--verbose', action='store_true', \
        help="Be more verbose about what is happening." )

    args = cmdline.parse_args()

    def printf( *args ):
        """A helper to tidy up print statements."""
        print( *args, flush=True )

    # ensure the number of bits is sane
    if (args.bits < 1) or (args.bits > 64):
        args.bits = 22

    # first off, do we have a timeout?
    killer = None           # save this for later
    if args.timeout > 0:

        # define a handler
        def shutdown( time, verbose=False ):

            sleep( time )
            if verbose:
                printf( "Program: exiting after timeout." )

    # launch it
    if args.verbose:
        printf( "Program: Launching background timeout." )
    killer = Thread( target=shutdown, args=(args.timeout,args.verbose), daemon=True )
    killer.start()

    # branch, depending on what's asked
    # the server gets priority
    addr = None           # pre-declare this to allow for cascading
    server_thread = None

    if args.QR_server:
        if args.verbose:
            printf( "Program: Attempting to launch server." )
        addr = split_ip_port( args.addr )

    if addr is not None:

        IP, port = addr
        if args.verbose:
            printf( f"Server: Asked to start on IP {IP} and port {port}." )
            printf( f"Server: Generating g and N, this will take some time." )
        DH = DH_params()
        if args.verbose:
            printf( f"Server: Finished generating g and N." )

        if not args.RSA_key:
            if args.verbose:
                printf( f"Server: No RSA key given, generating one." )
            RSA = RSA_key( bits=RSA_bits )
            if args.verbose:
                printf( f"Server: Finished generating an RSA key." )
        else:
            RSA = args.RSA_key

        if args.verbose:
            printf( f"Server: Populating the databases." )
        
        if type(args.vax_dates) is not list:
            args.vax_dates = [args.vax_dates]
        vax_database = {args.ohn: [args.given_name, args.surname, args.birth_date] + \
                [("Pharma","public",d) for d in args.vax_dates]}

        # use an inline routine as this doesn't have to be globally visible
        def server_loop( IP, port, DH, RSA, key_hash, key_enc, bits, db, verbose=False ):
            
            registered = dict()           # for tracking registered users

            sock = create_socket( IP, port, listen=True )
            if sock is None:
                if verbose:
                    printf( f"Server: Could not create socket, exiting." )
                return

            if verbose:
                printf( f"Server: Beginning connection loop." )
            while True:

                (client, client_address) = sock.accept()
                if verbose:
                    printf( f"Server: Got connection from {client_address}." )

                mode = receive( client, 1 )
                if len(mode) != 1:
                    if verbose:
                        printf( f"Server: Socket error with client, closing it and waiting for another connection." )
                    close_sock( client )
                    continue

                if mode == b'q':
                    if verbose:
                        printf( f"Server: Asked to quit by client. Shutting down." )
                    close_sock( client )
                    close_sock( sock )
                    return

                elif mode == b'r':
                    if verbose:
                        printf( f"Server: Asked to register by client." )

                    temp = server_register( client, DH.g, DH.N, registered )
                    if (temp is None) and verbose:
                            printf( f"Server: Registration failed, closing socket and waiting for another connection." )
                    elif temp is not None:
                        if verbose:
                            printf( f"Server: Registration complete, current users: {[x for x in temp]}." )
                        database = temp

                elif mode == b'p':
                    if verbose:
                        printf( f"Server: Asked for a QR code by client." )

                    temp = retrieve_passport( client, DH, RSA, key_hash, key_enc, bits, registered, db )
                    if (temp is None) and verbose:
                            printf( f"Server: Retrieval failed, closing socket and waiting for another connection." )
                    elif type(temp) == tuple:
                        if verbose:
                            printf( f"Server: Retrieval successful for OHN {temp[2]}." )
                            printf( f"Server:  Shared key is {temp[1]}." )

                elif mode == b'k':
                    if verbose:
                        printf( f"Server: Asked for our public key." )

                    data = i2b(RSA.e, 160) + i2b(RSA.N, 160)
                    count = send( client, data )
                    if (count != len(data)) and verbose:
                        printf( f"Server: Transmission failure, ." )
                    close_sock( client )

                # clean up is done inside the functions
                # loop back

        # launch the server
        if args.verbose:
            printf( "Program: Launching server." )
        server_thread = Thread( target=server_loop, args=(IP, port, DH, RSA, \
                args.key_hash, args.key_enc, args.bits, vax_database, args.verbose), daemon=True )
        server_thread.start()

    # the client is next highest
    client_thread = None
    if args.request_QR and (addr is not None):

        if args.QR_output:      # load this early to shake loose some errors
            import qrcode

        IP, port = addr
        if args.verbose:
            printf( f"Client: Asked to connect to IP {IP} and port {port}." )
        # another inline routine
        def client_routine( IP, port, verbose=False ):

            if verbose:
                printf( f"Client: Grabbing RSA key from server." )

            sock = create_socket( IP, port )
            count = send( sock, b'k' )
            if count != 1:
                printf( f"Client: Could not request RSA key, quitting." )
                return close_sock( sock )

            e_bytes = receive( sock, 160 ) 
            if len(e_bytes) != RSA_bytes:
                printf( f"Client: Could not receive e, quitting." )
                return close_sock( sock )

            N_bytes = receive( sock, 160 )
            if len(N_bytes) != RSA_bytes:
                printf( f"Client: Could not receive N, quitting." )
                return close_sock( sock )

            RSA = RSA_key( pubkey=(b2i(e_bytes), b2i(N_bytes)) )

            # we need values for UUID, secret, and salt
            salt = token_bytes(16)

            # UUID and secret must be the same length after UTF-8 decoding
            uuid   = bytes( randbelow(128) for _ in range(32) ).decode('utf-8')
            secret = bytes( randbelow(128) for _ in range(32) ).decode('utf-8')

            if verbose:
                printf( f"Client: UUID   = {uuid}." )
                printf( f"Client: secret = {secret}." )
                printf( f"Client: salt   = {salt.hex()}." )

                printf( f"Client: Beginning registration." )

            results = client_register( IP, port, uuid, secret, salt )
            if results is None:
                if verbose:
                    printf( f"Client: Registration failed, not attempting the protocol." )
                return
            else:
                g, N, v = results
                DH = DH_params( pair=(g,N) )
                if verbose:
                    printf( f"Client: Registration successful, g = {g}." )

            if verbose:
                printf( f"Client: Requesting the QR code." )

            results = request_passport( IP, port, uuid, secret, salt, DH, RSA, args.ohn, args.birth_date, \
                    args.vax_dates[-1] )
            if results is None:
                if verbose:
                    printf( f"Client: Protocol failed." )
                return
                
            a, K_client, passport = results
            if verbose:
                printf( f"Client: Protocol successful." )
                printf( f"Client:  K_client = {K_client}." )
                printf( f"Client:  passport = {passport.hex()}" )

            args.QRcode_file = passport     # allow for later verification of the passport

            if args.QR_output:
                image = qrcode.make( b2i(passport) )    # storing it as a number is more reliable
                image.save( args.QR_output )
                args.QR_output.close()

            return

        # launch the client
        if args.verbose:
            printf( "Program: Launching client." )
        client_thread = Thread( target=client_routine, args=(IP, port, args.verbose), daemon=True )
        client_thread.start()

    # then, launch the thread that quits the server
    if args.quit_server and (addr is not None):

        IP, port = addr
        if args.verbose:
            print( f"Quit: Asked to connect to IP {IP} and port {port}.", flush=True )
        if client_thread is not None:
            if args.verbose:
                print( f"Quit: Waiting for the client to complete first.", flush=True )
            client_thread.join()

        if args.verbose:
            print( "Quit: Attempting to kill the server.", flush=True )

        # no need for threading here
        sock = create_socket( IP, port )
        if sock is None:
            if args.verbose:
                print( f"Quit: Could not connect to the server to send the kill signal.", flush=True )
        else:
            count = send( sock, b'q' )
            if count != 1:
                if args.verbose:
                    print( f"Quit: Socket error when sending the signal.", flush=True )
            elif args.verbose:
                    print( f"Quit: Signal sent successfully.", flush=True )

            close_sock( sock )

    # verify the QR code (doing this last 
    if args.verify_QR:

        # do we have an RSA key?
        if not args.RSA_key:
            print( "ERROR: When doing verification, you must provide an RSA key!" )
            exit( 1 )

        # what style of input are we using?
        output = None
        for input in [args.QRcode_file, args.QRcode_image, args.QRcode_webcam]:
            if input is not None:
                output = verify_passport( input, args.key_enc, args.RSA_key, args.key_hash )
            if output is not None:
                break

        if output is None:
            print( "The QR code provided did not pass the verification stage." )
        else:
            print( "Success! The QR code was verified", end="" )
            if args.key_hash:
                print( ", and double-confirmed to be generated by the QR server." )
            else:
                print( "." )

            print( "==================================" )
            print( f"given_name    = {output[0]}" )
            print( f"surname       = {output[1]}" )
            print( f"birth date    = {output[2].isoformat()}" )
            print( f"vaccine count = {output[3]}", end="" )
            if output[3] == 15:
                print( " or more" )
            else:
                print()
            print( f"weeks since   = {output[4]}" )

    # now just wait until the threads terminate, or we're asked to die
    while not ((server_thread is None) and (client_thread is None)):

        if not killer.is_alive():
            if args.verbose:
                printf( f"Program: Timeout reached, so exiting." )
            if client_thread is not None:
                client_thread.terminate()
            if server_thread is not None:
                server_thread.terminate()
            exit()

        if (client_thread is not None) and (not client_thread.is_alive()):
            if args.verbose:
                printf( f"Program: Client terminated." )
            client_thread = None
        
        if (server_thread is not None) and (not server_thread.is_alive()):
            if args.verbose:
                printf( f"Program: Server terminated." )
            server_thread = None

#!/usr/bin/env python3

# good news: you get all these functions for free from prior assignment solutions
from encrypt_decrypt__SOLUTION import generate_iv, pad, unpad, xor
from basic_auth__SOLUTION import b2i, blake2b_256, bytes_to_int, calc_A, calc_B, calc_K_client
from basic_auth__SOLUTION import calc_K_server, calc_M1, calc_u, calc_x, client_register
from basic_auth__SOLUTION import close_sock, create_socket, find_Y, i2b, int_to_bytes
from basic_auth__SOLUTION import prim_root, receive, safe_prime, send, server_register
from basic_auth__SOLUTION import split_ip_port

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

from secrets import randbelow, token_bytes
import socket
from sys import exit

from threading import Thread
from time import sleep
from typing import Callable, Iterator, Mapping, Optional, Union


# bad news: all their external imports aren't imported into this namespace, 
#  so you'll need to reimport. Do so here.
### BEGIN
from Crypto.Cipher import AES
from hashlib import shake_256

# allow for future_expansion
RSA_bits   = 1280
RSA_bytes  = RSA_bits >> 3   # same as division by 8
base_bytes = 64
base_bits  = base_bytes << 3 # same as multiplying by 8
hash_bytes = 32
hash_bits  = hash_bytes << 3
salt_bytes = 16
salt_bits  = salt_bytes << 3

birth_epoch = date(1880, 1, 1)
vax_epoch   = date(2006, 6,11)

### END

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

        # delete this comment and insert your code here
        ### BEGIN
    
        sub_bits = bits >> 1
        p = safe_prime( sub_bits )
        q = safe_prime( sub_bits )
        N = p * q
        # we need to make sure N is in the proper range
        while (N >= (1 << bits)) or (N < (1 << (bits-1))) or (p == q):
            p = safe_prime( sub_bits )
            q = safe_prime( sub_bits )
            N = p * q

        return (p,q)

        ### END

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

        # delete this comment and insert your code here
        ### BEGIN
    
        phi_n = (p-1)*(q-1)

        e = randbelow( phi_n )
        while (e < 2) or (gcd( phi_n, e ) > 1):
            e = randbelow( phi_n )

        # we don't allow this, but it works:
        # d = pow( e, -1, phi_n )

        # the hard way, via the Euclidean algorithm
        # NOTE: this is based on an algorithm that's designed to mimic the
        #   version done by hand. There are better approaches.
        storage = [ [1,0,e], [0,1,phi_n] ]
        while storage[-1][-1] not in [0,1]:

            quotient = storage[-2][-1] // storage[-1][-1]
            storage.append( [storage[-2][i] - quotient*storage[-1][i] for i in range(3)] )

        assert storage[-1][-1] != 0     # no inverse, which is bad!
        
        # ensure this value isn't negative
        if storage[-1][0] < 0:
            storage[-1][0] += phi_n

        return (e, storage[-1][0])

        ### END

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

        # delete this comment and insert your code here
        ### BEGIN
    
        if self.d is None:
            return None

        return pow( b2i(message), self.d, self.N )

        ### END

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

        # delete this comment and insert your code here
        ### BEGIN
    
        return pow( b2i(signature), self.e, self.N ) == b2i(message)

        ### END

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

        # delete this comment and insert your code here
        ### BEGIN
    
        return pow( b2i(message), self.e, self.N )

        ### END

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

        # delete this comment and insert your code here
        ### BEGIN
    
        return self.sign( cypher )          # cheat!

        ### END

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

    # delete this comment and insert your code here
    ### BEGIN
    
    gn_enc = given_name.encode('utf-8')
    sr_enc = surname.encode('utf-8')

    # need to shave off characters? 
    while (len(gn_enc) + len(sr_enc) + 1) > target:

        if len(given_name) > len(surname):
            given_name = given_name[:-1]
        else:
            surname = surname[:-1]

        gn_enc = given_name.encode('utf-8')
        sr_enc = surname.encode('utf-8')

    # or pad things up?
    len_enc = len(gn_enc) + len(sr_enc) + 1
    if len_enc < target:

        # add all the padding in one go, rather than incrementally
        split   = randbelow( target - len_enc )
        gn_enc += bytes(split)
        sr_enc += bytes(target - len_enc - split)

    return int_to_bytes( len(gn_enc), 1 ) + gn_enc + sr_enc

    ### END

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

    # delete this comment and insert your code here
    ### BEGIN

    # convert the numeric fields
    vax_count = min( vax_count, 0xf )   # 4 bits
    if vax_count == 0:                  # 12 bits
        vax_since = 0xfff
    else:
        vax_since = min( max((last_vax_date - vax_epoch).days,0) // 7, 0xfff )
    vax_info  = vax_since + (vax_count << 12)                         # 4 + 12 = 2 bytes
    birth_days = min( max((birthdate - birth_epoch).days,0), 0xffff ) # 2 bytes

    # that's all the prep work we need
    return int_to_bytes( vax_info, 2 ) + int_to_bytes( birth_days, 2 ) + \
            encode_name( given_name, surname, 92 )
    
    ### END

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

    # delete this comment and insert your code here
    ### BEGIN

    # take advantage of block_size to automatically size the padding
    h       = shake_256()
    padded  = custom
    padded += b'\x00'*( (-len(padded)) % h.block_size )    # zero padding is legit!
    padded += key_hash
    padded += b'\x00'*( (-len(padded)) % h.block_size )

    # calculate and return the hash
    h.update( padded + data + bytes([length]) )
    return h.digest(length)

    ### END


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

    # delete this comment and insert your code here
    ### BEGIN

    # let's show off a bit with this
    return b''.join( nonce[2*i:2*i+2] + plaintext[12*i:12*(i+1)] + \
            inner_tag[2*i:2*i+2] for i in range(8) )

    # "for i in range(8):" is easier to understand, admittedly

    ### END


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

    # delete this comment and insert your code here
    ### BEGIN

    # we need an IV
    iv = generate_iv( 16 )

    # figure out how many blocks
    padded = pad( plaintext, 16 )
    blocks = len(padded) // 16      # guaranteed to divide evenly

    # create the stream to XOR against
    crypt      = AES.new( key_enc, AES.MODE_ECB )
    stream     = crypt.encrypt( b''.join( xor( int_to_bytes(i,16), iv ) for i in range(blocks) ) )
    cyphertext = xor( stream, padded )

    # KMAC it
    iv_c = iv + cyphertext
    tag = pseudoKMAC( key_mac, iv_c, 32, b'OH SARS QR MAC' ) 

    # all done!
    return iv_c + tag

    ### END

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

    # delete this comment and insert your code here
    ### BEGIN

    # sanity check the length
    if (len(cyphertext) < 64) or (len(cyphertext) % 16):
        return None

    # KMAC what we've got
    tag = pseudoKMAC( key_mac, cyphertext[:-32], 32, b'OH SARS QR MAC' ) 

    if tag != cyphertext[-32:]:
        return None

    # from here, try decrypting as if legit
    # we need an IV
    iv     = cyphertext[:16]
    padded = cyphertext[16:-32] 

    # figure out how many blocks
    blocks = len(padded) // 16      # still guaranteed to divide evenly!

    # create the stream to XOR against
    crypt      = AES.new( key_enc, AES.MODE_ECB )
    stream     = crypt.encrypt( b''.join( xor( int_to_bytes(i,16), iv ) for i in range(blocks) ) )
    plaintext = xor( stream, padded )

    # "plaintext" is not actually the plaintext! It needs depadding
    return unpad( plaintext )

    ### END

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
    ### BEGIN

    # grab a nonce and figure out the plaintext
    nonce = token_bytes(16)
    plaintext = gen_plaintext( given_name, surname, birthdate, vax_count, \
                    last_vax_date )
    
    # create the tag
    inner_tag = pseudoKMAC( key_hash, nonce + plaintext, 16, b'OH SARS SECOND VERIFY' )

    # interleave everything and encrypt
    crypt     = AES.new( key_enc, AES.MODE_ECB )
    encrypted = crypt.encrypt( interleave_data( plaintext, nonce, inner_tag ) )

    # tag then sign it
    outer_tag = shake_256( nonce + plaintext + inner_tag ).digest(31)
    combo     = encrypted + outer_tag

    # all done
    return combo + i2b( RSA_key.sign(combo), RSA_key.bytes )

    ### END

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
    ### BEGIN

    # check the signature's authenticity
    if not RSA_key.verify( passport[159:], passport[:159] ):
        return None

    # strip out the outer tag and decrypt
    outer_tag   = passport[128:159]
    crypt       = AES.new( key_enc, AES.MODE_ECB )
    interleaved = crypt.decrypt( passport[:128] )

    # de-interleave into the nonce, plaintext, and tag
    nonce     = b''.join( interleaved[16*i:16*i+2] for i in range(8) )
    plaintext = b''.join( interleaved[16*i+2:16*i+14] for i in range(8) )
    inner_tag = b''.join( interleaved[16*i+14:16*i+16] for i in range(8) )

    # verify the outer tag
    outer_tag_ref = shake_256( nonce + plaintext + inner_tag ).digest(31)
    if outer_tag != outer_tag_ref:
        return None

    # verify the inner tag, if possible
    if key_hash:
        inner_tag_ref = pseudoKMAC( key_hash, nonce + plaintext, 16, b'OH SARS SECOND VERIFY' )
        if inner_tag != inner_tag_ref:
            return None

    # if still here, uncompress the plaintext and translate into the expected output
    vax_count   = plaintext[0] >> 4
    vax_offset  = ((plaintext[0] & 0xf) << 8) + plaintext[1]

    if (vax_count > 0) and (vax_offset < 0xfff):
        weeks_since = ((date.today() - vax_epoch).days // 7) - vax_offset
    else:
        weeks_since = 0xfff

    print( f"DEBUG: vax-related plaintext = {plaintext[0:2].hex()}" )
    print( f"DEBUG: vax_count = {vax_count}" )
    print( f"DEBUG: vax_offset = {vax_offset}" )
    print( f"DEBUG: weeks_since = {weeks_since}" )

    birth_date  = birth_epoch + timedelta(days=int.from_bytes( plaintext[2:4], 'big' ))

    # extract the names and strip out the zeros
    given_enc   = plaintext[5:plaintext[4]+5]
    while given_enc[-1] == 0:
        given_enc = given_enc[:-1]

    sur_enc     = plaintext[plaintext[4]+5:]
    while sur_enc[-1] == 0:
        sur_enc = sur_enc[:-1]

    try:
        given_name = given_enc.decode('utf-8')
        surname    = sur_enc.decode('utf-8')
    except UnicodeDecodeError:
        return None

    return (given_name, surname, birth_date, vax_count, weeks_since)

    ### END

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

    # delete this comment and insert your code here
    ### BEGIN

    # a lot of this is just straight from A2, with some minor tweaks
    varprint( DH_params.g, 'g' )
    varprint( DH_params.N, 'N_DH' )
    varprint( RSA_key.N, 'N_RSA' )
    varprint( RSA_key.e, 'e_RSA' )
    varprint( uuid, 'uuid' )
    varprint( secret, 'secret' )
    varprint( salt, 'salt' )

    # connect to the server
    sock = create_socket( ip, port )
    if sock is None:
        return None

    # send 'p'
    count = send( sock, b'p' )
    if count != 1:
        return close_sock( sock )

    # retrieve g
    g_bytes = receive( sock, base_bytes )
    if len(g_bytes) != base_bytes:
        return close_sock( sock )

    # check it matches
    if bytes_to_int(g_bytes) != DH_params.g:
        return close_sock( sock )

    # retrieve N
    N_bytes = receive( sock, base_bytes )
    if len(N_bytes) != base_bytes:
        return close_sock( sock )

    # check it matches
    if bytes_to_int(N_bytes) != DH_params.N:
        return close_sock( sock )

    # k is already calculated by DH_params
    varprint( DH_params.k, 'k' )

    # calculate x and v
    x = calc_x( salt, secret ) 
    v = DH_params.calc_A( x )   # same action as A!

    # generate a via rejection sampling
    a = randbelow( DH_params.N )
    while (a == 0):
        a = randbelow( DH_params.N )
    varprint( a, 'a' )

    # calculate Enc(A)
    A = DH_params.calc_A( a )
    varprint( A, 'A' )

    EncA = RSA_key.encrypt( A )
    EncA_bytes = int_to_bytes( EncA, RSA_bytes )
    varprint( EncA, 'Enc(A)' )

    # send Enc(A), uuid
    uuid_bytes = uuid.encode('utf-8')
    u_len = int_to_bytes( len(uuid_bytes), 1 )
    data = EncA_bytes + u_len + uuid_bytes
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # get s, B
    s = receive( sock, salt_bytes )
    if (len(s) != salt_bytes) or (salt != s):
        return close_sock( sock )

    B_bytes = receive( sock, base_bytes )
    if len(B_bytes) != base_bytes:
        return close_sock( sock )

    B = bytes_to_int( B_bytes )
    varprint( B, 'B' )

    # compute u
    u = calc_u( A, B_bytes )
    varprint( u, 'u' )

    # compute K_client
    K_client = calc_K_client( DH_params.N, B, DH_params.k, v, a, u, x )
    varprint( K_client, 'K_client' )
    K_client_bytes = i2b( K_client, base_bytes )

    # get bits
    bits = receive( sock, 1 )
    if len(bits) != 1:
        return close_sock( sock )

    # find Y
    Y = find_Y( K_client, bits[0] )
    varprint( b2i(Y), 'Y' )

    # send Y
    count = send( sock, Y )
    if count != len(Y):
        return close_sock( sock )

    # receive M1_server
    M1 = receive( sock, hash_bytes )
    if len(M1) != hash_bytes:
        return close_sock( sock )

    varprint( M1, 'M1' )

    # now that we're set, build the health data
    health_data  = int_to_bytes( health_id, 5 ) + bytes(3)
    health_data += i2b( min((birthdate - birth_epoch).days,0xffff), 2 ) # head off an exception
    health_data += bytes(4)
    health_data += i2b( min((vax_date - vax_epoch).days,0xffff), 2 )

    varprint( health_data, 'health_data' )
    # figure out the encryption key
    health_key = pseudoKMAC( i2b(RSA_key.N,RSA_key.bytes) + i2b(RSA_key.e,RSA_key.bytes),
            i2b(K_client,base_bytes), 32, b'OH SARS KEYEXTEND 1' )

    varprint( health_key, 'health_key' )

    # actually encrypt the data
    crypt    = AES.new( health_key, AES.MODE_ECB )
    enc_data = crypt.encrypt( health_data )

    varprint( enc_data, 'enc_data' )

    # send it across the wire
    count = send( sock, enc_data )
    if count != len(enc_data):
        return close_sock( sock )

    # retrieve the QR code and tidy up
    QR_length = receive( sock, 4 )
    if len(QR_length) != 4:
        return close_sock( sock )

    count = b2i(QR_length)
    varprint( count, 'len(Enc(QR code))' )

    QR_enc = receive( sock, count )
    if len(QR_enc) != count:
        return close_sock( sock )

    # we're done with socket communication
    close_sock( sock )

    # decrypt the QR code
    QRcode = decrypt_data( QR_enc, K_client_bytes[:(base_bytes>>1)], \
            K_client_bytes[(base_bytes>>1):] )

    if QRcode is None:
        return None
    else:
        return (a, K_client, QRcode)

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

    # delete this comment and insert your code here
    ### BEGIN

    varprint( DH_params.g, 'g', 'Server' )
    varprint( DH_params.N, 'N_DH', 'Server' )
    varprint( DH_params.k, 'k', 'Server' )

    varprint( RSA_key.N, 'N_RSA', 'Server' )
    varprint( RSA_key.e, 'e_RSA', 'Server' )
    varprint( RSA_key.d, 'd_RSA', 'Server' )

    # send g and N
    g, N = map( lambda x: i2b(x,base_bytes), [DH_params.g, DH_params.N] )
    data = g + N
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # get A
    EncA_bytes = receive( sock, RSA_bytes )
    if len(EncA_bytes) != RSA_bytes:
        return close_sock( sock )
    varprint( EncA_bytes, "Enc(A)", "Server" )

    A = RSA_key.decrypt( EncA_bytes )
    varprint( A, "A", "Server" )
    if A == 0:
        return close_sock( sock )

    # get the UUID
    len_uuid_bytes = receive( sock, 1 )
    if len(len_uuid_bytes) != 1:
        return close_sock( sock )
    varprint( len_uuid_bytes[0], "len(uuid)", "Server" )

    uuid_bytes = receive( sock, len_uuid_bytes[0] )
    if len(uuid_bytes) != len_uuid_bytes[0]:
        return close_sock( sock )

    try:
        uuid = uuid_bytes.decode('utf-8')
    except:
        return close_sock( sock )

    varprint( uuid, "uuid", "Server" )

    # retrieve s and v if possible
    if uuid in registered:
        s, v = registered[uuid]
    else:
        return close_sock( sock )

    varprint( v, "v", "Server" )
    varprint( s, "s", "Server" )

    # generate b and calculate B
    b = randbelow( DH_params.N )
    while (b == 0):
        b = randbelow( DH_params.N )
    varprint( b, 'b', "Server" )

    B = DH_params.calc_B( b, v )
    varprint( B, 'B', "Server" )

    # send s and B
    data = s + i2b(B, base_bytes)
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # compute u
    u = calc_u( A, B )
    varprint( u, 'u', "Server" )

    # compute K_server
    K_server = calc_K_server( DH_params.N, A, b, v, u )
    varprint( K_server, 'K_server', "Server" )
    K_server_bytes = i2b( K_server, base_bytes )    # need this later

    # send bits
    count = send( sock, i2b(bits, 1) )
    if count != 1:
        return close_sock( sock )

    # receive Y
    Y = receive( sock, base_bytes )
    if len(Y) != base_bytes:
        return close_sock( sock )
    varprint( Y, 'Y', "Server" )

    # check Y (use copy-paste code for speed)
    base = bits >> 3
    mask = ~((1 << (8 - (bits&7))) - 1)

    hashVal = blake2b_256( i2b(K_server,base_bytes) + Y )
    if (hashVal[:base] != bytes(base)) or ((hashVal[base] & mask) != 0):
        return close_sock( sock )

    # compute M1
    M1 = calc_M1( A, K_server, Y )
    varprint( bytes_to_int(M1), 'M1', "Server" )

    # send M1. Don't close the socket yet!
    count = send( sock, M1 )
    if count != len(M1):
        return close_sock( sock )

    # figure out the encryption key
    health_key = pseudoKMAC( i2b(RSA_key.N,RSA_key.bytes) + i2b(RSA_key.e,RSA_key.bytes),
            i2b(K_server,base_bytes), 32, b'OH SARS KEYEXTEND 1' )

    varprint( health_key, 'health_key', "Server" )

    # grab the incoming health info
    health_enc = receive( sock, 16 )
    if len(health_enc) != 16:
        return close_sock( sock )

    # decrypt and validate
    crypt       = AES.new( health_key, AES.MODE_ECB )
    health_data = crypt.decrypt( health_enc )

    varprint( health_data, 'health_data', "Server" )

    if health_data[5:8] != bytes(3):
        return close_sock( sock )
    if health_data[10:14] != bytes(4):
        return close_sock( sock )

    # all good? Extract the key data
    ohn        = b2i( health_data[:5] )
    varprint( ohn, 'ohn', "Server" )

    birth_date = birth_epoch + timedelta( days=b2i(health_data[8:10]) )
    varprint( birth_date, 'birth_date', "Server" )

    vax_date   = vax_epoch + timedelta( days=b2i(health_data[14:16]) )
    varprint( vax_date, 'vax_date', "Server" )

    # look it up in the database and validate
    if ohn not in vax_database:
        return close_sock( sock )

    stored = vax_database[ohn]
    if birth_date != stored[2]:
        return close_sock( sock )
    
    vax_count = len(stored) - 3
    for vax in stored[3:]:
        if vax[2] == vax_date:
            break                   # prevents the return statement from executing
    else:
        return close_sock( sock )

    # generate the QR code
    if vax_count > 0:
        last_vax_date = stored[-1][2]
    else:
        last_vax_date = date.today()        # fill in a dummy value

    passport = create_passport( stored[0], stored[1], stored[2], vax_count, \
        last_vax_date, key_hash, key_enc, RSA_key )

    # encrypt it and send it back
    enc_QR = encrypt_data( passport, K_server_bytes[:(base_bytes>>1)], \
            K_server_bytes[(base_bytes>>1):] )

    count = send( sock, i2b(len(enc_QR), 4) )
    if count != 4:
        return close_sock( sock )
    
    count = send( sock, enc_QR )
    if count != len(enc_QR):
        return close_sock( sock )

    # if we've made it this far, we can't fail
    close_sock( sock )
    return (b, K_server, ohn, passport)

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

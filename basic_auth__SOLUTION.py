#!/usr/bin/env python3

##### IMPORTS

import argparse
from multiprocessing import Process
from sys import exit
from time import sleep

# Insert your imports here
### BEGIN
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.backends import default_backend

from secrets import randbits
import socket
from sympy import gcd, isprime, primefactors, sieve

# sieve speed-up courtesy: Wiener, Michael J. "Safe Prime Generation with a Combined Sieve." IACR Cryptol. ePrint Arch. 2003 (2003): 186.
# create a sieve of values to avoid
sieve.extend_to_no(150)                     # somewhere around here is best for my workstation
prime_list  = list( sieve._list )[2:]
prime_avoid = [(r-1)//2 for r in prime_list]
### END

##### METHODS

def split_ip_port( string ):
    """Split the given string into an IP address and port number.
    
    PARAMETERS
    ==========
    string: A string of the form IP:PORT.

    RETURNS
    =======
    If successful, a tuple of the form (IP,PORT), where IP is a 
      string and PORT is a number. Otherwise, returns None.
    """

    assert type(string) == str

    try:
        idx = string.index(':')
        return (string[:idx], int(string[idx+1:]))
    except:
        return None

def int_to_bytes( value, length ):
    """Convert the given integer into a bytes object with the specified
       number of bits. Uses network byte order.

    PARAMETERS
    ==========
    value: An int to be converted.
    length: The number of bytes this number occupies.

    RETURNS
    =======
    A bytes object representing the integer.
    """
    
    assert type(value) == int
    assert length > 0

    return value.to_bytes( length, 'big' )

### BEGIN
def i2b( x, l ):
    """The above, but it passes through bytes objects."""
    if type(x) == int:
        return x.to_bytes( l, 'big' )
    elif type(x) == bytes:
        return x
    else:
        raise Exception(f'Expected an int or bytes, got {type(x)}!')
### END

def bytes_to_int( value ):
    """Convert the given bytes object into an integer. Uses network
       byte order.

    PARAMETERS
    ==========
    value: An bytes object to be converted.

    RETURNS
    =======
    An integer representing the bytes object.
    """
    
    assert type(value) == bytes
    return int.from_bytes( value, 'big' )

### BEGIN
def b2i( x ):
    """The above, but it passes through int objects."""
    if type(x) == bytes:
        return int.from_bytes( x, 'big' )
    elif type(x) == int:
        return x
    else:
        raise Exception(f'Expected an int or bytes, got {type(x)}!')
### END

def create_socket( ip, port, listen=False ):
    """Create a TCP/IP socket at the specified port, and do the setup
       necessary to turn it into a connecting or receiving socket. Do
       not actually send or receive data here, and do not accept any
       incoming connections!

    PARAMETERS
    ==========
    ip: A string representing the IP address to connect/bind to.
    port: An integer representing the port to connect/bind to.
    listen: A boolean that flags whether or not to set the socket up
       for connecting or receiving.

    RETURNS
    =======
    If successful, a socket object that's been prepared according to 
       the instructions. Otherwise, return None.
    """
    
    assert type(ip) == str
    assert type(port) == int

    # delete this comment and insert your code here
    ### BEGIN
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

    try:
        if listen:
            sock.bind( (ip, port) )
            sock.listen(2)
        else:
            sock.connect( (ip, port) )

        return sock
    except:
        return None
    ### END

def send( sock, data ):
    """Send the provided data across the given socket. This is a
       'reliable' send, in the sense that the function retries sending
       until either a) all data has been sent, or b) the socket 
       closes.

    PARAMETERS
    ==========
    sock: A socket object to use for sending and receiving.
    data: A bytes object containing the data to send.

    RETURNS
    =======
    The number of bytes sent. If this value is less than len(data),
       the socket is dead and a new one must be created, plus an unknown
       amount of the data was transmitted.
    """
    
    assert type(sock) == socket.socket
    assert type(data) == bytes

    # delete this comment and insert your code here
    ### BEGIN
    sent = 0
    while sent < len(data):
        try:
            out = sock.send( data[sent:] )
        except:
            return sent

        if out <= 0:
            return sent
        sent += out

    return sent
    ### END

def receive( sock, length ):
    """Receive the provided data across the given socket. This is a
       'reliable' receive, in the sense that the function never returns
       until either a) the specified number of bytes was received, or b) 
       the socket closes. Never returning is an option.

    PARAMETERS
    ==========
    sock: A socket object to use for sending and receiving.
    length: A positive integer representing the number of bytes to receive.

    RETURNS
    =======
    A bytes object containing the received data. If this value is less than 
       length, the socket is dead and a new one must be created.
    """
    
    assert type(sock) == socket.socket
    assert length > 0

    # delete this comment and insert your code here
    ### BEGIN
    intake = b''
    while len(intake) < length:

        rem = length - len(intake)
        try:
            input = sock.recv( min(rem,4096) )
        except:
            return intake

        if input == b'':
            return intake
        intake = b''.join([intake,input])

    return intake
    ### END

def safe_prime( bits=512 ):
    """Generate a safe prime that is at least 'bits' bits long. The result
       should be greater than 1 << (bits-1).

    PARAMETERS
    ==========
    bits: An integer representing the number of bits in the safe prime.
       Must be greater than 1.

    RETURNS
    =======
    An interger matching the spec.
    """

    assert bits > 1

    # delete this comment and insert your code here
    ### BEGIN

    # do a linear search
    maximum = 1 << (bits-1)
    q       = randbits(bits-1) | (1 << (bits-2))      # guarantee the high bit is set
    q      += 5 - (q % 6)                             # make it 5 (mod 6)

    while True:

        # sieve out some known-bad values
        for i,r in enumerate(prime_list):
            if (q % r) == prime_avoid[i]:
                break
        else:
            if isprime( q ):
                cand = (q<<1) + 1
                if isprime( cand ):
                    return cand

        q += 6          # ensure it's always 5 (mod 6)

        if q >= maximum:
            q    = (1 << (bits-2)) + 1
            q   += 5 - (q % 6)                             # reset this back to where we expect

    ### END

def prim_root( N ):
    """Find a primitive root for N, a large safe prime. Hint: it isn't
       always 2.

    PARAMETERS
    ==========
    N: The prime in question. May be an integer or bytes object.

    RETURNS
    =======
    An integer representing the primitive root. Must be a positive
       number greater than 1.
    """

    # delete this comment and insert your code here
    ### BEGIN

    # IMPORTANT: This assumes N is a safe prime. Will fail for other cases!
    group   = N-1
    fact    = N>>1      # there's only two prime factors of the group, one of which is 2!

    # do a linear search
    for c in range(2,N):

        if gcd(N,c) != 1:
            continue
        elif pow( c, 2, N ) == 1:
            continue
        elif pow( c, fact, N ) == 1:
            continue
        else:
            return c

    ### END


def calc_x( s, pw ):
    """Calculate the value of x, according to the assignment.

    PARAMETERS
    ==========
    s: The salt to use. A bytes object consisting of 16 bytes.
    pw: The password to use, as a string.

    RETURNS
    =======
    An integer representing x.
    """

    assert type(pw) == str
    assert type(s) == bytes

    # delete this comment and insert your code here
    ### BEGIN

    hash = hashes.Hash( hashes.SHA256(), default_backend() )
    hash.update( s + pw.encode('utf-8') )
    return bytes_to_int( hash.finalize() )

    ### END

def calc_A( N, g, a ):
    """Calculate the value of A, according to the assignment.

    PARAMETERS
    ==========
    N: The safe prime. Could be an integer or bytes object.
    g: A primitive root of N. Could be an integer or bytes object.
    a: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing A.
    """

    # delete this comment and insert your code here
    ### BEGIN

    # this also works well:
#    N, g, a = [bytes_to_int(c) if type(c) == bytes else c \
#            for c in [N, g, a]]

    # new way:
    N, g, a = map( b2i, [N, g, a] )

    return pow(g, a, N)

    ### END

def calc_B( N, g, b, k, v ):
    """Calculate the value of B, according to the assignment.

    PARAMETERS
    ==========
    N: The safe prime. Could be an integer or bytes object.
    g: A primitive root of N. Could be an integer or bytes object.
    b: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.
    k: The hash of N and g. Could be an integer or bytes object.
    v: See the assignment sheet. Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing B.
    """

    # delete this comment and insert your code here
    ### BEGIN

    N, g, b, k, v = map( b2i, [N, g, b, k, v] )

    return (k*v + pow(g,b,N)) % N

    ### END

def calc_u( A, B ):
    """Calculate the value of u, according to the assignment.

    PARAMETERS
    ==========
    A: See calc_A(). Could be an integer or bytes object.
    B: See calc_B(). Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing u.
    """

    # delete this comment and insert your code here
    ### BEGIN

    # ints to bytes takes more thought
    A, B = map( lambda x: i2b(x,64), [A, B] )

    hash = hashes.Hash( hashes.SHA256(), default_backend() )
    hash.update( A + B )
    return bytes_to_int( hash.finalize() )

    ### END

def calc_K_client( N, B, k, v, a, u, x ):
    """Calculate the value of K_client, according to the assignment.

    PARAMETERS
    ==========
    N: The safe prime. Could be an integer or bytes object.
    B: See calc_B(). Could be an integer or bytes object.
    k: The hash of N and g. Could be an integer or bytes object.
    v: See the assignment sheet. Could be an integer or bytes object.
    a: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.
    u: The hash of A and B. Could be an integer or bytes object.
    x: See calc_x(). Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing K_client.
    """

    # delete this comment and insert your code here
    ### BEGIN

    N, B, k, v, a, u, x = map( b2i, [N, B, k, v, a, u, x] )

    return pow(B - k*v, a + u*x, N)

    ### END

def calc_K_server( N, A, b, v, u ):
    """Calculate the value of K_server, according to the assignment.

    PARAMETERS
    ==========
    N: The safe prime. Could be an integer or bytes object.
    A: See calc_A(). Could be an integer or bytes object.
    b: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.
    v: See the assignment sheet. Could be an integer or bytes object.
    u: The hash of A and B. Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing K_server.
    """

    # delete this comment and insert your code here
    ### BEGIN

    N, A, b, v, u = map( b2i, [N, A, b, v, u] )

    return pow( A*pow(v,u,N), b, N )

    ### END

def calc_M1( A, B, K_client ):
    """Calculate the value of M1, according to the assignment.

    PARAMETERS
    ==========
    A: See calc_A(). Could be an integer or bytes object.
    B: See calc_B(). Could be an integer or bytes object.
    K_client: See calc_K_client(). Could be an integer or bytes object.

    RETURNS
    =======
    A bytes object representing M1.
    """

    # delete this comment and insert your code here
    ### BEGIN

    A, B, K_client = map( lambda x: i2b(x,64), [A, B, K_client] )

    hash = hashes.Hash( hashes.SHA256(), default_backend() )
    hash.update( A + B + K_client )
    return hash.finalize()

    ### END

def calc_M2( A, M1, K_server ):
    """Calculate the value of M2, according to the assignment.

    PARAMETERS
    ==========
    A: See calc_A(). Could be an integer or bytes object.
    M1: See calc_M1(). Could be an integer or bytes object.
    K_server: See calc_K_server(). Could be an integer or bytes object.

    RETURNS
    =======
    A bytes object representing M2.
    """

    # delete this comment and insert your code here
    ### BEGIN

    # lengths matter here, so do this the other way
    length = [64,32,64]
    A, M1, K_server = [int_to_bytes(c, length[i]) if type(c) == int else c \
            for i,c in enumerate([A, M1, K_server])]

    hash = hashes.Hash( hashes.SHA256(), default_backend() )
    hash.update( A + M1 + K_server )
    return hash.finalize()

    ### END

def client_prepare():
    """Do the preparations necessary to connect to the server. Basically,
       just generate a salt.

    RETURNS
    =======
    A bytes object containing a randomly-generated salt, 16 bytes long.
    """

    # delete this comment and insert your code here
    ### BEGIN
    return int_to_bytes( randbits(16*8), 16 )

    ### END

def server_prepare():
    """Do the preparations necessary to accept clients. Generate N and g,
       and compute k.

    RETURNS
    =======
    A tuple of the form (N, g, k), containing those values as integers.
    """

    # delete this comment and insert your code here
    ### BEGIN
    N = safe_prime()
    g = prim_root( N )
    k = calc_u( N, g )      # same thing!

    return (N, g, k)
    ### END

### BEGIN
def close_sock( sock ):
    """A helper to close sockets cleanly."""
    try:
        sock.shutdown(socket.SHUT_RDWR)
        sock.close()
    except:
        pass
    return None

def varprint( data, label, source="Client" ):
    """A helper for printing out data."""
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

### END
def client_register( ip, port, username, pw, s ):
    """Register the given username with the server, from the client.
       IMPORTANT: don't forget to send 'r'!

    PARAMETERS
    ==========
    ip: The IP address to connect to, as a string.
    port: The port to connect to, as an int.
    username: The username to register, as a string.
    pw: The password, as a string.
    s: The salt, a bytes object 16 bytes long.

    RETURNS
    =======
    If successful, return a tuple of the form (N, g, v), all integers.
       On failure, return None.
    """

    # delete this comment and insert your code here
    ### BEGIN

    varprint( username, "username" )
    varprint( pw, "pw" )
    varprint( s, "salt" )

    # connect to the server
    sock = create_socket( ip, port )
    if sock is None:
        return None

    # send 'r'
    count = send( sock, b'r' )
    if count != 1:
        return close_sock( sock )

    # retrieve N and g
    expected = 128 # 512 bits + 512 bits
    N_g = receive( sock, expected )
    if len(N_g) != expected:
        return close_sock( sock )

    N = N_g[:expected>>1]
    g = N_g[expected>>1:]

    varprint( N_g, None )
    varprint( bytes_to_int(N), "N" )
    varprint( bytes_to_int(g), "g" )

    # calculate x and v
    x = calc_x( s, pw ) 
    v = calc_A( N, g, x )

    varprint( x, "x" )
    varprint( v, "v" )

    # send (username, s, v)
    u_enc = username.encode('utf-8')
    assert len(u_enc) < 256

    data = int_to_bytes( len(u_enc), 1 ) + u_enc + s + int_to_bytes( v, 64 )

    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # kill the connection
    close_sock( sock )

    print( "Client: Registration successful." )
    return tuple(map( b2i, [N, g, v] ))

    ### END

def server_register( sock, N, g, database ):
    """Handle the server's side of the registration. IMPORTANT: reading the
       initial 'r' has been handled for you.

    PARAMETERS
    ==========
    sock: A socket object that contains the client connection.
    N: A safe prime. Could be an integer or bytes object.
    g: A primitive root of the safe prime. Could be an integer or bytes object.
    database: A dictionary of all registered users. The keys are usernames
       (as strings!), and the values are tuples of the form (s, v), where s
       is the salt (16 bytes) and v is as per the assignment (integer).

    RETURNS
    =======
    If the registration process was successful, return an updated version of the
       database. If it was not, return None. NOTE: a username that tries to
       re-register with a different salt and/or password is likely malicious,
       and should therefore count as an unsuccessful registration.
    """

    # delete this comment and insert your code here
    ### BEGIN

    varprint( N, 'N', "Server" )
    varprint( g, 'g', "Server" )

    N, g = map( lambda x: i2b(x,64), [N, g] )

    # send N and g
    data = N + g
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # get username
    count = receive( sock, 1 )
    if len(count) != 1:
        return close_sock( sock )
    count = bytes_to_int( count )

    varprint( count, 'username_length', "Server" )

    u_enc = receive( sock, count )
    if len(u_enc) != count:
        return close_sock( sock )

    varprint( u_enc, 'u_enc', "Server" )
    try:
        username = u_enc.decode('utf-8')
    except:
        return close_sock( sock )
    varprint( username, 'username', "Server" )

    # get s, v
    s = receive( sock, 16 )
    if len(s) != 16:
        return close_sock( sock )
    varprint( s, 'salt', "Server" )
    
    v = receive( sock, 64 )  # 512 // 8
    if len(v) != 64:
        return close_sock( sock )
    varprint( v, 'v', "Server" )
    
    v = bytes_to_int( v )
    varprint( v, 'v', "Server" )

    # were we already registered?
    if username in database:
        temp = database[username]
        if (s != temp[0]) or (v != temp[1]):
            return close_sock( sock )
        else:
            print( "Server: Repeat registration attempted." )

    # all finished with the connection
    close_sock( sock )

    print( "Server: Registration successful." )

    # save them and return
    database[username] = (s, v)
    return database

    ### END

def client_protocol( ip, port, N, g, username, pw, s ):
    """Register the given username with the server, from the client.
       IMPORTANT: don't forget to send 'p'!

    PARAMETERS
    ==========
    ip: The IP address to connect to, as a string.
    port: The port to connect to, as an int.
    N: A safe prime. Could be an integer or bytes object.
    g: A primitive root of the safe prime. Could be an integer or bytes object.
    username: The username to register, as a string.
    pw: The password, as a string.
    s: The salt, a bytes object 16 bytes long. Must match what the server 
       sends back.

    RETURNS
    =======
    If successful, return a tuple of the form (a, K_client), where both a and 
       K_client are integers. If not, return None.
    """

    # delete this comment and insert your code here
    ### BEGIN

    varprint( N, 'N' )
    varprint( g, 'g' )
    varprint( username, 'username' )
    varprint( pw, 'pw' )
    varprint( s, 's' )

    # connect to the server
    sock = create_socket( ip, port )
    if sock is None:
        return None

    # send 'p'
    count = send( sock, b'p' )
    if count != 1:
        return close_sock( sock )

    # calculate k before conversions, as it might be more efficient
    k = calc_u( N, g )      # same thing as u! 
    varprint( k, 'k' )

    # conversions!
    N, g = map( b2i, [N, g] )

    # calculate x and v
    x = calc_x( s, pw ) 
    v = calc_A( N, g, x )

    varprint( x, 'x' )
    varprint( v, 'v' )

    # generate a via rejection sampling
    a = randbits( 512 )
    while a >= N:
        a = randbits( 512 )
    varprint( a, 'a' )

    # calculate A
    A = calc_A( N, g, a )
    A_bytes = int_to_bytes( A, 64 )
    varprint( A, 'A' )

    # send username, A
    u_enc = username.encode('utf-8')
    u_len = int_to_bytes( len(u_enc), 1 )

    data = u_len + u_enc + A_bytes
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # get s, B
    expected = 16 + 64
    s_B = receive( sock, expected )
    if len(s_B) != expected:
        return close_sock( sock )
    varprint( s_B, None )

    if s != s_B[:16]:
        return close_sock( sock )

    B = bytes_to_int( s_B[16:] )
    varprint( B, 'B' )

    # compute u
    u = calc_u( A_bytes, s_B[16:] )
    varprint( u, 'u' )

    # compute K_client
    K_client = calc_K_client( N, B, k, v, a, u, x )
    varprint( K_client, 'K_client' )

    # compute M1
    M1 = calc_M1( A_bytes, s_B[16:], K_client )
    varprint( M1, 'M1' )

    # send M1
    count = send( sock, M1 )
    if count != len(M1):
        return close_sock( sock )

    # receive M2_server
    expected = 32
    M2 = receive( sock, expected )
    if len(M2) != expected:
        return close_sock( sock )
    varprint( M2, 'M2' )

    # all done with the connection
    close_sock( sock )

    # doesn't match what we computed? FAILURE
    if M2 != calc_M2( A_bytes, M1, K_client ):
        return None
    else:
        print( "Client: Protocol successful." )
        return ( a, K_client )  # both are ints

    ### END

def server_protocol( sock, N, g, database ):
    """Handle the server's side of the consensus protocal. 
       IMPORTANT: reading the initial 'p' has been handled for 
       you.

    PARAMETERS
    ==========
    sock: A socket object that contains the client connection.
    N: A safe prime. Could be an integer or bytes object.
    g: A primitive root of the safe prime. Could be an integer or bytes object.
    database: A dictionary of all registered users. The keys are usernames
       (as strings!), and the values are tuples of the form (s, v), where s
       is the salt (16 bytes) and v is as per the assignment (integer).

    RETURNS
    =======
    If successful, return a tuple of the form (username, b, K_server), where both b and 
       K_server are integers while username is a string. If not, return None.
    """

    # delete this comment and insert your code here
    ### BEGIN

    # calculate k before conversions, as it might be more efficient
    varprint( N, 'N', "Server" )
    varprint( g, 'g', "Server" )

    k = calc_u( N, g )      # same thing as u! 
    varprint( k, 'k', "Server" )

    N, g = map( b2i, [N, g] )

    # get username
    data = receive( sock, 1 )
    if len(data) != 1:
        return close_sock( sock )
    count = bytes_to_int( data )
    varprint( count, 'username_length', "Server" )

    u_enc = receive( sock, count )
    if len(u_enc) != count:
        return close_sock( sock )
    varprint( u_enc, 'u_enc', "Server" )

    try:
        username = u_enc.decode('utf-8')
    except:
        return close_sock( sock )

    varprint( username, 'username', "Server" )

    # retrieve s, v, if possible
    if username in database:
        s, v = database[username]
    else:
        return close_sock( sock )

    # get A
    A_bytes = receive( sock, 64 )
    if len(A_bytes) != 64:
        return close_sock( sock )
    A = bytes_to_int( A_bytes )
    varprint( A_bytes, None, "Server" )
    varprint( A, 'A', "Server" )

    # generate b via rejection sampling
    b = randbits( 512 )
    while b >= N:
        b = randbits( 512 )
    varprint( b, 'b', "Server" )

    # calculate B
    B = calc_B( N, g, b, k, v )
    B_bytes = int_to_bytes( B, 64 )
    varprint( B, 'B', "Server" )

    # send s,B
    data = s + B_bytes
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # compute u
    u = calc_u( A_bytes, B_bytes )
    varprint( u, 'u', "Server" )

    # compute K_server
    K_server = calc_K_server( N, A_bytes, b, v, u )
    varprint( K_server, 'K_server', "Server" )

    # compute M1
    M1 = calc_M1( A_bytes, B_bytes, K_server )
    varprint( M1, 'M1', "Server" )

    # receive M1
    M1_client = receive( sock, 32 )
    if len(M1_client) != 32:
        return close_sock( sock )
    varprint( M1_client, 'M1_client', "Server" )

    # check M1
    if M1 != M1_client:
        return close_sock( sock )

    # compute M2
    M2 = calc_M2( A, M1, K_server )
    varprint( M2, 'M2', "Server" )

    # send M2. Defer error checking until after the socket's closed
    count = send( sock, M2 )
    close_sock( sock )
    if count != len(M2):
        return None
    else:
        print( "Server: Protocol successful." )
        return (username, b, K_server)
    ### END


##### MAIN

if __name__ == '__main__':

    # parse the command line args
    cmdline = argparse.ArgumentParser( description="Test out a secure key exchange algorithm." )

    methods = cmdline.add_argument_group( 'ACTIONS', "The three actions this program can do." )

    methods.add_argument( '--client', metavar='IP:port', type=str, \
        help='Perform registration and the protocol on the given IP address and port.' )
    methods.add_argument( '--server', metavar='IP:port', type=str, \
        help='Launch the server on the given IP address and port.' )
    methods.add_argument( '--quit', metavar='IP:port', type=str, \
        help='Tell the server on the given IP address and port to quit.' )

    methods = cmdline.add_argument_group( 'OPTIONS', "Modify the defaults used for the above actions." )

    methods.add_argument( '--username', metavar='NAME', type=str, default="admin", \
        help='The username the client sends to the server.' )
    methods.add_argument( '--password', metavar='PASSWORD', type=str, default="swordfish", \
        help='The password the client sends to the server.' )
    methods.add_argument( '--salt', metavar='FILE', type=argparse.FileType('rb', 0), \
        help='A specific salt for the client to use, stored as a file. Randomly generated if not given.' )
    methods.add_argument( '--timeout', metavar='SECONDS', type=int, default=600, \
        help='How long until the program automatically quits. Negative or zero disables this.' )
    methods.add_argument( '-v', '--verbose', action='store_true', \
        help="Be more verbose about what is happening." )

    args = cmdline.parse_args()

    # handle the salt
    if args.salt:
        salt = args.salt.read( 16 )
    else:
        salt = client_prepare()

    if args.verbose:
        print( f"Program: Using salt <{salt.hex()}>" )
    
    # first off, do we have a timeout?
    killer = None           # save this for later
    if args.timeout > 0:

        # define a handler
        def shutdown( time, verbose=False ):

            sleep( time )
            if verbose:
                print( "Program: exiting after timeout.", flush=True )

            return # optional, but I like having an explicit return

        # launch it
        if args.verbose:
            print( "Program: Launching background timeout.", flush=True )
        killer = Process( target=shutdown, args=(args.timeout,args.verbose) )
        killer.daemon = True
        killer.start()

    # next off, are we launching the server?
    result      = None     # pre-declare this to allow for cascading

    server_proc = None
    if args.server:
        if args.verbose:
            print( "Program: Attempting to launch server.", flush=True )
        result = split_ip_port( args.server )

    if result is not None:

        IP, port = result
        if args.verbose:
            print( f"Server: Asked to start on IP {IP} and port {port}.", flush=True )
            print( f"Server: Generating N and g, this will take some time.", flush=True )
        N, g, k = server_prepare() 
        if args.verbose:
            print( f"Server: Finished generating N and g.", flush=True )

        # use an inline routine as this doesn't have to be globally visible
        def server_loop( IP, port, N, g, k, verbose=False ):
            
            database = dict()           # for tracking registered users

            sock = create_socket( IP, port, listen=True )
            if sock is None:
                if verbose:
                    print( f"Server: Could not create socket, exiting.", flush=True )
                return

            if verbose:
                print( f"Server: Beginning connection loop.", flush=True )
            while True:

                (client, client_address) = sock.accept()
                if verbose:
                    print( f"Server: Got connection from {client_address}.", flush=True )

                mode = receive( client, 1 )
                if len(mode) != 1:
                    if verbose:
                        print( f"Server: Socket error with client, closing it and waiting for another connection.", flush=True )
                    client.shutdown(socket.SHUT_RDWR)
                    client.close()
                    continue

                if mode == b'q':
                    if verbose:
                        print( f"Server: Asked to quit by client. Shutting down.", flush=True )
                    client.shutdown(socket.SHUT_RDWR)
                    client.close()
                    sock.shutdown(socket.SHUT_RDWR)
                    sock.close()
                    return

                elif mode == b'r':
                    if verbose:
                        print( f"Server: Asked to register by client.", flush=True )

                    temp = server_register( client, N, g, database )
                    if (temp is None) and verbose:
                            print( f"Server: Registration failed, closing socket and waiting for another connection.", flush=True )
                    elif temp is not None:
                        if verbose:
                            print( f"Server: Registration complete, current users: {[x for x in temp]}.", flush=True )
                        database = temp

                elif mode == b'p':
                    if verbose:
                        print( f"Server: Asked to generate shared secret by client.", flush=True )

                    temp = server_protocol( client, N, g, database )
                    if (temp is None) and verbose:
                            print( f"Server: Protocol failed, closing socket and waiting for another connection.", flush=True )
                    elif type(temp) == tuple:
                        if verbose:
                            print( f"Server: Protocol complete, negotiated shared key for {temp[0]}.", flush=True )
                            print( f"Server:  Shared key is {temp[2]}.", flush=True )

                # clean up is done inside the functions
                # loop back

        # launch the server
        if args.verbose:
            print( "Program: Launching server.", flush=True )
        server_proc = Process( target=server_loop, args=(IP, port, N, g, k, args.verbose) )
        server_proc.daemon = True
        server_proc.start()

    # finally, check if we're launching the client
    result      = None     # clean this up

    client_proc = None
    if args.client:
        if args.verbose:
            print( "Program: Attempting to launch client.", flush=True )
        result = split_ip_port( args.client )

    if result is not None:

        IP, port = result
        if args.verbose:
            print( f"Client: Asked to connect to IP {IP} and port {port}.", flush=True )
        # another inline routine
        def client_routine( IP, port, username, pw, s, verbose=False ):

            if verbose:
                print( f"Client: Beginning registration.", flush=True )

            results = client_register( IP, port, username, pw, s )
            if results is None:
                if verbose:
                    print( f"Client: Registration failed, not attempting the protocol.", flush=True )
                return
            else:
                N, g, v = results
                if verbose:
                    print( f"Client: Registration successful, g = {g}.", flush=True )

            if verbose:
                print( f"Client: Beginning the shared-key protocol.", flush=True )

            results = client_protocol( IP, port, N, g, username, pw, s )
            if results is None:
                if verbose:
                    print( f"Client: Protocol failed.", flush=True )
            else:
                a, K_client = results
                if verbose:
                    print( f"Client: Protocol successful.", flush=True )
                    print( f"Client:  K_client = {K_client}.", flush=True )

            return

        # launch the client
        if args.verbose:
            print( "Program: Launching client.", flush=True )
        client_proc = Process( target=client_routine, args=(IP, port, args.username, args.password, salt, args.verbose) )
        client_proc.daemon = True
        client_proc.start()

    # finally, the quitting routine
    result      = None     # clean this up

    if args.quit:
        # defer on the killing portion, in case the client is active
        result = split_ip_port( args.quit )

    if result is not None:

        IP, port = result
        if args.verbose:
            print( f"Quit: Asked to connect to IP {IP} and port {port}.", flush=True )
        if client_proc is not None:
            if args.verbose:
                print( f"Quit: Waiting for the client to complete first.", flush=True )
            client_proc.join()

        if args.verbose:
            print( "Quit: Attempting to kill the server.", flush=True )

        # no need for multiprocessing here
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

            sock.shutdown(socket.SHUT_RDWR)
            sock.close()

    # finally, we wait until we're told to kill ourselves off, or both the client and server are done
    while not ((server_proc is None) and (client_proc is None)):

        if not killer.is_alive():
            if args.verbose:
                print( f"Program: Timeout reached, so exiting.", flush=True )
            if client_proc is not None:
                client_proc.terminate()
            if server_proc is not None:
                server_proc.terminate()
            exit()

        if (client_proc is not None) and (not client_proc.is_alive()):
            if args.verbose:
                print( f"Program: Client terminated.", flush=True )
            client_proc = None
        
        if (server_proc is not None) and (not server_proc.is_alive()):
            if args.verbose:
                print( f"Program: Server terminated.", flush=True )
            server_proc = None

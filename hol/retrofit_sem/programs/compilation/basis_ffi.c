/*
  This is a slight modification of basis/basis_ffi.c from the CakeML Github
  repository, adding communication over raw sockets. Pending contribution,
  this is temporarily located in the HOL4P4 repository under the original
  license:
  
  BSD 3-Clause License

  Copyright (c) 2025, Anthony Fox, Google LLC, Ramana Kumar, Magnus Myreen, Michael Norrish, Scott Owens, Yong Kiam Tan, and other contributors listed at https://cakeml.org

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are met:

  1. Redistributions of source code must retain the above copyright notice, this
     list of conditions and the following disclaimer.

  2. Redistributions in binary form must reproduce the above copyright notice,
     this list of conditions and the following disclaimer in the documentation
     and/or other materials provided with the distribution.

  3. Neither the name of the copyright holder nor the names of its
     contributors may be used to endorse or promote products derived from
     this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
  DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  
*/ 

/*
  Implements the foreign function interface (FFI) used in the CakeML basis
  library, as a thin wrapper around the relevant system calls.
*/
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#ifdef EVAL
#include <signal.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/time.h>
#endif

/* Added for Unix Domain Socket functionality */
#include <sys/socket.h>
#include <sys/un.h>

/* Added for raw socket functionality */
#include <linux/if_packet.h>
#include <net/ethernet.h>
#include <net/if.h>
#include <sys/ioctl.h>
#include <arpa/inet.h>
#include <poll.h>

/* This flag is on by default. It catches CakeML's out-of-memory exit codes
 * and prints a helpful message to stderr.
 * Note that this is not specified by the basis library.
 * */
#define STDERR_MEM_EXHAUST

/* clFFI (command line) */

unsigned int argc;
char **argv;

/* exported in cake.S */
extern void cml_main(void);
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

extern char cake_text_begin;
extern char cake_codebuffer_begin;
extern char cake_codebuffer_end;

#ifdef EVAL

/* Signal handler for SIGINT */

/* This is set to 1 when the runtime traps a SIGINT */
volatile sig_atomic_t caught_sigint = 0;

void do_sigint(int sig_num)
{
    signal(SIGINT, do_sigint);
    caught_sigint = 1;
}

void ffipoll_sigint (unsigned char *c, long clen, unsigned char *a, long alen)
{
    if (alen < 1) {
        return;
    }
    a[0] = (unsigned char) caught_sigint;
    caught_sigint = 0;
}

void ffikernel_ffi (unsigned char *c, long clen, unsigned char *a, long alen) {
    for (long i = 0; i < clen; i++) {
        putc(c[i], stdout);
    }
}

#else

void ffipoll_sigint (unsigned char *c, long clen, unsigned char *a, long alen) { }

void ffikernel_ffi (unsigned char *c, long clen, unsigned char *a, long alen) { }

#endif

void ffiget_arg_count (unsigned char *c, long clen, unsigned char *a, long alen) {
  /* gives result in big-endian order */
  a[0] = (char) argc;
  a[1] = (char) (argc / 256);
}

void ffiget_arg_length (unsigned char *c, long clen, unsigned char *a, long alen) {
  /* assumes big-endian order, gives result in big-endian order */
  int i = a[0] + (a[1] * 256);
  int k = 0;
  while (argv[i][k] != 0) { k++; }
  a[0] = (char) k;
  a[1] = (char) (k / 256);
}

void ffiget_arg (unsigned char *c, long clen, unsigned char *a, long alen) {
  int i = a[0] + (a[1] * 256);
  int k = 0;
  while (argv[i][k] != 0) {
    a[k] = argv[i][k];
    k++;
  }
}

void int_to_byte2(int i, unsigned char *b){
    /* i is encoded on 2 bytes in big-endian order */
    b[0] = (i >> 8) & 0xFF;
    b[1] = i & 0xFF;
}

int byte2_to_int(unsigned char *b){
    /* this assumes bytes in big-endian order */
    return ((b[0] << 8) | b[1]);
}

void int_to_byte8(int i, unsigned char *b){
    /* i is encoded on 8 bytes in big-endian order */
    /* i is cast to long long to ensure having 64 bits */
    /* assumes CHAR_BIT = 8. use static assertion checks? */
    b[0] = ((long long) i >> 56) & 0xFF;
    b[1] = ((long long) i >> 48) & 0xFF;
    b[2] = ((long long) i >> 40) & 0xFF;
    b[3] = ((long long) i >> 32) & 0xFF;
    b[4] = ((long long) i >> 24) & 0xFF;
    b[5] = ((long long) i >> 16) & 0xFF;
    b[6] = ((long long) i >> 8) & 0xFF;
    b[7] =  (long long) i & 0xFF;
}

int byte8_to_int(unsigned char *b){
    /* this assumes bytes in big-endian order */
    return (((long long) b[0] << 56) | ((long long) b[1] << 48) |
             ((long long) b[2] << 40) | ((long long) b[3] << 32) |
             (b[4] << 24) | (b[5] << 16) | (b[6] << 8) | b[7]);
}


/* fsFFI (file system and I/O) */

void ffiopen_in (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(9 <= alen);
  int fd = open((const char *) c, O_RDONLY);
  if (0 <= fd){
    a[0] = 0;
    int_to_byte8(fd, &a[1]);
  }
  else
    a[0] = 1;
}

void ffiopen_out (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(9 <= alen);
  #ifdef EVAL
  int fd = open((const char *) c, O_RDWR|O_CREAT|O_TRUNC, S_IRUSR|S_IWUSR|S_IRGRP|S_IROTH);
  #else
  int fd = open((const char *) c, O_RDWR|O_CREAT|O_TRUNC, S_IRUSR|S_IWUSR|S_IRGRP|S_IROTH);
  #endif
  if (0 <= fd){
    a[0] = 0;
    int_to_byte8(fd, &a[1]);
  }
  else
    a[0] = 1;
}

void ffiread (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(clen == 8);
  int fd = byte8_to_int(c);
  int n = byte2_to_int(a);
  assert(alen >= n + 4);
  int nread = read(fd, &a[4], n);
  if(nread < 0){
    a[0] = 1;
  }
  else{
    a[0] = 0;
    int_to_byte2(nread,&a[1]);
  }
}

void ffiwrite (unsigned char *c, long clen, unsigned char *a, long alen){
  assert(clen == 8);
  int fd = byte8_to_int(c);
  int n = byte2_to_int(a);
  int off = byte2_to_int(&a[2]);
  assert(alen >= n + off + 4);
  int nw = write(fd, &a[4 + off], n);
  if(nw < 0){
      a[0] = 1;
  }
  else{
    a[0] = 0;
    int_to_byte2(nw,&a[1]);
  }
}

void fficlose (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(alen >= 1);
  assert(clen == 8);
  int fd = byte8_to_int(c);
  if (close(fd) == 0) a[0] = 0;
  else a[0] = 1;
}

/* GC FFI */
int inGC = 0;
struct timeval t1,t2,lastT;
long microsecs = 0;
int numGC = 0;
int hasT = 0;
long prevOcc = 0;
long numAllocBytes = 0;

void cml_exit(int arg) {

  #ifdef STDERR_MEM_EXHAUST
  if (arg != 0) {
    fprintf(stderr,"Program exited with nonzero exit code.\n");
  }
  #endif

  #ifdef DEBUG_FFI
  {
    if(arg == 1) {
      fprintf(stderr,"CakeML heap space exhausted.\n");
    }
    else if(arg == 2) {
      fprintf(stderr,"CakeML stack space exhausted.\n");
    }
    fprintf(stderr,"GCNum: %d, GCTime(us): %ld\n",numGC,microsecs);
    fprintf(stderr,"Total allocated heap data: %ld bytes\n",numAllocBytes);
  }
  #endif

  exit(arg);
}

void cml_err(int arg) {
  if (arg == 3) {
    fprintf(stderr,"Memory not ready for entry. You may have not run the init code yet, or be trying to enter during an FFI call.\n");
  }

  cml_exit(arg);
}

void ffiexit (unsigned char *c, long clen, unsigned char *a, long alen) {
  assert(alen == 1);
  exit((int)a[0]);
}


/* empty FFI (assumed to do nothing, but can be used for tracing/logging) */
void ffi (unsigned char *c, long clen, unsigned char *a, long alen) {
  #ifdef DEBUG_FFI
  {
    if (clen == 0)
    {
      if(inGC==1)
      {
        gettimeofday(&t2, NULL);
        microsecs += (t2.tv_usec - t1.tv_usec) + (t2.tv_sec - t1.tv_sec)*1e6;
        numGC++;
        inGC = 0;
        long occ = (long)c; // number of bytes in occupied in heap (all live after standard GC)
        // long len = (long)a;
        // fprintf(stderr,"GC stops  %ld %ld \n",occ,len);
        prevOcc = occ;
      }
      else
      {
        inGC = 1;
        gettimeofday(&t1, NULL);
        long occ = (long)c;
        // long len = (long)a;
        // fprintf(stderr,"GC starts %ld %ld \n",occ,len);
        numAllocBytes += (occ - prevOcc);
      }
    } else {
      int indent = 30;
      for (int i=0; i<clen; i++) {
        putc(c[i],stderr);
        indent--;
      }
      for (int i=0; i<indent; i++) {
        putc(' ',stderr);
      }
      struct timeval nowT;
      gettimeofday(&nowT, NULL);
      if (hasT) {
        long usecs = (nowT.tv_usec - lastT.tv_usec) +
                     (nowT.tv_sec - lastT.tv_sec)*1e6;
        fprintf(stderr," --- %ld milliseconds\n",usecs / (long)1000);
      } else {
        fprintf(stderr,"\n");
      }
      gettimeofday(&lastT, NULL);
      hasT = 1;
    }
  }
  #endif
}

// ---------------------------------------------------------------------------
// Functions on doubles for the Double module
// ---------------------------------------------------------------------------

typedef union {
    double num;
    char bytes[sizeof(double)];
} double_bytes;

typedef union {
    int64_t num;
    char bytes[sizeof(int64_t)];
} int_bytes;

void ffidouble_fromString(char *c, long clen, char *a, long alen) {
    double_bytes d;
    char *endp;
    errno = 0;
    d.num = strtod(c, &endp);
    if (errno == ERANGE || endp && *endp != '\0') {
        a[0] = 1;
    } else {
        a[0] = 0;
        memcpy(&a[1], d.bytes, sizeof d.bytes);
    }
}

void ffidouble_toString(char *c, long clen, char *a, long alen) {
    double_bytes d;
    memcpy(d.bytes, a, sizeof d.bytes);
    snprintf(a, 255, "%.20g", d.num);
}

void ffidouble_fromInt(char *c, long clen, char *a, long alen) {
    double_bytes d;
    int_bytes i;
    memcpy(i.bytes, a, sizeof i.bytes);
    d.num = (double) i.num;
    memcpy(a, d.bytes, sizeof d.bytes);
}

void ffidouble_toInt(char *c, long clen, char *a, long alen) {
    double_bytes d;
    int_bytes i;
    memcpy(d.bytes, a, sizeof d.bytes);
    i.num = (int64_t) d.num;
    memcpy(a, i.bytes, sizeof i.bytes);
}

void ffidouble_pow(char *c, long clen, char *a, long alen) {
    double_bytes x, y;
    memcpy(x.bytes, a, sizeof x.bytes);
    memcpy(y.bytes, &a[8], sizeof y.bytes);
    x.num = pow(x.num, y.num);
    memcpy(a, x.bytes, sizeof x.bytes);
}

void ffidouble_ln(char *c, long clen, char *a, long alen) {
    double_bytes d;
    memcpy(d.bytes, a, sizeof d.bytes);
    d.num = log(d.num);
    memcpy(a, d.bytes, sizeof d.bytes);
}

void ffidouble_exp(char *c, long clen, char *a, long alen) {
    double_bytes d;
    memcpy(d.bytes, a, sizeof d.bytes);
    d.num = exp(d.num);
    memcpy(a, d.bytes, sizeof d.bytes);
}

void ffidouble_floor(char *c, long clen, char *a, long alen) {
    double_bytes d;
    memcpy(d.bytes, a, sizeof d.bytes);
    d.num = floor(d.num);
    memcpy(a, d.bytes, sizeof d.bytes);
}

// ---------------------------------------------------------------------------
// Unix Domain Socket FFI
// ---------------------------------------------------------------------------

/**
 * Creates a Unix Domain Socket listener at the specified socket path.
 * 
 * This function:
 * 1. Creates a socket
 * 2. Binds it to the provided path
 * 3. Sets it to listen mode
 * 4. Returns the socket descriptor in the buffer if successful
 * 
 * Input:
 *   c: Socket path as a null-terminated string
 *   clen: Length of the socket path
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error)
 *   a[1-8]: Socket descriptor (only valid if a[0] == 0)
 */
void ffiunix_socket_listen(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(9 <= alen);  // Need at least 9 bytes for status + socket descriptor
    
    // Socket path
    const char *socket_path = (const char *)c;
    
    // Create socket
    int sock_fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (sock_fd < 0) {
        a[0] = 1;  // Error
        return;
    }
    
    // Set up socket address structure
    struct sockaddr_un addr;
    memset(&addr, 0, sizeof(struct sockaddr_un));
    addr.sun_family = AF_UNIX;
    
    // Check if path is too long
    if (strlen(socket_path) >= sizeof(addr.sun_path)) {
        close(sock_fd);
        a[0] = 1;  // Error
        return;
    }
    
    strncpy(addr.sun_path, socket_path, sizeof(addr.sun_path) - 1);
    
    // Remove socket file if it already exists
    unlink(socket_path);
    
    // Bind socket to address
    if (bind(sock_fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(sock_fd);
        a[0] = 1;  // Error
        return;
    }
    
    // Listen on socket (queue up to 5 connection requests)
    if (listen(sock_fd, 5) < 0) {
        close(sock_fd);
        a[0] = 1;  // Error
        return;
    }
    
    // Success - return the socket descriptor
    a[0] = 0;  // Success
    int_to_byte8(sock_fd, &a[1]);
}

/**
 * Accepts a connection on the Unix Domain Socket.
 * 
 * Input:
 *   c: 8-byte socket descriptor (listener socket)
 *   clen: Should be 8
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error, 2 = would block)
 *   a[1-8]: Connected socket descriptor (only valid if a[0] == 0)
 */
void ffiunix_socket_accept(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(clen == 8);  // Should be 8 bytes for socket descriptor
    assert(9 <= alen);  // Need at least 9 bytes for status + socket descriptor
    
    int sock_fd = byte8_to_int(c);
    
    // Accept a connection
    struct sockaddr_un client_addr;
    socklen_t client_len = sizeof(client_addr);
    int conn_fd = accept(sock_fd, (struct sockaddr *)&client_addr, &client_len);
    
    if (conn_fd < 0) {
        if (errno == EAGAIN || errno == EWOULDBLOCK) {
            a[0] = 2;  // Would block (no connections available)
        } else {
            a[0] = 1;  // Error
        }
        return;
    }
    
    // Success - return the connected socket descriptor
    a[0] = 0;  // Success
    int_to_byte8(conn_fd, &a[1]);
}

/**
 * Reads data from a Unix Domain Socket.
 * 
 * Input:
 *   c: 8-byte socket descriptor
 *   clen: Should be 8
 *   a[0-1]: Maximum number of bytes to read (16-bit integer)
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error, 2 = connection closed)
 *   a[1-2]: Number of bytes read (16-bit integer, only valid if a[0] == 0)
 *   a[4+]: Buffer containing read data
 */
void ffiunix_socket_read(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(clen == 8);  // Should be 8 bytes for socket descriptor
    
    int sock_fd = byte8_to_int(c);
    int max_bytes = byte2_to_int(a);
    
    assert(alen >= max_bytes + 4);  // Need space for status, bytes read, and data
    
    int bytes_read = read(sock_fd, &a[4], max_bytes);
    
    if (bytes_read < 0) {
        a[0] = 1;  // Error
        return;
    } else if (bytes_read == 0) {
        a[0] = 2;  // Connection closed
        return;
    }
    
    // Success
    a[0] = 0;
    int_to_byte2(bytes_read, &a[1]);
}

/**
 * Writes data to a Unix Domain Socket.
 * 
 * Input:
 *   c: 8-byte socket descriptor
 *   clen: Should be 8
 *   a[0-1]: Number of bytes to write (16-bit integer)
 *   a[2-3]: Offset into the buffer (16-bit integer)
 *   a[4+offset]: Buffer containing data to write
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error)
 *   a[1-2]: Number of bytes written (16-bit integer, only valid if a[0] == 0)
 */
void ffiunix_socket_write(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(clen == 8);  // Should be 8 bytes for socket descriptor
    
    int sock_fd = byte8_to_int(c);
    int bytes_to_write = byte2_to_int(a);
    int offset = byte2_to_int(&a[2]);
    
    assert(alen >= bytes_to_write + offset + 4);  // Need space for status, bytes written, and data
    
    int bytes_written = write(sock_fd, &a[4 + offset], bytes_to_write);
    
    if (bytes_written < 0) {
        a[0] = 1;  // Error
        return;
    }
    
    // Success
    a[0] = 0;
    int_to_byte2(bytes_written, &a[1]);
}

// ---------------------------------------------------------------------------
// Raw Socket FFI for network interfaces
// ---------------------------------------------------------------------------

/**
 * Creates a raw socket that can receive and send Ethernet frames.
 * 
 * This function:
 * 1. Creates a raw socket using the AF_PACKET domain
 * 2. Returns the socket descriptor in the buffer if successful
 * 
 * Input:
 *   c: Not used, can be empty
 *   clen: Not used
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error)
 *   a[1-8]: Socket descriptor (only valid if a[0] == 0)
 */
void ffiraw_socket_create(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(9 <= alen);  // Need at least 9 bytes for status + socket descriptor
    
    // Create raw socket for all Ethernet protocols
    int sock_fd = socket(AF_PACKET, SOCK_RAW, htons(ETH_P_ALL));
    
    if (sock_fd < 0) {
        a[0] = 1;  // Error
        return;
    }
    
    // Success - return the socket descriptor
    a[0] = 0;  // Success
    int_to_byte8(sock_fd, &a[1]);
}

/**
 * Gets the interface index for a named network interface.
 * 
 * This function:
 * 1. Takes a socket descriptor and interface name
 * 2. Uses ioctl to get the interface index
 * 3. Returns the interface index in the buffer if successful
 * 
 * Input:
 *   c[0-7]: Socket descriptor (8 bytes)
 *   c[8+]: Interface name (null-terminated string)
 *   clen: Length of c
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error)
 *   a[1-8]: Interface index (only valid if a[0] == 0)
 */
void ffiget_interface_index(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(9 <= alen);  // Need at least 9 bytes for status + interface index
    
    // Extract socket descriptor from c
    int sock_fd = byte8_to_int(c);
    
    // The rest of c contains the interface name (null-terminated)
    const char *interface_name = (const char *)(c + 8);
    
    // Check if interface name is valid
    if (!interface_name || strlen(interface_name) >= IFNAMSIZ) {
        a[0] = 1;  // Error
        return;
    }
    
    // Get interface index
    struct ifreq ifr;
    memset(&ifr, 0, sizeof(ifr));
    strncpy(ifr.ifr_name, interface_name, IFNAMSIZ - 1);
    ifr.ifr_name[IFNAMSIZ - 1] = '\0';
    
    if (ioctl(sock_fd, SIOCGIFINDEX, &ifr) < 0) {
        a[0] = 1;  // Error
        return;
    }
    
    // Success - return the interface index
    a[0] = 0;  // Success
    int_to_byte8(ifr.ifr_ifindex, &a[1]);
}

/**
 * Gets the MTU (Maximum Transmission Unit) for a named network interface.
 * 
 * This function:
 * 1. Takes a socket descriptor and interface name
 * 2. Uses ioctl to get the interface MTU
 * 3. Returns the MTU in the buffer if successful
 * 
 * Input:
 *   c[0-7]: Socket descriptor (8 bytes)
 *   c[8+]: Interface name (null-terminated string)
 *   clen: Length of c
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error)
 *   a[1-8]: MTU value (only valid if a[0] == 0)
 */
void ffiget_interface_mtu(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(9 <= alen);  // Need at least 9 bytes for status + MTU
    
    // Extract socket descriptor from c
    int sock_fd = byte8_to_int(c);
    
    // The rest of c contains the interface name (null-terminated)
    const char *interface_name = (const char *)(c + 8);
    
    // Check if interface name is valid
    if (!interface_name || strlen(interface_name) >= IFNAMSIZ) {
        a[0] = 1;  // Error
        return;
    }
    
    // Get interface MTU
    struct ifreq ifr;
    memset(&ifr, 0, sizeof(ifr));
    strncpy(ifr.ifr_name, interface_name, IFNAMSIZ - 1);
    ifr.ifr_name[IFNAMSIZ - 1] = '\0';
    
    if (ioctl(sock_fd, SIOCGIFMTU, &ifr) < 0) {
        a[0] = 1;  // Error
        return;
    }
    
    // Success - return the MTU
    a[0] = 0;  // Success
    int_to_byte8(ifr.ifr_mtu, &a[1]);
}

/**
 * Binds a raw socket to a specific network interface.
 * 
 * This function:
 * 1. Takes a socket descriptor and interface index
 * 2. Binds the socket to the specified interface
 * 
 * Input:
 *   c[0-7]: Socket descriptor (8 bytes)
 *   c[8-15]: Interface index (8 bytes)
 *   clen: Length of c (should be at least 16)
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error)
 */
void ffiraw_socket_bind(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(1 <= alen);  // Need at least 1 byte for status
    
    // Extract socket descriptor and interface index from c
    if (clen < 16) {
        a[0] = 1;  // Error
        return;
    }
    
    int sock_fd = byte8_to_int(c);
    int if_index = byte8_to_int(c + 8);
    
    // Bind socket to interface
    struct sockaddr_ll addr;
    memset(&addr, 0, sizeof(addr));
    addr.sll_family = AF_PACKET;
    addr.sll_protocol = htons(ETH_P_ALL);
    addr.sll_ifindex = if_index;
    
    if (bind(sock_fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        a[0] = 1;  // Error
        return;
    }
    
    // Success
    a[0] = 0;
}

/**
 * Receives a raw Ethernet frame from a bound socket.
 * 
 * This function:
 * 1. Takes a socket descriptor
 * 2. Receives data from the socket
 * 3. Returns the received data and its length
 * 
 * Input:
 *   c: 8-byte socket descriptor
 *   clen: Should be 8
 *   a[0-1]: Maximum number of bytes to read (16-bit integer)
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error)
 *   a[1-2]: Number of bytes read (16-bit integer, only valid if a[0] == 0)
 *   a[4+]: Buffer containing read data (Ethernet frame)
 */
void ffiraw_socket_recv(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(clen == 8);  // Should be 8 bytes for socket descriptor
    
    int sock_fd = byte8_to_int(c);
    int max_bytes = byte2_to_int(a);
    
    assert(alen >= max_bytes + 4);  // Need space for status, bytes read, and data
    
    int bytes_read = recv(sock_fd, &a[4], max_bytes, 0);
    
    if (bytes_read < 0) {
        a[0] = 1;  // Error
        return;
    }
    
    // Success
    a[0] = 0;
    int_to_byte2(bytes_read, &a[1]);
}

/**
 * Sends a raw Ethernet frame through a socket.
 * 
 * This function:
 * 1. Takes a socket descriptor
 * 2. Sends the provided data through the socket
 * 3. Returns the number of bytes successfully sent
 * 
 * Input:
 *   c: 8-byte socket descriptor
 *   clen: Should be 8
 *   a[0-1]: Number of bytes to write (16-bit integer)
 *   a[2-3]: Offset into the buffer (16-bit integer)
 *   a[4+offset]: Buffer containing data to write (Ethernet frame)
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error)
 *   a[1-2]: Number of bytes written (16-bit integer, only valid if a[0] == 0)
 */
void ffiraw_socket_send(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(clen == 8);  // Should be 8 bytes for socket descriptor
    
    int sock_fd = byte8_to_int(c);
    int bytes_to_write = byte2_to_int(a);
    int offset = byte2_to_int(&a[2]);
    
    assert(alen >= bytes_to_write + offset + 4);  // Need space for status, bytes written, and data
    
    // For raw socket sending, we can use send() or write() function
    int bytes_written = send(sock_fd, &a[4 + offset], bytes_to_write, 0);
    
    if (bytes_written < 0) {
        a[0] = 1;  // Error
        return;
    }
    
    // Success
    a[0] = 0;
    int_to_byte2(bytes_written, &a[1]);
}

/**
 * Sends a raw Ethernet frame to a specific interface.
 * 
 * This function:
 * 1. Takes a socket descriptor and interface index
 * 2. Sends the provided data to the specified interface
 * 3. Returns the number of bytes successfully sent
 * 
 * Input:
 *   c[0-7]: Socket descriptor (8 bytes)
 *   c[8-15]: Interface index (8 bytes)
 *   clen: Length of c (should be at least 16)
 *   a[0-1]: Number of bytes to write (16-bit integer)
 *   a[2-3]: Offset into the buffer (16-bit integer)
 *   a[4+offset]: Buffer containing data to write (Ethernet frame)
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error)
 *   a[1-2]: Number of bytes written (16-bit integer, only valid if a[0] == 0)
 */
void ffiraw_socket_sendto(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(clen >= 16);  // Should be at least 16 bytes for socket descriptor and interface index
    
    int sock_fd = byte8_to_int(c);
    int if_index = byte8_to_int(c + 8);
    int bytes_to_write = byte2_to_int(a);
    int offset = byte2_to_int(&a[2]);
    
    assert(alen >= bytes_to_write + offset + 4);  // Need space for status, bytes written, and data
    
    // Set up sockaddr_ll for sendto
    struct sockaddr_ll addr;
    memset(&addr, 0, sizeof(addr));
    addr.sll_family = AF_PACKET;
    addr.sll_protocol = htons(ETH_P_ALL);
    addr.sll_ifindex = if_index;
    
    // Send the packet
    int bytes_written = sendto(sock_fd, &a[4 + offset], bytes_to_write, 0,
                              (struct sockaddr *)&addr, sizeof(addr));
    
    if (bytes_written < 0) {
        a[0] = 1;  // Error
        return;
    }
    
    // Success
    a[0] = 0;
    int_to_byte2(bytes_written, &a[1]);
}

/**
 * Poll multiple socket file descriptors for events
 * 
 * Input:
 *   c: Buffer containing array of {fd, events} pairs (8 bytes per fd, 2 bytes per events field)
 *      Format: [fd1(8 bytes), events1(2 bytes), fd2(8 bytes), events2(2 bytes), ...]
 *   clen: Length of c 
 *   a[0-3]: Number of file descriptors to poll (4 bytes)
 *   a[4-7]: Timeout in milliseconds (4 bytes, -1 for infinite)
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error, 2 = timeout)
 *   a[1-4]: Number of ready descriptors
 *   a[8+]: Array of revents values (2 bytes per fd, in same order as input)
 */
void ffiraw_socket_poll(unsigned char *c, long clen, unsigned char *a, long alen) {
    // Extract number of fds and timeout (big-endian order assumed)
    int nfds = (a[0] << 24) | (a[1] << 16) | (a[2] << 8) | a[3];
    int timeout = (a[4] << 24) | (a[5] << 16) | (a[6] << 8) | a[7];
    
    // Check that we have enough space for the results
    assert(alen >= 8 + (nfds * 2));
    
    // Allocate pollfd array
    struct pollfd *fds = malloc(nfds * sizeof(struct pollfd));
    if (!fds) {
        a[0] = 1;  // Error
        return;
    }
    
    // Fill in the pollfd array from input buffer
    for (int i = 0; i < nfds; i++) {
        int fd_offset = i * 10;  // 8 bytes for fd + 2 bytes for events
        fds[i].fd = byte8_to_int(c + fd_offset);
        fds[i].events = (c[fd_offset + 8] << 8) | c[fd_offset + 9];
        fds[i].revents = 0;
    }
    
    // Call poll
    int ret = poll(fds, nfds, timeout);
    
    if (ret < 0) {
        // Error
        a[0] = 1;
        free(fds);
        return;
    } else if (ret == 0) {
        // Timeout
        a[0] = 2;
        free(fds);
        return;
    }
    
    // Success - copy revents back to output buffer (big-endian order assumed)
    a[0] = 0;
    a[1] = (ret >> 24) & 0xFF;
    a[2] = (ret >> 16) & 0xFF;
    a[3] = (ret >> 8) & 0xFF;
    a[4] = ret & 0xFF;
    
    for (int i = 0; i < nfds; i++) {
        a[8 + (i * 2)] = (fds[i].revents >> 8) & 0xFF;
        a[8 + (i * 2) + 1] = fds[i].revents & 0xFF;
    }
    
    free(fds);
}

/**
 * Sets socket buffer size (receive or send).
 * 
 * This function:
 * 1. Takes a socket descriptor and buffer size
 * 2. Sets either the receive or send buffer size based on the option
 * 3. Returns success or failure
 * 
 * Input:
 *   c[0-7]: Socket descriptor (8 bytes)
 *   c[8-15]: Buffer size in bytes (8 bytes)
 *   c[16]: Buffer type (0 = receive buffer, 1 = send buffer)
 *   clen: Length of c (should be at least 17)
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error)
 *   a[1-8]: Actual buffer size set (after kernel adjustments) if success
 */
void ffiset_socket_buffer_size(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(clen >= 17);  // Should be at least 17 bytes (8 for fd + 8 for size + 1 for type)
    assert(alen >= 9);   // Need at least 9 bytes for status + actual buffer size
    
    int sock_fd = byte8_to_int(c);
    int buffer_size = byte8_to_int(c + 8);
    int buffer_type = c[16];  // 0 = receive buffer, 1 = send buffer
    
    // Choose the appropriate socket option based on buffer_type
    int option = (buffer_type == 0) ? SO_RCVBUF : SO_SNDBUF;
    
    // Set the socket buffer size
    if (setsockopt(sock_fd, SOL_SOCKET, option, &buffer_size, sizeof(buffer_size)) < 0) {
        a[0] = 1;  // Error
        return;
    }
    
    // Get the actual buffer size that was set (kernel may adjust it)
    int actual_size = 0;
    socklen_t size_len = sizeof(actual_size);
    
    if (getsockopt(sock_fd, SOL_SOCKET, option, &actual_size, &size_len) < 0) {
        a[0] = 1;  // Error
        return;
    }
    
    // Success
    a[0] = 0;
    int_to_byte8(actual_size, &a[1]);
}

/**
 * Closes a raw socket.
 * 
 * This function:
 * 1. Takes a socket descriptor
 * 2. Closes the socket
 * 3. Returns success or failure
 * 
 * Input:
 *   c: 8-byte socket descriptor
 *   clen: Should be 8
 *   
 * Output:
 *   a[0]: Status (0 = success, 1 = error)
 */
void ffiraw_socket_close(unsigned char *c, long clen, unsigned char *a, long alen) {
    assert(clen == 8);  // Should be 8 bytes for socket descriptor
    assert(alen >= 1);  // Need at least 1 byte for status
    
    int sock_fd = byte8_to_int(c);
    
    // Close the socket
    if (close(sock_fd) < 0) {
        a[0] = 1;  // Error
    } else {
        a[0] = 0;  // Success
    }
}

void cml_clear() {
  __builtin___clear_cache(&cake_codebuffer_begin, &cake_codebuffer_end);
}

int main (int local_argc, char **local_argv) {

  argc = local_argc;
  argv = local_argv;

  char *heap_env = getenv("CML_HEAP_SIZE");
  char *stack_env = getenv("CML_STACK_SIZE");
  char *temp; //used to store remainder of strtoul parse

  unsigned long sz = 1024*1024; // 1 MB unit
  unsigned long cml_heap_sz = 1024 * sz;    // Default: 1 GB heap
  unsigned long cml_stack_sz = 1024 * sz;   // Default: 1 GB stack

  // Read CML_HEAP_SIZE env variable (if present)
  // Warning: strtoul may overflow!
  if(heap_env != NULL)
  {
    cml_heap_sz = strtoul(heap_env, &temp, 10);
    cml_heap_sz *= sz; //heap size is read in units of MBs
  }

  if(stack_env != NULL)
  {
    cml_stack_sz = strtoul(stack_env, &temp, 10);
    cml_stack_sz *= sz; //stack size is read in units of MBs
  }

  if(cml_heap_sz < sz || cml_stack_sz < sz) //At least 1MB heap and stack size
  {
    #ifdef STDERR_MEM_EXHAUST
    fprintf(stderr,"Too small requested heap (%lu) or stack (%lu) size in bytes.\n",cml_heap_sz, cml_stack_sz);
    #endif
    exit(3);
  }

  if(cml_heap_sz + cml_stack_sz < 8192) // Global minimum heap/stack for CakeML. 4096 for 32-bit architectures
  {
    #ifdef STDERR_MEM_EXHAUST
    fprintf(stderr,"Too small requested heap (%lu) + stack (%lu) size in bytes.\n",cml_heap_sz, cml_stack_sz);
    #endif
    exit(3);
  }

  /**
   *  CakeML and its default assembly wrapper expects the following memory layout:
   *
   *  cml_heap      cml_stack      cml_stackend
   *  |             |              |
   *  V             v              v
   *  |--- heap ---||--- stack ---|
   *
   *  The heap/stack are assumed to be in contiguous memory,
   *  cml_heap points to the first address of the heap,
   *  cml_stack points to 1 address past the end of the heap (i.e., the first address of the stack),
   *  cml_stackend points to 1 address past the end of the stack.
   *
   *  All cml_* pointers must be word aligned.
   *  The position cml_stack may be (slightly) dynamically adjusted by CakeML,
   *  see `get_stack_heap_limit` in stack_removeProof
   **/

  cml_heap = malloc(cml_heap_sz + cml_stack_sz); // allocate both heap and stack at once

  if(cml_heap == NULL)
  {
    #ifdef STDERR_MEM_EXHAUST
    fprintf(stderr,"failed to allocate sufficient CakeML heap and stack space.\n");
    perror("malloc");
    #endif
    exit(3);
  }

  cml_stack = cml_heap + cml_heap_sz;
  cml_stackend = cml_stack + cml_stack_sz;

  #ifdef EVAL

  /** Set up the "eval" code buffer to be read-write-execute. **/
  if(mprotect(&cake_text_begin, &cake_codebuffer_end - &cake_text_begin,
              PROT_READ | PROT_WRITE | PROT_EXEC))
  {
    #ifdef STDERR_MEM_EXHAUST
    fprintf(stderr,"failed to set permissions for CakeML code buffer.\n");
    perror("mprotect");
    #endif
    exit(3);
  }

  /* Set up the signal handler for SIGINTs when running the REPL. */
  for (int i = 0; i < local_argc; i++) {
      if (strcmp(local_argv[i], "--repl") == 0 ||
          strcmp(local_argv[i], "--candle") == 0) {
        signal(SIGINT, do_sigint);
        break;
      }
  }

  #endif

  cml_main(); // Passing control to CakeML

  return 0;
}

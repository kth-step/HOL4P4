/**
 *
 * Copyright 2016 The P4 Language Consortium
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */
// The original version of this file, from the official P4 specification covered by the copyright and license listed above, has been adapted to the V1Model architecture.

#include <core.p4>
#include <v1model.p4>

// This program processes packets comprising an Ethernet and an IPv4
// header, and it forwards packets using the destination IP address

// This version should be the same as the regular program, but with hard-coded table entries

typedef bit<48>  EthernetAddress;
typedef bit<32>  IPv4Address;

// Standard Ethernet header
header Ethernet_h {
    EthernetAddress dstAddr;
    EthernetAddress srcAddr;
    bit<16>         etherType;
}

// IPv4 header (without options)
header IPv4_h {
    bit<4>       version;
    bit<4>       ihl;
    bit<8>       diffserv;
    bit<16>      totalLen;
    bit<16>      identification;
    bit<3>       flags;
    bit<13>      fragOffset;
    bit<8>       ttl;
    bit<8>       protocol;
    bit<16>      hdrChecksum;
    IPv4Address  srcAddr;
    IPv4Address  dstAddr;
}

// Structure of parsed headers
struct Parsed_packet {
    Ethernet_h ethernet;
    IPv4_h     ip;
}

struct Meta_t {}

// Parser section

// User-defined errors that may be signaled during parsing
error {
    IPv4OptionsNotSupported,
    IPv4IncorrectVersion,
    IPv4ChecksumError
}

// Standard for V1Model
const bit<9> DROP_PORT = 0x1FF;
// Chosen arbitrarily (0 is default, but invalid)
const bit<9> CPU_OUT_PORT = 0x1FE;

parser TopParser(packet_in b,
                 out Parsed_packet p,
                 inout Meta_t meta,
                 inout standard_metadata_t standard_metadata) {

    state start {
        b.extract(p.ethernet);
        transition select(p.ethernet.etherType) {
            0x0800: parse_ipv4;
            // no default rule: all other packets rejected
        }
    }

    state parse_ipv4 {
        b.extract(p.ip);
        verify(p.ip.version == 4w4, error.IPv4IncorrectVersion);
        verify(p.ip.ihl == 4w5, error.IPv4OptionsNotSupported);
        transition accept;
    }
}

control TopVerifyChecksum(inout Parsed_packet headers,
                inout Meta_t meta) {
    apply {
        verify_checksum(true, {headers.ip.version, headers.ip.ihl, headers.ip.diffserv, headers.ip.totalLen, headers.ip.identification, headers.ip.flags, headers.ip.fragOffset, headers.ip.ttl, headers.ip.protocol, headers.ip.srcAddr, headers.ip.dstAddr}, headers.ip.hdrChecksum, HashAlgorithm.csum16);
    }
}

control TopPipe(inout Parsed_packet headers,
                inout Meta_t meta,
                inout standard_metadata_t standard_metadata) {
    apply { }
}

// Match-action pipeline section

control TopIngress(inout Parsed_packet headers,
                inout Meta_t meta,
                inout standard_metadata_t standard_metadata) {
     IPv4Address nextHop;  // local variable

     /**
      * Indicates that a packet is dropped by setting the
      * output port to the DROP_PORT
      */
      action Drop_action() {
          standard_metadata.egress_spec = DROP_PORT;
      }

     /**
      * Set the next hop and the output port.
      * Decrements ipv4 ttl field.
      * @param ipv4_dest ipv4 address of next hop
      * @param port output port
      */
      action Set_nhop(IPv4Address ipv4_dest, bit<9> port) {
          nextHop = ipv4_dest;
          headers.ip.ttl = headers.ip.ttl - 1;
          standard_metadata.egress_spec = port;
      }

     /**
      * Computes address of next IPv4 hop and output port
      * based on the IPv4 destination of the current packet.
      * Decrements packet IPv4 TTL.
      * @param nextHop IPv4 address of next hop
      */
     table ipv4_match {
         key = { headers.ip.dstAddr: lpm; }  // longest-prefix match
         actions = {
              Drop_action;
              Set_nhop;
         }
 //        size = 1024;
         default_action = Drop_action;
         const entries = {
            0x0a000002 &&& 0xFFFFFFFF : Set_nhop(0x0a000002,2);
            0x0a000001 &&& 0xFFFFFFFF : Set_nhop(0x0a000001,1);
            _                         : Drop_action;
        }
     }

     /**
      * Send the packet to the CPU port
      */
      action Send_to_cpu() {
          standard_metadata.egress_spec = CPU_OUT_PORT;
      }

     /**
      * Check packet TTL and send to CPU if expired.
      */
     table check_ttl {
         key = { headers.ip.ttl: exact; }
         actions = { Send_to_cpu; NoAction; }
         const default_action = NoAction; // defined in core.p4
     }

     /**
      * Set the destination MAC address of the packet
      * @param dmac destination MAC address.
      */
      action Set_dmac(EthernetAddress dmac) {
          headers.ethernet.dstAddr = dmac;
      }

     /**
      * Set the destination Ethernet address of the packet
      * based on the next hop IP address.
      * @param nextHop IPv4 address of next hop.
      */
      table dmac {
          key = { nextHop: exact; }
          actions = {
               Drop_action;
               Set_dmac;
          }
 //         size = 1024;
          default_action = Drop_action;
          const entries = {
            0x0a000002 : Set_dmac(0x021122334402);
            0x0a000001 : Set_dmac(0x021122334401);
            _                         : Drop_action;
          }
      }

      /**
       * Set the source MAC address.
       * @param smac: source MAC address to use
       */
       action Set_smac(EthernetAddress smac) {
           headers.ethernet.srcAddr = smac;
       }

      /**
       * Set the source mac address based on the output port.
       */
      table smac {
           key = { standard_metadata.egress_spec: exact; }
           actions = {
                Drop_action;
                Set_smac;
          }
//          size = 16;
          default_action = Drop_action;
          const entries = {
            0x02 : Set_smac(0x021122334404);
            0x01 : Set_smac(0x021122334403);
            _                         : Drop_action;
          }
      }

      apply {
/*
    	if (standard_metadata.ingress_port == 1)
    		standard_metadata.egress_spec = 2;
        else
        	standard_metadata.egress_spec = 1;
*/
          if (standard_metadata.parser_error != error.NoError || standard_metadata.checksum_error == 1w1) {
              Drop_action();  // invoke drop directly
              return;
          }

          ipv4_match.apply(); // Match result will go into nextHop
          if (standard_metadata.egress_spec == DROP_PORT) return;

          check_ttl.apply();
          if (standard_metadata.egress_spec == CPU_OUT_PORT) return;

          dmac.apply();
          if (standard_metadata.egress_spec == DROP_PORT) return;

          smac.apply();

    }
}

control TopComputeChecksum(inout Parsed_packet p, inout Meta_t meta) {
    apply {
        //if (p.ip.isValid()) {
            update_checksum(true, {p.ip.version, p.ip.ihl, p.ip.diffserv, p.ip.totalLen, p.ip.identification, p.ip.flags, p.ip.fragOffset, p.ip.ttl, p.ip.protocol, p.ip.srcAddr, p.ip.dstAddr}, p.ip.hdrChecksum, HashAlgorithm.csum16);
        //}
    }
}

control TopDeparser(packet_out b, in Parsed_packet p) {
    apply {
        b.emit(p.ethernet);
        b.emit(p.ip);
    }
}

V1Switch(TopParser(),
    TopVerifyChecksum(),
    TopIngress(),
    TopPipe(),
    TopComputeChecksum(),
    TopDeparser()) main;

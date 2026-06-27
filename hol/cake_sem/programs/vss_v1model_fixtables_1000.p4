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
            0x32105152 : Drop_action;
            0x31A052A4 : Drop_action;
            0x66C18732 : Drop_action;
            0x16C9DA9E : Drop_action;
            0xB32CB554 : Drop_action;
            0xA9CF1866 : Drop_action;
            0xB8157E55 : Drop_action;
            0xDE191037 : Drop_action;
            0xCE24B444 : Drop_action;
            0x48359493 : Drop_action;
            0xB8033D14 : Drop_action;
            0x2BB8AC57 : Drop_action;
            0xBB02A1B1 : Drop_action;
            0xC275DBE9 : Drop_action;
            0x1BB35578 : Drop_action;
            0xA7068836 : Drop_action;
            0x1C5E2BF7 : Drop_action;
            0x65EFA0A2 : Drop_action;
            0xFCBC13F7 : Drop_action;
            0x4241E9DC : Drop_action;
            0x61244A5A : Drop_action;
            0x23C2FDFD : Drop_action;
            0x5437AB6A : Drop_action;
            0x2B4295B0 : Drop_action;
            0x088D0C7A : Drop_action;
            0x54A2EDCE : Drop_action;
            0xF7845100 : Drop_action;
            0xFB8EC75F : Drop_action;
            0x3236408E : Drop_action;
            0x7F1142AB : Drop_action;
            0x991A9C13 : Drop_action;
            0xBC195014 : Drop_action;
            0x77D4AA14 : Drop_action;
            0xEB1E34D8 : Drop_action;
            0x6BC54DBD : Drop_action;
            0xAEF064B6 : Drop_action;
            0xB56A6202 : Drop_action;
            0xBA02E040 : Drop_action;
            0x4D2F280D : Drop_action;
            0x92050D86 : Drop_action;
            0x10B5958B : Drop_action;
            0x0D440A0A : Drop_action;
            0xAB31DD0E : Drop_action;
            0x8D259789 : Drop_action;
            0x4F8DDDBB : Drop_action;
            0x9D070461 : Drop_action;
            0x7E6A3D96 : Drop_action;
            0xA68A81A3 : Drop_action;
            0xAFECBE8E : Drop_action;
            0xEA6C43A9 : Drop_action;
            0x5331514F : Drop_action;
            0xE717823B : Drop_action;
            0xB81E24A7 : Drop_action;
            0x6A0DE954 : Drop_action;
            0xA5738039 : Drop_action;
            0x47BFE5B3 : Drop_action;
            0x97D59D92 : Drop_action;
            0x46E44EA7 : Drop_action;
            0x59B10A01 : Drop_action;
            0x061D36C8 : Drop_action;
            0x9C57851A : Drop_action;
            0x313C3434 : Drop_action;
            0xE0A7386A : Drop_action;
            0xE18FD507 : Drop_action;
            0x6A62839E : Drop_action;
            0x06ECDC16 : Drop_action;
            0xC2149138 : Drop_action;
            0x9551B758 : Drop_action;
            0x655D08E7 : Drop_action;
            0x4F5C974A : Drop_action;
            0x9B34BA39 : Drop_action;
            0x0CFCADF8 : Drop_action;
            0x453D55D0 : Drop_action;
            0xA4515939 : Drop_action;
            0xD4E6E345 : Drop_action;
            0x336D6916 : Drop_action;
            0xE83DF614 : Drop_action;
            0x1CD674A7 : Drop_action;
            0x602CF431 : Drop_action;
            0xEF51E22D : Drop_action;
            0xC82B7C08 : Drop_action;
            0x717EB5F8 : Drop_action;
            0x75747965 : Drop_action;
            0x8E4F30F2 : Drop_action;
            0x0F3D25E1 : Drop_action;
            0x795E7C35 : Drop_action;
            0x29983151 : Drop_action;
            0x0EF59D5C : Drop_action;
            0x6F23C79C : Drop_action;
            0x49BAC17A : Drop_action;
            0xC3827787 : Drop_action;
            0xC030C6AF : Drop_action;
            0x52EE8747 : Drop_action;
            0x8A84ED1C : Drop_action;
            0xE7E0EC3D : Drop_action;
            0x948E56C5 : Drop_action;
            0xE42DFA0A : Drop_action;
            0x46F3CAB3 : Drop_action;
            0xCDA504B0 : Drop_action;
            0xFE2D6873 : Drop_action;
            0x9773DF30 : Drop_action;
            0x37F24E53 : Drop_action;
            0x8AB2A832 : Drop_action;
            0x6244B047 : Drop_action;
            0xFC5AE7B4 : Drop_action;
            0x30528DBF : Drop_action;
            0x20921E10 : Drop_action;
            0x2F05389E : Drop_action;
            0xA1826AED : Drop_action;
            0xE3BCAC3E : Drop_action;
            0xA8F0563B : Drop_action;
            0xACDF6811 : Drop_action;
            0x0525638A : Drop_action;
            0xB431A7E4 : Drop_action;
            0x591F3023 : Drop_action;
            0xBF3D818B : Drop_action;
            0x8586DDC9 : Drop_action;
            0x7C091DA8 : Drop_action;
            0x11389A18 : Drop_action;
            0x0C1D12DF : Drop_action;
            0xC929CE72 : Drop_action;
            0xFDF189C1 : Drop_action;
            0x29D26C91 : Drop_action;
            0x6277C65E : Drop_action;
            0x8A367986 : Drop_action;
            0xB2326607 : Drop_action;
            0xF9570D09 : Drop_action;
            0x82277247 : Drop_action;
            0x3A79FC2C : Drop_action;
            0x799CC084 : Drop_action;
            0x6681459D : Drop_action;
            0x5CFC8DE1 : Drop_action;
            0xD53E67A7 : Drop_action;
            0x78B9F9BF : Drop_action;
            0x7C2E8033 : Drop_action;
            0xF72B94D4 : Drop_action;
            0x861ECB2E : Drop_action;
            0x52F6934C : Drop_action;
            0x5438D95A : Drop_action;
            0x302E2036 : Drop_action;
            0x6C80A6D9 : Drop_action;
            0x8D5A967F : Drop_action;
            0x7753943B : Drop_action;
            0x3C1513A1 : Drop_action;
            0x2BD96C01 : Drop_action;
            0x065BE579 : Drop_action;
            0x5F502ED2 : Drop_action;
            0x598960AC : Drop_action;
            0xC78A8ECA : Drop_action;
            0x1D7602B5 : Drop_action;
            0xFBB26EAD : Drop_action;
            0x4DD0982B : Drop_action;
            0xB3F1CD52 : Drop_action;
            0x7F8CE9E8 : Drop_action;
            0x22101216 : Drop_action;
            0xD1C89699 : Drop_action;
            0x27A42F81 : Drop_action;
            0xDE693766 : Drop_action;
            0xA6D574A2 : Drop_action;
            0x18847C78 : Drop_action;
            0x67EA73F8 : Drop_action;
            0x80900649 : Drop_action;
            0xFAB24CE5 : Drop_action;
            0x45477620 : Drop_action;
            0xC5C12181 : Drop_action;
            0x4430AD34 : Drop_action;
            0xA79F630B : Drop_action;
            0xF7416D84 : Drop_action;
            0xF7A67A25 : Drop_action;
            0xEEF8C529 : Drop_action;
            0xB2489FED : Drop_action;
            0xAB059EE4 : Drop_action;
            0x6CF6990D : Drop_action;
            0xA072EEE7 : Drop_action;
            0x7513345E : Drop_action;
            0x87B803B1 : Drop_action;
            0x345E1BC8 : Drop_action;
            0x27ABA096 : Drop_action;
            0x876F21A6 : Drop_action;
            0x5D7EE4D1 : Drop_action;
            0x3389FD52 : Drop_action;
            0xD614914E : Drop_action;
            0x1897C8DF : Drop_action;
            0x7B1BDA8E : Drop_action;
            0xC3E03C7F : Drop_action;
            0x67EDE1B2 : Drop_action;
            0xAF2D53F8 : Drop_action;
            0xA9ED340F : Drop_action;
            0x785A7E44 : Drop_action;
            0x0FED17C4 : Drop_action;
            0x9D921868 : Drop_action;
            0x1715D048 : Drop_action;
            0x7873B7A4 : Drop_action;
            0x4B5F9CEB : Drop_action;
            0x2836357B : Drop_action;
            0xC89E5617 : Drop_action;
            0x69EB43EB : Drop_action;
            0x4CA8A7E7 : Drop_action;
            0x45948108 : Drop_action;
            0x5082DE74 : Drop_action;
            0x585861D1 : Drop_action;
            0x6CC3AE35 : Drop_action;
            0x13E1A995 : Drop_action;
            0xF785498D : Drop_action;
            0x933B470A : Drop_action;
            0x0D268115 : Drop_action;
            0x614E3976 : Drop_action;
            0xE7FA0364 : Drop_action;
            0xA73F94D5 : Drop_action;
            0xBE141430 : Drop_action;
            0x81B87B27 : Drop_action;
            0x8DF66A82 : Drop_action;
            0xF73E52A7 : Drop_action;
            0x4333B771 : Drop_action;
            0xC1726CA0 : Drop_action;
            0xD8C5A955 : Drop_action;
            0x5E364D14 : Drop_action;
            0x9445A0D6 : Drop_action;
            0xC18183A8 : Drop_action;
            0x47AAD5A6 : Drop_action;
            0xBF411CF8 : Drop_action;
            0xE031271A : Drop_action;
            0xC5AA1248 : Drop_action;
            0xB701E72D : Drop_action;
            0x79EB28ED : Drop_action;
            0xAE827519 : Drop_action;
            0xCE6A9D1E : Drop_action;
            0xEB71396B : Drop_action;
            0x7E963E3B : Drop_action;
            0x6A3ADE5A : Drop_action;
            0x127B1D3F : Drop_action;
            0x0BE7EE4A : Drop_action;
            0xC98678B2 : Drop_action;
            0xBDF710F5 : Drop_action;
            0x362D0FCE : Drop_action;
            0x85125D59 : Drop_action;
            0x325EBD22 : Drop_action;
            0x8CF4DC72 : Drop_action;
            0xDBCA815F : Drop_action;
            0x1E86D7DA : Drop_action;
            0xD3850EB2 : Drop_action;
            0x3074393D : Drop_action;
            0x12B7E3FA : Drop_action;
            0x3230E31D : Drop_action;
            0x2FA37195 : Drop_action;
            0xAC40CDCC : Drop_action;
            0x36757F41 : Drop_action;
            0xAAABFDBD : Drop_action;
            0x2C409EC8 : Drop_action;
            0xB6A3C8B9 : Drop_action;
            0xE53FC5FC : Drop_action;
            0x857EE8B3 : Drop_action;
            0x66316D04 : Drop_action;
            0x039DB33D : Drop_action;
            0x7CE15A4C : Drop_action;
            0xBC9F669C : Drop_action;
            0xEC14AF74 : Drop_action;
            0xB2F8801D : Drop_action;
            0x6F907755 : Drop_action;
            0x51B8869E : Drop_action;
            0x5DD826CD : Drop_action;
            0x3930EBF4 : Drop_action;
            0xD1B820B8 : Drop_action;
            0x3E4C39EA : Drop_action;
            0x651CFD6B : Drop_action;
            0xB22A1077 : Drop_action;
            0xF5B09C93 : Drop_action;
            0x85E8CAFA : Drop_action;
            0x08FE2B66 : Drop_action;
            0x532A3F83 : Drop_action;
            0x58BBAE3A : Drop_action;
            0x54A3532E : Drop_action;
            0xC2B16D48 : Drop_action;
            0xDA4A34B7 : Drop_action;
            0xFBF898D7 : Drop_action;
            0x9A379E1C : Drop_action;
            0x71D876D8 : Drop_action;
            0x75077E8A : Drop_action;
            0x30768946 : Drop_action;
            0xC40BA638 : Drop_action;
            0x0E97C19F : Drop_action;
            0xA1D8E814 : Drop_action;
            0x466B9C58 : Drop_action;
            0xFA86E901 : Drop_action;
            0xD3B4C7FA : Drop_action;
            0x67278AE3 : Drop_action;
            0xF89D83F9 : Drop_action;
            0xB11BF3AF : Drop_action;
            0x77C76E15 : Drop_action;
            0xA2B06320 : Drop_action;
            0x376286D1 : Drop_action;
            0xC7C81385 : Drop_action;
            0xBDF62C91 : Drop_action;
            0x699DEDD2 : Drop_action;
            0xB7F81BFA : Drop_action;
            0x3233870F : Drop_action;
            0xFA358A78 : Drop_action;
            0x03B2EB82 : Drop_action;
            0x79284794 : Drop_action;
            0x975EBFE3 : Drop_action;
            0x79CC72F6 : Drop_action;
            0x75F355EC : Drop_action;
            0x16578B6D : Drop_action;
            0xB4DCEA1F : Drop_action;
            0xA42571F4 : Drop_action;
            0x7A5F83BE : Drop_action;
            0x025E5C07 : Drop_action;
            0xB61FFAE8 : Drop_action;
            0xC5AF4F7B : Drop_action;
            0x973849E5 : Drop_action;
            0x541E7AAD : Drop_action;
            0x72BAA457 : Drop_action;
            0xA1A8F506 : Drop_action;
            0xCB1D6595 : Drop_action;
            0x87F1F5D7 : Drop_action;
            0x9BE5B8C1 : Drop_action;
            0xAD40631D : Drop_action;
            0xC1E06AB5 : Drop_action;
            0xE31DDD9F : Drop_action;
            0x1A9C8A75 : Drop_action;
            0xA975591B : Drop_action;
            0x4006D895 : Drop_action;
            0xFDF16302 : Drop_action;
            0xBBB241FA : Drop_action;
            0xAAE8C5DF : Drop_action;
            0x08FA0081 : Drop_action;
            0x5CD39457 : Drop_action;
            0xEDBC47A9 : Drop_action;
            0x1067161E : Drop_action;
            0x736CFD0F : Drop_action;
            0xB6084D23 : Drop_action;
            0x0EA6A6A9 : Drop_action;
            0x0C4DB901 : Drop_action;
            0x0ECC2C19 : Drop_action;
            0x357A4442 : Drop_action;
            0xA64D4BAB : Drop_action;
            0x2CC44907 : Drop_action;
            0x15A9D13A : Drop_action;
            0xE1ED62D5 : Drop_action;
            0xED2387BE : Drop_action;
            0xB4CB13DA : Drop_action;
            0xEF5F3247 : Drop_action;
            0xBB1D2AF0 : Drop_action;
            0x7AA73939 : Drop_action;
            0x199DE9AB : Drop_action;
            0xB3D82D1D : Drop_action;
            0x9C6F3892 : Drop_action;
            0x98BBF92D : Drop_action;
            0xBCB775C6 : Drop_action;
            0x6F6AC32F : Drop_action;
            0xDD679BD0 : Drop_action;
            0x48291708 : Drop_action;
            0xF2535FD8 : Drop_action;
            0x1CC74CD2 : Drop_action;
            0x4C91B570 : Drop_action;
            0xB4DBB7AD : Drop_action;
            0x3FBDEE13 : Drop_action;
            0xEE59B884 : Drop_action;
            0xB73EDFF9 : Drop_action;
            0xC99A5B47 : Drop_action;
            0x14BB33AB : Drop_action;
            0x26D76A82 : Drop_action;
            0xA029C633 : Drop_action;
            0x6242D3F4 : Drop_action;
            0x384F9113 : Drop_action;
            0x1F756E9C : Drop_action;
            0x5D0B74D1 : Drop_action;
            0xC19F150C : Drop_action;
            0x3CFE82EE : Drop_action;
            0x999F3010 : Drop_action;
            0x89B2322C : Drop_action;
            0x363E79F7 : Drop_action;
            0xEAA9E532 : Drop_action;
            0x5B65A0D0 : Drop_action;
            0x4101BCC6 : Drop_action;
            0x6C69EA80 : Drop_action;
            0xAAF520B9 : Drop_action;
            0x0DD4D18D : Drop_action;
            0x8684C010 : Drop_action;
            0x8EA8EB3D : Drop_action;
            0x4264B6D7 : Drop_action;
            0xBE3634D2 : Drop_action;
            0x013256C7 : Drop_action;
            0x72270916 : Drop_action;
            0xDA728611 : Drop_action;
            0x60FD0F34 : Drop_action;
            0xC4186C4C : Drop_action;
            0x9B30ED06 : Drop_action;
            0xD5411A61 : Drop_action;
            0xCDB78298 : Drop_action;
            0xBAF9A743 : Drop_action;
            0x6120557C : Drop_action;
            0x9764B64A : Drop_action;
            0x65B78093 : Drop_action;
            0x2CA7D383 : Drop_action;
            0xBD45B38A : Drop_action;
            0xB715D881 : Drop_action;
            0xE45909FB : Drop_action;
            0x8C291FD1 : Drop_action;
            0xE9ACE554 : Drop_action;
            0x4CDEB6C6 : Drop_action;
            0xE7E91A32 : Drop_action;
            0x7F062DAC : Drop_action;
            0xB37ADDE8 : Drop_action;
            0x5D6A1310 : Drop_action;
            0x13049FA6 : Drop_action;
            0x023C4F2B : Drop_action;
            0x0792C082 : Drop_action;
            0x695FF6AC : Drop_action;
            0x0C5E2957 : Drop_action;
            0xB8EAF7A8 : Drop_action;
            0x44DA7BB4 : Drop_action;
            0x33549C8D : Drop_action;
            0x46E63BFB : Drop_action;
            0x43DA2AE5 : Drop_action;
            0x7E48AC5F : Drop_action;
            0x44910DB6 : Drop_action;
            0xC5F1D2EB : Drop_action;
            0x57DFC4F5 : Drop_action;
            0xF2BA7C56 : Drop_action;
            0x5ECA61AF : Drop_action;
            0x44B62B72 : Drop_action;
            0x0E57735B : Drop_action;
            0x99131227 : Drop_action;
            0x449B56AC : Drop_action;
            0xFD0719D1 : Drop_action;
            0x3432066B : Drop_action;
            0xE0A24E9E : Drop_action;
            0x186D24BA : Drop_action;
            0x4393B760 : Drop_action;
            0xEF8E05F0 : Drop_action;
            0x4EAA533C : Drop_action;
            0xDD82ED86 : Drop_action;
            0x18EBB367 : Drop_action;
            0x831BD1A0 : Drop_action;
            0x6946AFC1 : Drop_action;
            0x09F76D15 : Drop_action;
            0x6DB649B4 : Drop_action;
            0x8C03CC9C : Drop_action;
            0x2CF87E36 : Drop_action;
            0xE9EDE034 : Drop_action;
            0x89DB26F6 : Drop_action;
            0x03FC3A75 : Drop_action;
            0xE1535A35 : Drop_action;
            0x275846FB : Drop_action;
            0x0BFC0A66 : Drop_action;
            0x562CD3BD : Drop_action;
            0x5A07BCE7 : Drop_action;
            0xB15B0595 : Drop_action;
            0xEC66A4E7 : Drop_action;
            0xABEF2D1C : Drop_action;
            0x3BC8782A : Drop_action;
            0xDAAD81EA : Drop_action;
            0x9FD4F8A5 : Drop_action;
            0xF1884832 : Drop_action;
            0x4986E3E4 : Drop_action;
            0xC6EFAF2E : Drop_action;
            0x49F5FC7C : Drop_action;
            0xC0AC8E5F : Drop_action;
            0x154EF8DC : Drop_action;
            0xE7973AF1 : Drop_action;
            0x47587602 : Drop_action;
            0x0A9EB68A : Drop_action;
            0x928FA7FD : Drop_action;
            0x6500248E : Drop_action;
            0x2DF4DA5C : Drop_action;
            0x9A6A2105 : Drop_action;
            0x9D0A09E5 : Drop_action;
            0x1ED28BA6 : Drop_action;
            0x943F389A : Drop_action;
            0xB11550D9 : Drop_action;
            0xC85204B0 : Drop_action;
            0x9657EC48 : Drop_action;
            0x7A0225FC : Drop_action;
            0xF0EE8818 : Drop_action;
            0x3CE5C5BF : Drop_action;
            0xFD705BA0 : Drop_action;
            0x27ACAD71 : Drop_action;
            0x8ECADB79 : Drop_action;
            0xF68BBFA3 : Drop_action;
            0x7BBCB628 : Drop_action;
            0xFBD5ABD9 : Drop_action;
            0xF1DEB048 : Drop_action;
            0x0C1735C0 : Drop_action;
            0x30A3E0A9 : Drop_action;
            0x8D5E5786 : Drop_action;
            0xF6948F5A : Drop_action;
            0x49E18EC6 : Drop_action;
            0x0DFDD00A : Drop_action;
            0x1359E565 : Drop_action;
            0x6C8E7041 : Drop_action;
            0x719C6F86 : Drop_action;
            0xB0C7C965 : Drop_action;
            0x4BD57E6B : Drop_action;
            0xEFB7ED25 : Drop_action;
            0x55F1FFA9 : Drop_action;
            0x83B1CA28 : Drop_action;
            0x2BAA054F : Drop_action;
            0xDEE27A06 : Drop_action;
            0xDF76C082 : Drop_action;
            0xF26A0648 : Drop_action;
            0xB2F2DC43 : Drop_action;
            0xC3BC80E1 : Drop_action;
            0x897E2580 : Drop_action;
            0x1D275C11 : Drop_action;
            0xB908F272 : Drop_action;
            0xBE2336B5 : Drop_action;
            0x52593CE5 : Drop_action;
            0xFB91AFF5 : Drop_action;
            0xF6AB4AD5 : Drop_action;
            0xF3A30B32 : Drop_action;
            0xBED4326F : Drop_action;
            0xB4D3B14B : Drop_action;
            0x0E36FAFA : Drop_action;
            0x85F1820E : Drop_action;
            0x31B57110 : Drop_action;
            0x7B74EFE6 : Drop_action;
            0x05F98EE1 : Drop_action;
            0x21A22468 : Drop_action;
            0xEF5830FB : Drop_action;
            0x86FD844E : Drop_action;
            0x9E3C98FE : Drop_action;
            0x5FA84963 : Drop_action;
            0x35E898F9 : Drop_action;
            0x2D42AC87 : Drop_action;
            0xFFEB7BFD : Drop_action;
            0x4B07BBD9 : Drop_action;
            0x27C64FD1 : Drop_action;
            0x44F7CF43 : Drop_action;
            0x3A5A3066 : Drop_action;
            0x9D7933BD : Drop_action;
            0x5268CB1D : Drop_action;
            0x29E3B72C : Drop_action;
            0x9F959069 : Drop_action;
            0x9E4FD66A : Drop_action;
            0x103B6CEC : Drop_action;
            0x59A59C00 : Drop_action;
            0x2F3A17EE : Drop_action;
            0xF7CBF1CC : Drop_action;
            0xB4F54A93 : Drop_action;
            0x7791DCE3 : Drop_action;
            0x6C1A966A : Drop_action;
            0x33975446 : Drop_action;
            0x51A9E662 : Drop_action;
            0xE36DEE78 : Drop_action;
            0x40D4C2B9 : Drop_action;
            0x72F46765 : Drop_action;
            0x9004DD50 : Drop_action;
            0x8F01EDA8 : Drop_action;
            0xA574D0E8 : Drop_action;
            0xCC839D24 : Drop_action;
            0x2A94FCE5 : Drop_action;
            0xCABCCB45 : Drop_action;
            0xF7B556AF : Drop_action;
            0x35B1EBAC : Drop_action;
            0x4C70CED7 : Drop_action;
            0x3DE700C4 : Drop_action;
            0xE946C161 : Drop_action;
            0xE7B7D3E8 : Drop_action;
            0xEC8183CD : Drop_action;
            0xFF4A4F3A : Drop_action;
            0x98BF03B7 : Drop_action;
            0xB9F0E39C : Drop_action;
            0xCAAC4BA5 : Drop_action;
            0xB2EA974F : Drop_action;
            0x639C2700 : Drop_action;
            0x9354790A : Drop_action;
            0x83F8B3C1 : Drop_action;
            0xE0DA0AB2 : Drop_action;
            0xC7118A03 : Drop_action;
            0x2A04FABF : Drop_action;
            0x9473AF32 : Drop_action;
            0xBDABC99C : Drop_action;
            0x9D9CB29F : Drop_action;
            0xF9D23F3F : Drop_action;
            0xC5A7715D : Drop_action;
            0xD68BFEA9 : Drop_action;
            0x11DDFE81 : Drop_action;
            0x964B20C2 : Drop_action;
            0x308443B0 : Drop_action;
            0x01712A00 : Drop_action;
            0xB6AC2D42 : Drop_action;
            0xD568E78D : Drop_action;
            0xF278442C : Drop_action;
            0xABAACAB0 : Drop_action;
            0x31063A3F : Drop_action;
            0x7F46687F : Drop_action;
            0xAC1FFF6E : Drop_action;
            0xDBFDE6F6 : Drop_action;
            0xCB378C2E : Drop_action;
            0xCF711901 : Drop_action;
            0x8FC20644 : Drop_action;
            0x9473629A : Drop_action;
            0x07B4BBAA : Drop_action;
            0xC28DE171 : Drop_action;
            0xE242C304 : Drop_action;
            0xDC209D7D : Drop_action;
            0x461C4C78 : Drop_action;
            0xC3DCF06D : Drop_action;
            0xB33542B5 : Drop_action;
            0x3AAFDEEB : Drop_action;
            0x39250F70 : Drop_action;
            0xFD9AB3F8 : Drop_action;
            0x3CF5B657 : Drop_action;
            0x1C092ED6 : Drop_action;
            0xF6CC6DB1 : Drop_action;
            0x47A803F4 : Drop_action;
            0x5E1857DA : Drop_action;
            0xD8FF323B : Drop_action;
            0xF020F185 : Drop_action;
            0x310FAF7A : Drop_action;
            0x2C752405 : Drop_action;
            0x4A5DDE14 : Drop_action;
            0xC7D9C393 : Drop_action;
            0xB99EA75B : Drop_action;
            0xF7112D21 : Drop_action;
            0x74CC082B : Drop_action;
            0x42B1F47B : Drop_action;
            0xB4692240 : Drop_action;
            0x7F9162F0 : Drop_action;
            0xEA519A2C : Drop_action;
            0x8B313173 : Drop_action;
            0xFB72DCB3 : Drop_action;
            0x3800CCB4 : Drop_action;
            0x01A500C5 : Drop_action;
            0x424FEE24 : Drop_action;
            0xAC212DBC : Drop_action;
            0x3C605F6F : Drop_action;
            0xEA2C7994 : Drop_action;
            0xF8C64560 : Drop_action;
            0xA0D456EE : Drop_action;
            0x28805499 : Drop_action;
            0x19353A4D : Drop_action;
            0xC3EAFD5A : Drop_action;
            0x75E3EC2F : Drop_action;
            0xA7D9257A : Drop_action;
            0x77ACB244 : Drop_action;
            0x24D77BEB : Drop_action;
            0xC1F7327F : Drop_action;
            0x7C813A9D : Drop_action;
            0x292D65B0 : Drop_action;
            0x8B12BE1B : Drop_action;
            0xCE5D8FE9 : Drop_action;
            0x3E6695B9 : Drop_action;
            0x212DB868 : Drop_action;
            0x5DB7E08A : Drop_action;
            0xACAF68A9 : Drop_action;
            0x6947E51B : Drop_action;
            0x14BEE5D1 : Drop_action;
            0x240FE80B : Drop_action;
            0xCE9B98D2 : Drop_action;
            0x3B7E8B94 : Drop_action;
            0xAE1A977E : Drop_action;
            0x183ED98C : Drop_action;
            0xA9C11BE6 : Drop_action;
            0x14334849 : Drop_action;
            0x1FD31839 : Drop_action;
            0x8F16B9BB : Drop_action;
            0x74F6B67E : Drop_action;
            0x3C85E207 : Drop_action;
            0xA279A042 : Drop_action;
            0x0AFA8C40 : Drop_action;
            0xBB8B6B2F : Drop_action;
            0x89BA422B : Drop_action;
            0xCE243C3D : Drop_action;
            0x3CF6F6A0 : Drop_action;
            0xDFB92CEC : Drop_action;
            0x156023DD : Drop_action;
            0x1733C404 : Drop_action;
            0x0D3F1859 : Drop_action;
            0xBDBAA432 : Drop_action;
            0xB45EFB9A : Drop_action;
            0xCEC729E6 : Drop_action;
            0x73590901 : Drop_action;
            0x7CB61208 : Drop_action;
            0xE49E8638 : Drop_action;
            0xCFE90985 : Drop_action;
            0x5362B305 : Drop_action;
            0x9BA69427 : Drop_action;
            0x98F6B8BC : Drop_action;
            0x5BC976C0 : Drop_action;
            0x2E0FAF87 : Drop_action;
            0x7EB9582F : Drop_action;
            0x9590DA0D : Drop_action;
            0x6B3DAE8D : Drop_action;
            0x392387E8 : Drop_action;
            0x8C5C79B4 : Drop_action;
            0xA859FC32 : Drop_action;
            0x611C72B4 : Drop_action;
            0xAF4B3F46 : Drop_action;
            0x8C444180 : Drop_action;
            0xCBA91C11 : Drop_action;
            0xAA4D6CBB : Drop_action;
            0x9AF92977 : Drop_action;
            0xC97FF787 : Drop_action;
            0x7437A191 : Drop_action;
            0xD4EE583B : Drop_action;
            0x7ED5CC79 : Drop_action;
            0x928FF89B : Drop_action;
            0x69C72E77 : Drop_action;
            0xEA48191D : Drop_action;
            0xC9F3D8BE : Drop_action;
            0x22ADCC3C : Drop_action;
            0x0B3BA8C0 : Drop_action;
            0x8BE91DB9 : Drop_action;
            0xB912E0AA : Drop_action;
            0x3C375F3D : Drop_action;
            0x36728748 : Drop_action;
            0xB2604815 : Drop_action;
            0x0E0044F8 : Drop_action;
            0x7EA6BFDF : Drop_action;
            0x087DADEA : Drop_action;
            0xD7970E5E : Drop_action;
            0x1F14CB93 : Drop_action;
            0xAAA48A9D : Drop_action;
            0x60FD3C75 : Drop_action;
            0x137A1BD2 : Drop_action;
            0x8F29F8E9 : Drop_action;
            0xE53E9564 : Drop_action;
            0x94ABB7AB : Drop_action;
            0xD732F0BD : Drop_action;
            0x07E1B18B : Drop_action;
            0x5C2F6576 : Drop_action;
            0xCF966A20 : Drop_action;
            0xF1D3A15E : Drop_action;
            0x36447DFC : Drop_action;
            0xB171F688 : Drop_action;
            0x1DBA92CF : Drop_action;
            0x9FDC8883 : Drop_action;
            0x9E9E9CE1 : Drop_action;
            0x15949F82 : Drop_action;
            0xACF06020 : Drop_action;
            0x8E3D82EE : Drop_action;
            0x0C44E82D : Drop_action;
            0xA366F7B4 : Drop_action;
            0xF68E0255 : Drop_action;
            0x489DE9D2 : Drop_action;
            0x3586C5E8 : Drop_action;
            0xAA593324 : Drop_action;
            0x7BC053DE : Drop_action;
            0x7D9FAE6F : Drop_action;
            0x381A6B4C : Drop_action;
            0xF9D11427 : Drop_action;
            0x8C9D9B6C : Drop_action;
            0x9B500315 : Drop_action;
            0x8CD02D87 : Drop_action;
            0x8C6E18C0 : Drop_action;
            0x9467E0C6 : Drop_action;
            0xAED6AB3D : Drop_action;
            0x14E5A892 : Drop_action;
            0x4B98EB13 : Drop_action;
            0x643E3CE1 : Drop_action;
            0xD632FC7F : Drop_action;
            0x2A728258 : Drop_action;
            0x5314D563 : Drop_action;
            0x046E92D1 : Drop_action;
            0xCC4A7E41 : Drop_action;
            0xB53A6D28 : Drop_action;
            0xF2A15845 : Drop_action;
            0x3F5EA0DF : Drop_action;
            0x84029E1D : Drop_action;
            0x9868B348 : Drop_action;
            0xA656482B : Drop_action;
            0xB6143376 : Drop_action;
            0xECA656EC : Drop_action;
            0xDD69672C : Drop_action;
            0x84B8F5C3 : Drop_action;
            0xAD306458 : Drop_action;
            0x6154E0FD : Drop_action;
            0x075CAB0A : Drop_action;
            0xF401FC01 : Drop_action;
            0x0B847DC2 : Drop_action;
            0xA46D40AE : Drop_action;
            0xF55E99E9 : Drop_action;
            0x25032D9D : Drop_action;
            0x1E5AA6E3 : Drop_action;
            0xDE70DA51 : Drop_action;
            0xCDA8D100 : Drop_action;
            0x5C806076 : Drop_action;
            0x2DC7342D : Drop_action;
            0xA69BB9C0 : Drop_action;
            0x9F9C2637 : Drop_action;
            0xB0005E41 : Drop_action;
            0xA064BCCF : Drop_action;
            0x96B00736 : Drop_action;
            0x70398D3B : Drop_action;
            0xF2055756 : Drop_action;
            0xB8EDFD3E : Drop_action;
            0x75B327EF : Drop_action;
            0x78A99F51 : Drop_action;
            0x6C1E284E : Drop_action;
            0xE5EFCFA7 : Drop_action;
            0xFE498603 : Drop_action;
            0xF57720A6 : Drop_action;
            0x63D6DA4A : Drop_action;
            0x8E9DEE21 : Drop_action;
            0x84EE7813 : Drop_action;
            0xB4189852 : Drop_action;
            0x98B7A0BD : Drop_action;
            0x65DDAAFB : Drop_action;
            0xF0490EC7 : Drop_action;
            0x91AB6285 : Drop_action;
            0x5A333B8D : Drop_action;
            0x2033D0F6 : Drop_action;
            0xE5B82AB4 : Drop_action;
            0x9A180FA6 : Drop_action;
            0x1197A7C7 : Drop_action;
            0xC79D96D7 : Drop_action;
            0xD62BB8A3 : Drop_action;
            0x8D189B3E : Drop_action;
            0xC2A84846 : Drop_action;
            0xFB8A0B47 : Drop_action;
            0x6E3A6789 : Drop_action;
            0x6F7EE063 : Drop_action;
            0x26D9388F : Drop_action;
            0x3E8C1660 : Drop_action;
            0x8FC06531 : Drop_action;
            0x79B9DCE3 : Drop_action;
            0xD48E6F25 : Drop_action;
            0xF013120F : Drop_action;
            0xEBDBD558 : Drop_action;
            0x76673792 : Drop_action;
            0x034FAC11 : Drop_action;
            0xBFDEF864 : Drop_action;
            0x520486BC : Drop_action;
            0x06CA71C7 : Drop_action;
            0x798F00AB : Drop_action;
            0xEEABDEE9 : Drop_action;
            0x12B189E9 : Drop_action;
            0xA403A5A8 : Drop_action;
            0x74E77C14 : Drop_action;
            0x891A9115 : Drop_action;
            0xB297726F : Drop_action;
            0x869BB41C : Drop_action;
            0x1A4F5978 : Drop_action;
            0x97B1F01E : Drop_action;
            0xDA74F4B2 : Drop_action;
            0x743D43B8 : Drop_action;
            0x73DAC37F : Drop_action;
            0x1E640B3D : Drop_action;
            0xDFB30A9A : Drop_action;
            0xB1E1C4FC : Drop_action;
            0x6BD0B4D9 : Drop_action;
            0x6F139DFD : Drop_action;
            0x712B1A77 : Drop_action;
            0x6DE9CD29 : Drop_action;
            0x286CD3E7 : Drop_action;
            0x9D777E52 : Drop_action;
            0x14548350 : Drop_action;
            0xBDD108B8 : Drop_action;
            0xCFA553C2 : Drop_action;
            0x792069DB : Drop_action;
            0x8A40BB7F : Drop_action;
            0x797088DC : Drop_action;
            0x6C06A548 : Drop_action;
            0xF4324A93 : Drop_action;
            0xCCE1BFAF : Drop_action;
            0xE5A04BF1 : Drop_action;
            0x4A6E629A : Drop_action;
            0xA8946CEF : Drop_action;
            0x141052B5 : Drop_action;
            0x5120E891 : Drop_action;
            0xB5541A28 : Drop_action;
            0x38458D4D : Drop_action;
            0x85B0555E : Drop_action;
            0xC59D9274 : Drop_action;
            0xA2EE1D66 : Drop_action;
            0xACC82F4F : Drop_action;
            0x3F2CA526 : Drop_action;
            0xE73FEC47 : Drop_action;
            0xDDAFFB61 : Drop_action;
            0x1EA1AC2D : Drop_action;
            0xAD00CC7D : Drop_action;
            0xCEFCD4F9 : Drop_action;
            0xE1AB0DDA : Drop_action;
            0x9DE7986E : Drop_action;
            0xD7EBEC38 : Drop_action;
            0x208256C7 : Drop_action;
            0xAF9F2F0E : Drop_action;
            0x2E467D7D : Drop_action;
            0xAC48D191 : Drop_action;
            0xD585F8A5 : Drop_action;
            0xE0ACE9B2 : Drop_action;
            0xA5120CD2 : Drop_action;
            0x0A63620F : Drop_action;
            0x624C4E2C : Drop_action;
            0x44754C9C : Drop_action;
            0x1A78F0ED : Drop_action;
            0x3B0DCE9F : Drop_action;
            0x463DA407 : Drop_action;
            0x8E06A22A : Drop_action;
            0xB4B8CA2C : Drop_action;
            0xBEABE7F0 : Drop_action;
            0xE4A5D973 : Drop_action;
            0x15E6FC92 : Drop_action;
            0xEB44E872 : Drop_action;
            0x951DDCE7 : Drop_action;
            0xD51224EC : Drop_action;
            0x4D292551 : Drop_action;
            0x66CCE732 : Drop_action;
            0x5E1ADB47 : Drop_action;
            0xBDC96C69 : Drop_action;
            0x5D081468 : Drop_action;
            0xEF57BFD1 : Drop_action;
            0xE73DCE29 : Drop_action;
            0xADF5F390 : Drop_action;
            0xD90CFF4B : Drop_action;
            0x78EB588B : Drop_action;
            0xF041917D : Drop_action;
            0xABF593AA : Drop_action;
            0x52E7B384 : Drop_action;
            0x63B03CCE : Drop_action;
            0xEDCF93A0 : Drop_action;
            0x71711B03 : Drop_action;
            0x40F68CFA : Drop_action;
            0xBD2A312B : Drop_action;
            0x16499C41 : Drop_action;
            0x6D505B91 : Drop_action;
            0xFB36318A : Drop_action;
            0xEEA2266C : Drop_action;
            0xA513C7F4 : Drop_action;
            0x209501A8 : Drop_action;
            0x2AC46038 : Drop_action;
            0x5BF4000A : Drop_action;
            0x1DB1AE5C : Drop_action;
            0xC81A572E : Drop_action;
            0x3E315972 : Drop_action;
            0x287D9BA1 : Drop_action;
            0xB41CD9A8 : Drop_action;
            0x669C9767 : Drop_action;
            0x562F4C49 : Drop_action;
            0x1EA03BC9 : Drop_action;
            0xD97AF5A7 : Drop_action;
            0x25D925A7 : Drop_action;
            0xBCCC6AE8 : Drop_action;
            0xBC28AA97 : Drop_action;
            0x953F0F55 : Drop_action;
            0x5121EBD1 : Drop_action;
            0x863153C3 : Drop_action;
            0x844F47F2 : Drop_action;
            0xE8FF66E3 : Drop_action;
            0x0EC192F9 : Drop_action;
            0x87639205 : Drop_action;
            0x635DF1E9 : Drop_action;
            0x9019DB16 : Drop_action;
            0x2EE6C784 : Drop_action;
            0xA47F9BC2 : Drop_action;
            0x2A0A7368 : Drop_action;
            0x4F731EFE : Drop_action;
            0xEC577928 : Drop_action;
            0x75808E50 : Drop_action;
            0xA14E28C4 : Drop_action;
            0xF6574BE1 : Drop_action;
            0x46798D2E : Drop_action;
            0xDC54DE80 : Drop_action;
            0x1197E9C3 : Drop_action;
            0x4BDE338A : Drop_action;
            0xBB40587D : Drop_action;
            0x9923113A : Drop_action;
            0xF0F89F0F : Drop_action;
            0x36F3B79B : Drop_action;
            0xD7397DFD : Drop_action;
            0x58681B4C : Drop_action;
            0xEE36C379 : Drop_action;
            0x18FC4A1F : Drop_action;
            0xFB0E6003 : Drop_action;
            0xE1C45281 : Drop_action;
            0xCB77CFAB : Drop_action;
            0xBFAB5F56 : Drop_action;
            0x99E672AD : Drop_action;
            0x47CD1301 : Drop_action;
            0x46718993 : Drop_action;
            0xAA777F3B : Drop_action;
            0x9CB52A79 : Drop_action;
            0xAEA2CF32 : Drop_action;
            0x6984514B : Drop_action;
            0xCF87628F : Drop_action;
            0x5130060F : Drop_action;
            0xD87F5205 : Drop_action;
            0x1BAD7298 : Drop_action;
            0x5283897B : Drop_action;
            0xB09BF53D : Drop_action;
            0xF915FE47 : Drop_action;
            0x157F9B43 : Drop_action;
            0xF1B9DFEE : Drop_action;
            0x0DCDBD6D : Drop_action;
            0x480A0029 : Drop_action;
            0xBB113E50 : Drop_action;
            0x3F01D2BF : Drop_action;
            0x5AEB8C63 : Drop_action;
            0xF3B9959A : Drop_action;
            0xA58B1075 : Drop_action;
            0x3DE0DA8E : Drop_action;
            0x2EEE2F56 : Drop_action;
            0xF33D3122 : Drop_action;
            0xA2A596FA : Drop_action;
            0x6B8F2FA8 : Drop_action;
            0xFD8A31A1 : Drop_action;
            0x74CA80C5 : Drop_action;
            0xC9E210D6 : Drop_action;
            0x0A000002 : Set_dmac(0x021122334402);
            0x0A000001 : Set_dmac(0x021122334401);
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

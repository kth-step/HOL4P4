#include <core.p4>
#include <v1model.p4>

struct headers {}

struct metadata {}

parser MyParser(packet_in packet,
                out headers hdr,
                inout metadata meta,
                inout standard_metadata_t standard_metadata) {
    state start {
        transition accept;
    }
}

control MyVerifyChecksum(inout headers hdr,
                         inout metadata meta) {
    apply {}
}

control MyIngress(inout headers hdr,
                  inout metadata meta,
                  inout standard_metadata_t standard_metadata) {
    register<bit<16>>(1) r;
    bit<16> tmp;

    action read_register(){
        r.read(tmp, 0); 
        tmp=tmp+1;
    }
    action write_register(){r.write(0, tmp);}

    table flowlet{
        actions = {read_register;}
    }
    table new_flowlet{
        actions = {write_register;}
    }

    apply
    {
        {
            flowlet.apply();
            //if (ingress_metadata.flow_ipg > FLOWLET_INACTIVE_TIMEOUT)
            new_flowlet.apply();
        }
    }
}


control MyEgress(inout headers hdr,
                 inout metadata meta,
                 inout standard_metadata_t standard_metadata) {
    apply {}
}

control MyComputeChecksum(inout headers hdr, inout metadata meta) {
    apply {}
}

control MyDeparser(packet_out packet, in headers hdr) {
    apply {}
}

V1Switch(
 MyParser(),
 MyVerifyChecksum(),
 MyIngress(),
 MyEgress(),
 MyComputeChecksum(),
 MyDeparser()
) main;

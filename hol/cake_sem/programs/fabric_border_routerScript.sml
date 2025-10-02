open HolKernel boolLib Parse bossLib;

val _ = new_theory "fabric_border_router";

open p4Syntax;
open bitstringSyntax numSyntax;
open p4Theory;
open p4_auxTheory;
open p4_cake_exec_semTheory;
open p4_coreTheory p4_v1modelTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_progLib;

intLib.deprecate_int();
ratLib.deprecate_rat();
realLib.deprecate_real();
val _ = (max_print_depth := 1000);

open p4_cake_exec_semProgTheory p4_cake_arch_v1modelProgTheory;
open p4_cake_transformLib;

val _ = translation_extends "p4_cake_arch_v1modelProg";

(*******************************)
(* Google fabric border router *)

(*

This program is fabric_border_router.p4 (with flag SAI_INSTANTIATION_FABRIC_BORDER_ROUTER set) from
sonic-pins imported into HOL4P4, with certain hard-coded table entries. The original repo can be
obtained by

  git clone git@github.com:sonic-net/sonic-pins.git

after which the HOL4P4 import tool can be used to generate the below.


The original license of fabric_border_router.p4:


                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

*)

val google_fbr_actx = “([arch_block_inp;
  arch_block_pbl "packet_parser"
    [e_var (varn_name "b"); e_var (varn_name "parsedHdr");
     e_var (varn_name "meta"); e_var (varn_name "standard_metadata")];
  arch_block_ffbl "postparser";
  arch_block_pbl "verify_ipv4_checksum"
    [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_ffbl "preingress";
  arch_block_pbl "ingress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "egress"
    [e_var (varn_name "hdr"); e_var (varn_name "meta");
     e_var (varn_name "standard_metadata")];
  arch_block_pbl "compute_ipv4_checksum"
    [e_var (varn_name "hdr"); e_var (varn_name "meta")];
  arch_block_pbl "packet_deparser"
    [e_var (varn_name "b"); e_var (varn_name "hdr")]; arch_block_out],
 [("packet_parser",pbl_type_parser,
   [("packet",d_none); ("headers",d_out); ("local_metadata",d_inout);
    ("standard_metadata",d_inout)],
   [("packet_parser",stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),
     [])],[],
   [("start",
     stmt_seq
       (stmt_seq
          (stmt_ass
             (lval_field (lval_varname (varn_name "local_metadata"))
                "enable_vlan_checks") (e_v (v_bool F)))
          (stmt_seq
             (stmt_ass
                (lval_field (lval_varname (varn_name "local_metadata"))
                   "vlan_id")
                (e_v (v_bit ([F; F; F; F; F; F; F; F; F; F; F; F],12))))
             (stmt_seq
                (stmt_ass
                   (lval_field (lval_varname (varn_name "local_metadata"))
                      "admit_to_l3") (e_v (v_bool F)))
                (stmt_seq
                   (stmt_ass
                      (lval_field (lval_varname (varn_name "local_metadata"))
                         "vrf_id")
                      (e_v (v_bit ([F; F; F; F; F; F; F; F; F; F],10))))
                   (stmt_seq
                      (stmt_ass
                         (lval_field
                            (lval_varname (varn_name "local_metadata"))
                            "enable_decrement_ttl") (e_v (v_bool F)))
                      (stmt_seq
                         (stmt_ass
                            (lval_field
                               (lval_varname (varn_name "local_metadata"))
                               "enable_src_mac_rewrite") (e_v (v_bool F)))
                         (stmt_seq
                            (stmt_ass
                               (lval_field
                                  (lval_varname (varn_name "local_metadata"))
                                  "enable_dst_mac_rewrite") (e_v (v_bool F)))
                            (stmt_seq
                               (stmt_ass
                                  (lval_field
                                     (lval_varname
                                        (varn_name "local_metadata"))
                                     "enable_vlan_rewrite") (e_v (v_bool F)))
                               (stmt_seq
                                  (stmt_ass
                                     (lval_field
                                        (lval_field
                                           (lval_varname
                                              (varn_name "local_metadata"))
                                           "packet_rewrites") "src_mac")
                                     (e_v
                                        (v_bit
                                           ([F; F; F; F; F; F; F; F; F; F; F;
                                             F; F; F; F; F; F; F; F; F; F; F;
                                             F; F; F; F; F; F; F; F; F; F; F;
                                             F; F; F; F; F; F; F; F; F; F; F;
                                             F; F; F; F],48))))
                                  (stmt_seq
                                     (stmt_ass
                                        (lval_field
                                           (lval_field
                                              (lval_varname
                                                 (varn_name "local_metadata"))
                                              "packet_rewrites") "dst_mac")
                                        (e_v
                                           (v_bit
                                              ([F; F; F; F; F; F; F; F; F; F;
                                                F; F; F; F; F; F; F; F; F; F;
                                                F; F; F; F; F; F; F; F; F; F;
                                                F; F; F; F; F; F; F; F; F; F;
                                                F; F; F; F; F; F; F; F],48))))
                                     (stmt_seq
                                        (stmt_ass
                                           (lval_field
                                              (lval_varname
                                                 (varn_name "local_metadata"))
                                              "l4_src_port")
                                           (e_v
                                              (v_bit
                                                 ([F; F; F; F; F; F; F; F; F;
                                                   F; F; F; F; F; F; F],16))))
                                        (stmt_seq
                                           (stmt_ass
                                              (lval_field
                                                 (lval_varname
                                                    (varn_name
                                                       "local_metadata"))
                                                 "l4_dst_port")
                                              (e_v
                                                 (v_bit
                                                    ([F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; F; F],
                                                     16))))
                                           (stmt_seq
                                              (stmt_ass
                                                 (lval_field
                                                    (lval_varname
                                                       (varn_name
                                                          "local_metadata"))
                                                    "wcmp_selector_input")
                                                 (e_v
                                                    (v_bit
                                                       ([F; F; F; F; F; F; F;
                                                         F; F; F; F; F; F; F;
                                                         F; F],16))))
                                              (stmt_seq
                                                 (stmt_ass
                                                    (lval_field
                                                       (lval_varname
                                                          (varn_name
                                                             "local_metadata"))
                                                       "apply_tunnel_decap_at_end_of_pre_ingress")
                                                    (e_v (v_bool F)))
                                                 (stmt_seq
                                                    (stmt_ass
                                                       (lval_field
                                                          (lval_varname
                                                             (varn_name
                                                                "local_metadata"))
                                                          "apply_tunnel_encap_at_egress")
                                                       (e_v (v_bool F)))
                                                    (stmt_seq
                                                       (stmt_ass
                                                          (lval_field
                                                             (lval_varname
                                                                (varn_name
                                                                   "local_metadata"))
                                                             "tunnel_encap_src_ipv6")
                                                          (e_v
                                                             (v_bit
                                                                ([F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F],
                                                                 128))))
                                                       (stmt_seq
                                                          (stmt_ass
                                                             (lval_field
                                                                (lval_varname
                                                                   (varn_name
                                                                      "local_metadata"))
                                                                "tunnel_encap_dst_ipv6")
                                                             (e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F],
                                                                    128))))
                                                          (stmt_seq
                                                             (stmt_ass
                                                                (lval_field
                                                                   (lval_varname
                                                                      (varn_name
                                                                         "local_metadata"))
                                                                   "marked_to_copy")
                                                                (e_v
                                                                   (v_bool F)))
                                                             (stmt_seq
                                                                (stmt_ass
                                                                   (lval_field
                                                                      (lval_varname
                                                                         (varn_name
                                                                            "local_metadata"))
                                                                      "marked_to_mirror")
                                                                   (e_v
                                                                      (v_bool
                                                                         F)))
                                                                (stmt_seq
                                                                   (stmt_ass
                                                                      (lval_field
                                                                         (lval_varname
                                                                            (varn_name
                                                                               "local_metadata"))
                                                                         "mirror_session_id")
                                                                      (e_v
                                                                         (v_bit
                                                                            ([F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F],
                                                                             10))))
                                                                   (stmt_seq
                                                                      (stmt_ass
                                                                         (lval_field
                                                                            (lval_varname
                                                                               (varn_name
                                                                                  "local_metadata"))
                                                                            "mirror_egress_port")
                                                                         (e_v
                                                                            (v_bit
                                                                               ([F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F],
                                                                                9))))
                                                                      (stmt_seq
                                                                         (stmt_ass
                                                                            (lval_field
                                                                               (lval_varname
                                                                                  (varn_name
                                                                                     "local_metadata"))
                                                                               "color")
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F],
                                                                                   2))))
                                                                         (stmt_seq
                                                                            (stmt_ass
                                                                               (lval_field
                                                                                  (lval_varname
                                                                                     (varn_name
                                                                                        "local_metadata"))
                                                                                  "ingress_port")
                                                                               (e_cast
                                                                                  (cast_unsigned
                                                                                     9)
                                                                                  (e_acc
                                                                                     (e_var
                                                                                        (varn_name
                                                                                           "standard_metadata"))
                                                                                     "ingress_port")))
                                                                            (stmt_seq
                                                                               (stmt_ass
                                                                                  (lval_field
                                                                                     (lval_varname
                                                                                        (varn_name
                                                                                           "local_metadata"))
                                                                                     "route_metadata")
                                                                                  (e_v
                                                                                     (v_bit
                                                                                        ([F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F],
                                                                                         6))))
                                                                               (stmt_seq
                                                                                  (stmt_ass
                                                                                     (lval_field
                                                                                        (lval_varname
                                                                                           (varn_name
                                                                                              "local_metadata"))
                                                                                        "bypass_ingress")
                                                                                     (e_v
                                                                                        (v_bool
                                                                                           F)))
                                                                                  (stmt_seq
                                                                                     (stmt_ass
                                                                                        (lval_field
                                                                                           (lval_varname
                                                                                              (varn_name
                                                                                                 "local_metadata"))
                                                                                           "wcmp_group_id_valid")
                                                                                        (e_v
                                                                                           (v_bool
                                                                                              F)))
                                                                                     (stmt_seq
                                                                                        (stmt_ass
                                                                                           (lval_field
                                                                                              (lval_varname
                                                                                                 (varn_name
                                                                                                    "local_metadata"))
                                                                                              "wcmp_group_id_value")
                                                                                           (e_v
                                                                                              (v_bit
                                                                                                 ([F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F],
                                                                                                  12))))
                                                                                        (stmt_seq
                                                                                           (stmt_ass
                                                                                              (lval_field
                                                                                                 (lval_varname
                                                                                                    (varn_name
                                                                                                       "local_metadata"))
                                                                                                 "nexthop_id_valid")
                                                                                              (e_v
                                                                                                 (v_bool
                                                                                                    F)))
                                                                                           (stmt_seq
                                                                                              (stmt_ass
                                                                                                 (lval_field
                                                                                                    (lval_varname
                                                                                                       (varn_name
                                                                                                          "local_metadata"))
                                                                                                    "nexthop_id_value")
                                                                                                 (e_v
                                                                                                    (v_bit
                                                                                                       ([F;
                                                                                                         F;
                                                                                                         F;
                                                                                                         F;
                                                                                                         F;
                                                                                                         F;
                                                                                                         F;
                                                                                                         F;
                                                                                                         F;
                                                                                                         F],
                                                                                                        10))))
                                                                                              (stmt_seq
                                                                                                 (stmt_ass
                                                                                                    (lval_field
                                                                                                       (lval_varname
                                                                                                          (varn_name
                                                                                                             "local_metadata"))
                                                                                                       "ipmc_table_hit")
                                                                                                    (e_v
                                                                                                       (v_bool
                                                                                                          F)))
                                                                                                 (stmt_ass
                                                                                                    (lval_field
                                                                                                       (lval_varname
                                                                                                          (varn_name
                                                                                                             "local_metadata"))
                                                                                                       "acl_drop")
                                                                                                    (e_v
                                                                                                       (v_bool
                                                                                                          F)))))))))))))))))))))))))))))))))
       (stmt_trans
          (e_select
             (e_struct
                [("",
                  e_acc (e_var (varn_name "standard_metadata"))
                    "ingress_port")])
             [([s_sing (v_bit ([T; T; T; T; T; T; T; T; F],9))],
               "parse_packet_out_header")] "parse_ethernet")));
    ("parse_packet_out_header",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "headers")) "packet_out_header"]))
       (stmt_trans (e_v (v_str "parse_ethernet"))));
    ("parse_ethernet",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "headers")) "ethernet"]))
       (stmt_trans
          (e_select
             (e_struct
                [("",
                  e_acc (e_acc (e_var (varn_name "headers")) "ethernet")
                    "ether_type")])
             [([s_sing
                  (v_bit
                     ([F; F; F; F; T; F; F; F; F; F; F; F; F; F; F; F],16))],
               "parse_ipv4");
              ([s_sing
                  (v_bit
                     ([T; F; F; F; F; T; T; F; T; T; F; T; T; T; F; T],16))],
               "parse_ipv6");
              ([s_sing
                  (v_bit
                     ([F; F; F; F; T; F; F; F; F; F; F; F; F; T; T; F],16))],
               "parse_arp")] "accept")));
    ("parse_ipv4",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "headers")) "ipv4"]))
       (stmt_trans
          (e_select
             (e_struct
                [("",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "protocol")])
             [([s_sing (v_bit ([F; F; F; F; F; T; F; F],8))],
               "parse_ipv4_in_ip");
              ([s_sing (v_bit ([F; F; T; F; T; F; F; T],8))],
               "parse_ipv6_in_ip");
              ([s_sing (v_bit ([F; F; F; F; F; F; F; T],8))],"parse_icmp");
              ([s_sing (v_bit ([F; F; F; F; F; T; T; F],8))],"parse_tcp");
              ([s_sing (v_bit ([F; F; F; T; F; F; F; T],8))],"parse_udp")]
             "accept")));
    ("parse_ipv4_in_ip",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "headers")) "inner_ipv4"]))
       (stmt_trans
          (e_select
             (e_struct
                [("",
                  e_acc (e_acc (e_var (varn_name "headers")) "inner_ipv4")
                    "protocol")])
             [([s_sing (v_bit ([F; F; F; F; F; F; F; T],8))],"parse_icmp");
              ([s_sing (v_bit ([F; F; F; F; F; T; T; F],8))],"parse_tcp");
              ([s_sing (v_bit ([F; F; F; T; F; F; F; T],8))],"parse_udp")]
             "accept")));
    ("parse_ipv6",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "headers")) "ipv6"]))
       (stmt_trans
          (e_select
             (e_struct
                [("",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv6")
                    "next_header")])
             [([s_sing (v_bit ([F; F; F; F; F; T; F; F],8))],
               "parse_ipv4_in_ip");
              ([s_sing (v_bit ([F; F; T; F; T; F; F; T],8))],
               "parse_ipv6_in_ip");
              ([s_sing (v_bit ([F; F; T; T; T; F; T; F],8))],"parse_icmp");
              ([s_sing (v_bit ([F; F; F; F; F; T; T; F],8))],"parse_tcp");
              ([s_sing (v_bit ([F; F; F; T; F; F; F; T],8))],"parse_udp")]
             "accept")));
    ("parse_ipv6_in_ip",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "headers")) "inner_ipv6"]))
       (stmt_trans
          (e_select
             (e_struct
                [("",
                  e_acc (e_acc (e_var (varn_name "headers")) "inner_ipv6")
                    "next_header")])
             [([s_sing (v_bit ([F; F; T; T; T; F; T; F],8))],"parse_icmp");
              ([s_sing (v_bit ([F; F; F; F; F; T; T; F],8))],"parse_tcp");
              ([s_sing (v_bit ([F; F; F; T; F; F; F; T],8))],"parse_udp")]
             "accept")));
    ("parse_tcp",
     stmt_seq
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "packet_in" "extract")
                [e_var (varn_name "packet");
                 e_acc (e_var (varn_name "headers")) "tcp"]))
          (stmt_seq
             (stmt_ass
                (lval_field (lval_varname (varn_name "local_metadata"))
                   "l4_src_port")
                (e_acc (e_acc (e_var (varn_name "headers")) "tcp") "src_port"))
             (stmt_ass
                (lval_field (lval_varname (varn_name "local_metadata"))
                   "l4_dst_port")
                (e_acc (e_acc (e_var (varn_name "headers")) "tcp") "dst_port"))))
       (stmt_trans (e_v (v_str "accept"))));
    ("parse_udp",
     stmt_seq
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "packet_in" "extract")
                [e_var (varn_name "packet");
                 e_acc (e_var (varn_name "headers")) "udp"]))
          (stmt_seq
             (stmt_ass
                (lval_field (lval_varname (varn_name "local_metadata"))
                   "l4_src_port")
                (e_acc (e_acc (e_var (varn_name "headers")) "udp") "src_port"))
             (stmt_ass
                (lval_field (lval_varname (varn_name "local_metadata"))
                   "l4_dst_port")
                (e_acc (e_acc (e_var (varn_name "headers")) "udp") "dst_port"))))
       (stmt_trans (e_v (v_str "accept"))));
    ("parse_icmp",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "headers")) "icmp"]))
       (stmt_trans (e_v (v_str "accept"))));
    ("parse_arp",
     stmt_seq
       (stmt_ass lval_null
          (e_call (funn_ext "packet_in" "extract")
             [e_var (varn_name "packet");
              e_acc (e_var (varn_name "headers")) "arp"]))
       (stmt_trans (e_v (v_str "accept"))))],[]);
  ("packet_deparser",pbl_type_control,[("packet",d_none); ("headers",d_in)],
   [("packet_deparser",
     stmt_seq stmt_empty
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "packet_out" "emit")
                [e_var (varn_name "packet");
                 e_acc (e_var (varn_name "headers")) "packet_out_header"]))
          (stmt_seq
             (stmt_ass lval_null
                (e_call (funn_ext "packet_out" "emit")
                   [e_var (varn_name "packet");
                    e_acc (e_var (varn_name "headers"))
                      "mirror_encap_ethernet"]))
             (stmt_seq
                (stmt_ass lval_null
                   (e_call (funn_ext "packet_out" "emit")
                      [e_var (varn_name "packet");
                       e_acc (e_var (varn_name "headers"))
                         "mirror_encap_vlan"]))
                (stmt_seq
                   (stmt_ass lval_null
                      (e_call (funn_ext "packet_out" "emit")
                         [e_var (varn_name "packet");
                          e_acc (e_var (varn_name "headers"))
                            "mirror_encap_ipv6"]))
                   (stmt_seq
                      (stmt_ass lval_null
                         (e_call (funn_ext "packet_out" "emit")
                            [e_var (varn_name "packet");
                             e_acc (e_var (varn_name "headers"))
                               "mirror_encap_udp"]))
                      (stmt_seq
                         (stmt_ass lval_null
                            (e_call (funn_ext "packet_out" "emit")
                               [e_var (varn_name "packet");
                                e_acc (e_var (varn_name "headers")) "ipfix"]))
                         (stmt_seq
                            (stmt_ass lval_null
                               (e_call (funn_ext "packet_out" "emit")
                                  [e_var (varn_name "packet");
                                   e_acc (e_var (varn_name "headers"))
                                     "psamp_extended"]))
                            (stmt_seq
                               (stmt_ass lval_null
                                  (e_call (funn_ext "packet_out" "emit")
                                     [e_var (varn_name "packet");
                                      e_acc (e_var (varn_name "headers"))
                                        "ethernet"]))
                               (stmt_seq
                                  (stmt_ass lval_null
                                     (e_call (funn_ext "packet_out" "emit")
                                        [e_var (varn_name "packet");
                                         e_acc (e_var (varn_name "headers"))
                                           "tunnel_encap_ipv6"]))
                                  (stmt_seq
                                     (stmt_ass lval_null
                                        (e_call
                                           (funn_ext "packet_out" "emit")
                                           [e_var (varn_name "packet");
                                            e_acc
                                              (e_var (varn_name "headers"))
                                              "tunnel_encap_gre"]))
                                     (stmt_seq
                                        (stmt_ass lval_null
                                           (e_call
                                              (funn_ext "packet_out" "emit")
                                              [e_var (varn_name "packet");
                                               e_acc
                                                 (e_var (varn_name "headers"))
                                                 "ipv4"]))
                                        (stmt_seq
                                           (stmt_ass lval_null
                                              (e_call
                                                 (funn_ext "packet_out"
                                                    "emit")
                                                 [e_var (varn_name "packet");
                                                  e_acc
                                                    (e_var
                                                       (varn_name "headers"))
                                                    "ipv6"]))
                                           (stmt_seq
                                              (stmt_ass lval_null
                                                 (e_call
                                                    (funn_ext "packet_out"
                                                       "emit")
                                                    [e_var
                                                       (varn_name "packet");
                                                     e_acc
                                                       (e_var
                                                          (varn_name
                                                             "headers"))
                                                       "inner_ipv4"]))
                                              (stmt_seq
                                                 (stmt_ass lval_null
                                                    (e_call
                                                       (funn_ext "packet_out"
                                                          "emit")
                                                       [e_var
                                                          (varn_name "packet");
                                                        e_acc
                                                          (e_var
                                                             (varn_name
                                                                "headers"))
                                                          "inner_ipv6"]))
                                                 (stmt_seq
                                                    (stmt_ass lval_null
                                                       (e_call
                                                          (funn_ext
                                                             "packet_out"
                                                             "emit")
                                                          [e_var
                                                             (varn_name
                                                                "packet");
                                                           e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "headers"))
                                                             "arp"]))
                                                    (stmt_seq
                                                       (stmt_ass lval_null
                                                          (e_call
                                                             (funn_ext
                                                                "packet_out"
                                                                "emit")
                                                             [e_var
                                                                (varn_name
                                                                   "packet");
                                                              e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "headers"))
                                                                "icmp"]))
                                                       (stmt_seq
                                                          (stmt_ass lval_null
                                                             (e_call
                                                                (funn_ext
                                                                   "packet_out"
                                                                   "emit")
                                                                [e_var
                                                                   (varn_name
                                                                      "packet");
                                                                 e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "headers"))
                                                                   "tcp"]))
                                                          (stmt_ass lval_null
                                                             (e_call
                                                                (funn_ext
                                                                   "packet_out"
                                                                   "emit")
                                                                [e_var
                                                                   (varn_name
                                                                      "packet");
                                                                 e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "headers"))
                                                                   "udp"]))))))))))))))))))),
     [])],[],[],[]);
  ("verify_ipv4_checksum",pbl_type_control,
   [("headers",d_inout); ("local_metadata",d_inout)],
   [("verify_ipv4_checksum",
     stmt_seq stmt_empty
       (stmt_ass lval_null
          (e_call (funn_ext "" "verify_checksum")
             [e_call (funn_ext "header" "isValid")
                [e_acc (e_var (varn_name "headers")) "ipv4"];
              e_struct
                [("1",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "version");
                 ("2",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4") "ihl");
                 ("3",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4") "dscp");
                 ("4",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4") "ecn");
                 ("5",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "total_len");
                 ("6",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "identification");
                 ("7",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "reserved");
                 ("8",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "do_not_fragment");
                 ("9",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "more_fragments");
                 ("10",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "frag_offset");
                 ("11",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4") "ttl");
                 ("12",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "protocol");
                 ("13",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "src_addr");
                 ("14",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "dst_addr")];
              e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                "header_checksum";
              e_v
                (v_bit
                   ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; F; F; F; T; T; F],32))])),[])],[],
   [],[]);
  ("compute_ipv4_checksum",pbl_type_control,
   [("headers",d_inout); ("local_metadata",d_inout)],
   [("compute_ipv4_checksum",
     stmt_seq stmt_empty
       (stmt_ass lval_null
          (e_call (funn_ext "" "update_checksum")
             [e_call (funn_ext "header" "isValid")
                [e_acc (e_var (varn_name "headers")) "ipv4"];
              e_struct
                [("1",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "version");
                 ("2",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4") "ihl");
                 ("3",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4") "dscp");
                 ("4",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4") "ecn");
                 ("5",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "total_len");
                 ("6",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "identification");
                 ("7",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "reserved");
                 ("8",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "do_not_fragment");
                 ("9",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "more_fragments");
                 ("10",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "frag_offset");
                 ("11",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4") "ttl");
                 ("12",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "protocol");
                 ("13",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "src_addr");
                 ("14",
                  e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                    "dst_addr")];
              e_acc (e_acc (e_var (varn_name "headers")) "ipv4")
                "header_checksum";
              e_v
                (v_bit
                   ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; F; F; F; T; T; F],32))])),[])],[],
   [],[]);
  ("ingress",pbl_type_control,
   [("headers",d_inout); ("local_metadata",d_inout);
    ("standard_metadata",d_inout)],
   [("ingress_cloning.ingress_clone",
     stmt_seq
       (stmt_cond (e_var (varn_name "ingress_cloning_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "ingress_cloning_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "ingress_cloning_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "" "clone_preserving_field_list")
                [e_v
                   (v_bit
                      ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                        F; F; F; F; F; F; F; F; F; F; F; F; F; F],32));
                 e_var (varn_name "ingress_cloning_clone_session");
                 e_v (v_bit ([F; F; F; F; F; F; F; T],8))]))
          (stmt_ret (e_v v_bot))),
     [("ingress_cloning_from_table",d_in); ("ingress_cloning_hit",d_in);
      ("ingress_cloning_clone_session",d_none)]);
    ("mirror_session_lookup.mirror_as_ipv4_erspan",
     stmt_seq
       (stmt_cond (e_var (varn_name "mirror_session_lookup_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "mirror_session_lookup_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var (varn_name "mirror_session_lookup_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; T],32)))]))
          stmt_empty) (stmt_seq stmt_empty (stmt_ret (e_v v_bot))),
     [("mirror_session_lookup_from_table",d_in);
      ("mirror_session_lookup_hit",d_in);
      ("mirror_session_lookup_port",d_none);
      ("mirror_session_lookup_src_ip",d_none);
      ("mirror_session_lookup_dst_ip",d_none);
      ("mirror_session_lookup_src_mac",d_none);
      ("mirror_session_lookup_dst_mac",d_none);
      ("mirror_session_lookup_ttl",d_none);
      ("mirror_session_lookup_tos",d_none)]);
    ("mirror_session_lookup.mirror_with_vlan_tag_and_ipfix_encapsulation",
     stmt_seq
       (stmt_cond (e_var (varn_name "mirror_session_lookup_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "mirror_session_lookup_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var (varn_name "mirror_session_lookup_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname
                      (varn_name "mirror_session_lookup_local_metadata"))
                   "mirror_egress_port")
                (e_var (varn_name "mirror_session_lookup_monitor_port")))
             (stmt_seq
                (stmt_ass
                   (lval_field
                      (lval_varname
                         (varn_name "mirror_session_lookup_local_metadata"))
                      "mirror_encap_src_mac")
                   (e_var
                      (varn_name "mirror_session_lookup_mirror_encap_src_mac")))
                (stmt_seq
                   (stmt_ass
                      (lval_field
                         (lval_varname
                            (varn_name "mirror_session_lookup_local_metadata"))
                         "mirror_encap_dst_mac")
                      (e_var
                         (varn_name
                            "mirror_session_lookup_mirror_encap_dst_mac")))
                   (stmt_seq
                      (stmt_ass
                         (lval_field
                            (lval_varname
                               (varn_name
                                  "mirror_session_lookup_local_metadata"))
                            "mirror_encap_vlan_id")
                         (e_var
                            (varn_name
                               "mirror_session_lookup_mirror_encap_vlan_id")))
                      (stmt_seq
                         (stmt_ass
                            (lval_field
                               (lval_varname
                                  (varn_name
                                     "mirror_session_lookup_local_metadata"))
                               "mirror_encap_src_ip")
                            (e_var
                               (varn_name
                                  "mirror_session_lookup_mirror_encap_src_ip")))
                         (stmt_seq
                            (stmt_ass
                               (lval_field
                                  (lval_varname
                                     (varn_name
                                        "mirror_session_lookup_local_metadata"))
                                  "mirror_encap_dst_ip")
                               (e_var
                                  (varn_name
                                     "mirror_session_lookup_mirror_encap_dst_ip")))
                            (stmt_seq
                               (stmt_ass
                                  (lval_field
                                     (lval_varname
                                        (varn_name
                                           "mirror_session_lookup_local_metadata"))
                                     "mirror_encap_udp_src_port")
                                  (e_var
                                     (varn_name
                                        "mirror_session_lookup_mirror_encap_udp_src_port")))
                               (stmt_ass
                                  (lval_field
                                     (lval_varname
                                        (varn_name
                                           "mirror_session_lookup_local_metadata"))
                                     "mirror_encap_udp_dst_port")
                                  (e_var
                                     (varn_name
                                        "mirror_session_lookup_mirror_encap_udp_dst_port"))))))))))
          (stmt_ret (e_v v_bot))),
     [("mirror_session_lookup_from_table",d_in);
      ("mirror_session_lookup_hit",d_in);
      ("mirror_session_lookup_monitor_port",d_none);
      ("mirror_session_lookup_monitor_failover_port",d_none);
      ("mirror_session_lookup_mirror_encap_src_mac",d_none);
      ("mirror_session_lookup_mirror_encap_dst_mac",d_none);
      ("mirror_session_lookup_mirror_encap_vlan_id",d_none);
      ("mirror_session_lookup_mirror_encap_src_ip",d_none);
      ("mirror_session_lookup_mirror_encap_dst_ip",d_none);
      ("mirror_session_lookup_mirror_encap_udp_src_port",d_none);
      ("mirror_session_lookup_mirror_encap_udp_dst_port",d_none)]);
    ("routing_resolution.set_dst_mac",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_resolution_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_resolution_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var (varn_name "routing_resolution_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field
                (lval_field
                   (lval_varname
                      (varn_name "routing_resolution_local_metadata"))
                   "packet_rewrites") "dst_mac")
             (e_var (varn_name "routing_resolution_dst_mac")))
          (stmt_ret (e_v v_bot))),
     [("routing_resolution_from_table",d_in);
      ("routing_resolution_hit",d_in); ("routing_resolution_dst_mac",d_none)]);
    ("routing_resolution.set_port_and_src_mac_and_vlan_id",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_resolution_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_resolution_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var (varn_name "routing_resolution_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname
                      (varn_name "routing_resolution_standard_metadata"))
                   "egress_spec")
                (e_cast (cast_unsigned 9)
                   (e_var (varn_name "routing_resolution_port"))))
             (stmt_seq
                (stmt_ass
                   (lval_field
                      (lval_field
                         (lval_varname
                            (varn_name "routing_resolution_local_metadata"))
                         "packet_rewrites") "src_mac")
                   (e_var (varn_name "routing_resolution_src_mac")))
                (stmt_ass
                   (lval_field
                      (lval_field
                         (lval_varname
                            (varn_name "routing_resolution_local_metadata"))
                         "packet_rewrites") "vlan_id")
                   (e_var (varn_name "routing_resolution_vlan_id")))))
          (stmt_ret (e_v v_bot))),
     [("routing_resolution_from_table",d_in);
      ("routing_resolution_hit",d_in); ("routing_resolution_port",d_none);
      ("routing_resolution_src_mac",d_none);
      ("routing_resolution_vlan_id",d_none)]);
    ("routing_resolution.set_port_and_src_mac",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_resolution_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_resolution_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var (varn_name "routing_resolution_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass lval_null
             (e_call
                (funn_name
                   "routing_resolution.set_port_and_src_mac_and_vlan_id")
                [e_var (varn_name "routing_resolution_from_table");
                 e_var (varn_name "routing_resolution_hit");
                 e_var (varn_name "routing_resolution_port");
                 e_var (varn_name "routing_resolution_src_mac");
                 e_v (v_bit ([T; T; T; T; T; T; T; T; T; T; T; T],12))]))
          (stmt_ret (e_v v_bot))),
     [("routing_resolution_from_table",d_in);
      ("routing_resolution_hit",d_in); ("routing_resolution_port",d_none);
      ("routing_resolution_src_mac",d_none)]);
    ("routing_resolution.set_ip_nexthop_and_disable_rewrites",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_resolution_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_resolution_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var (varn_name "routing_resolution_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; T; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_varname
                   (varn_name "routing_resolution_router_interface_id_valid"))
                (e_v (v_bool T)))
             (stmt_seq
                (stmt_ass
                   (lval_varname
                      (varn_name
                         "routing_resolution_router_interface_id_value"))
                   (e_var
                      (varn_name "routing_resolution_router_interface_id")))
                (stmt_seq
                   (stmt_ass
                      (lval_varname
                         (varn_name "routing_resolution_neighbor_id_valid"))
                      (e_v (v_bool T)))
                   (stmt_seq
                      (stmt_ass
                         (lval_varname
                            (varn_name "routing_resolution_neighbor_id_value"))
                         (e_var (varn_name "routing_resolution_neighbor_id")))
                      (stmt_seq
                         (stmt_ass
                            (lval_field
                               (lval_varname
                                  (varn_name
                                     "routing_resolution_local_metadata"))
                               "enable_decrement_ttl")
                            (e_unop unop_neg
                               (e_cast cast_bool
                                  (e_var
                                     (varn_name
                                        "routing_resolution_disable_decrement_ttl")))))
                         (stmt_seq
                            (stmt_ass
                               (lval_field
                                  (lval_varname
                                     (varn_name
                                        "routing_resolution_local_metadata"))
                                  "enable_src_mac_rewrite")
                               (e_unop unop_neg
                                  (e_cast cast_bool
                                     (e_var
                                        (varn_name
                                           "routing_resolution_disable_src_mac_rewrite")))))
                            (stmt_seq
                               (stmt_ass
                                  (lval_field
                                     (lval_varname
                                        (varn_name
                                           "routing_resolution_local_metadata"))
                                     "enable_dst_mac_rewrite")
                                  (e_unop unop_neg
                                     (e_cast cast_bool
                                        (e_var
                                           (varn_name
                                              "routing_resolution_disable_dst_mac_rewrite")))))
                               (stmt_ass
                                  (lval_field
                                     (lval_varname
                                        (varn_name
                                           "routing_resolution_local_metadata"))
                                     "enable_vlan_rewrite")
                                  (e_unop unop_neg
                                     (e_cast cast_bool
                                        (e_var
                                           (varn_name
                                              "routing_resolution_disable_vlan_rewrite"))))))))))))
          (stmt_ret (e_v v_bot))),
     [("routing_resolution_from_table",d_in);
      ("routing_resolution_hit",d_in);
      ("routing_resolution_router_interface_id",d_none);
      ("routing_resolution_neighbor_id",d_none);
      ("routing_resolution_disable_decrement_ttl",d_none);
      ("routing_resolution_disable_src_mac_rewrite",d_none);
      ("routing_resolution_disable_dst_mac_rewrite",d_none);
      ("routing_resolution_disable_vlan_rewrite",d_none)]);
    ("routing_resolution.set_ip_nexthop",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_resolution_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_resolution_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var (varn_name "routing_resolution_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass lval_null
             (e_call
                (funn_name
                   "routing_resolution.set_ip_nexthop_and_disable_rewrites")
                [e_var (varn_name "routing_resolution_from_table");
                 e_var (varn_name "routing_resolution_hit");
                 e_var (varn_name "routing_resolution_router_interface_id");
                 e_var (varn_name "routing_resolution_neighbor_id");
                 e_v (v_bit ([F],1)); e_v (v_bit ([F],1));
                 e_v (v_bit ([F],1)); e_v (v_bit ([F],1))]))
          (stmt_ret (e_v v_bot))),
     [("routing_resolution_from_table",d_in);
      ("routing_resolution_hit",d_in);
      ("routing_resolution_router_interface_id",d_none);
      ("routing_resolution_neighbor_id",d_none)]);
    ("routing_resolution.set_p2p_tunnel_encap_nexthop",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_resolution_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_resolution_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var (varn_name "routing_resolution_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; T; F; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_varname
                   (varn_name "routing_resolution_tunnel_id_valid"))
                (e_v (v_bool T)))
             (stmt_ass
                (lval_varname
                   (varn_name "routing_resolution_tunnel_id_value"))
                (e_var (varn_name "routing_resolution_tunnel_id"))))
          (stmt_ret (e_v v_bot))),
     [("routing_resolution_from_table",d_in);
      ("routing_resolution_hit",d_in);
      ("routing_resolution_tunnel_id",d_none)]);
    ("routing_resolution.mark_for_p2p_tunnel_encap",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_resolution_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_resolution_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var (varn_name "routing_resolution_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; T; F; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname
                      (varn_name "routing_resolution_local_metadata"))
                   "tunnel_encap_src_ipv6")
                (e_var (varn_name "routing_resolution_encap_src_ip")))
             (stmt_seq
                (stmt_ass
                   (lval_field
                      (lval_varname
                         (varn_name "routing_resolution_local_metadata"))
                      "tunnel_encap_dst_ipv6")
                   (e_var (varn_name "routing_resolution_encap_dst_ip")))
                (stmt_seq
                   (stmt_ass
                      (lval_field
                         (lval_varname
                            (varn_name "routing_resolution_local_metadata"))
                         "apply_tunnel_encap_at_egress") (e_v (v_bool T)))
                   (stmt_ass lval_null
                      (e_call (funn_name "routing_resolution.set_ip_nexthop")
                         [e_var (varn_name "routing_resolution_from_table");
                          e_var (varn_name "routing_resolution_hit");
                          e_var
                            (varn_name
                               "routing_resolution_router_interface_id");
                          e_var (varn_name "routing_resolution_encap_dst_ip")])))))
          (stmt_ret (e_v v_bot))),
     [("routing_resolution_from_table",d_in);
      ("routing_resolution_hit",d_in);
      ("routing_resolution_encap_src_ip",d_none);
      ("routing_resolution_encap_dst_ip",d_none);
      ("routing_resolution_router_interface_id",d_none)]);
    ("acl_ingress.acl_copy",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass lval_null
                (e_call (funn_ext "direct_counter" "count")
                   [e_var (varn_name "acl_ingress_acl_ingress_counter")]))
             (stmt_seq
                (stmt_ass lval_null
                   (e_call (funn_ext "direct_meter" "read")
                      [e_var (varn_name "acl_ingress_acl_ingress_meter");
                       e_acc (e_var (varn_name "acl_ingress_local_metadata"))
                         "color"]))
                (stmt_ass
                   (lval_field
                      (lval_varname (varn_name "acl_ingress_local_metadata"))
                      "marked_to_copy") (e_v (v_bool T)))))
          (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in);
      ("acl_ingress_qos_queue",d_none)]);
    ("acl_ingress.acl_trap",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass lval_null
                (e_call (funn_name "acl_ingress.acl_copy")
                   [e_var (varn_name "acl_ingress_from_table");
                    e_var (varn_name "acl_ingress_hit");
                    e_var (varn_name "acl_ingress_qos_queue")]))
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "acl_ingress_local_metadata"))
                   "acl_drop") (e_v (v_bool T)))) (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in);
      ("acl_ingress_qos_queue",d_none)]);
    ("acl_ingress.acl_forward",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; T; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "direct_meter" "read")
                [e_var (varn_name "acl_ingress_acl_ingress_meter");
                 e_acc (e_var (varn_name "acl_ingress_local_metadata"))
                   "color"])) (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in)]);
    ("acl_ingress.acl_count",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "direct_counter" "count")
                [e_var (varn_name "acl_ingress_acl_ingress_counting_counter")]))
          (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in)]);
    ("acl_ingress.acl_mirror",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; T; F; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass lval_null
                (e_call (funn_ext "direct_counter" "count")
                   [e_var (varn_name "acl_ingress_acl_ingress_counter")]))
             (stmt_seq
                (stmt_ass
                   (lval_field
                      (lval_varname (varn_name "acl_ingress_local_metadata"))
                      "marked_to_mirror") (e_v (v_bool T)))
                (stmt_ass
                   (lval_field
                      (lval_varname (varn_name "acl_ingress_local_metadata"))
                      "mirror_session_id")
                   (e_var (varn_name "acl_ingress_mirror_session_id")))))
          (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in);
      ("acl_ingress_mirror_session_id",d_none)]);
    ("acl_ingress.set_qos_queue_and_cancel_copy_above_rate_limit",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; T; F; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "direct_meter" "read")
                [e_var (varn_name "acl_ingress_acl_ingress_qos_meter");
                 e_acc (e_var (varn_name "acl_ingress_local_metadata"))
                   "color"])) (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in);
      ("acl_ingress_qos_queue",d_none)]);
    ("acl_ingress.set_cpu_and_multicast_queues_and_deny_above_rate_limit",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; T; F; T; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "direct_meter" "read")
                [e_var (varn_name "acl_ingress_acl_ingress_qos_meter");
                 e_acc (e_var (varn_name "acl_ingress_local_metadata"))
                   "color"])) (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in);
      ("acl_ingress_cpu_queue",d_none);
      ("acl_ingress_green_multicast_queue",d_none);
      ("acl_ingress_red_multicast_queue",d_none)]);
    ("acl_ingress.set_cpu_queue_and_deny_above_rate_limit",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; T; F; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "direct_meter" "read")
                [e_var (varn_name "acl_ingress_acl_ingress_qos_meter");
                 e_acc (e_var (varn_name "acl_ingress_local_metadata"))
                   "color"])) (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in);
      ("acl_ingress_cpu_queue",d_none)]);
    ("acl_ingress.set_cpu_queue",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; T; T; F; F],32)))]))
          stmt_empty) (stmt_seq stmt_empty (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in);
      ("acl_ingress_cpu_queue",d_none)]);
    ("acl_ingress.acl_deny",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; T; T; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass (lval_varname (varn_name "acl_ingress_cancel_copy"))
                (e_v (v_bool T)))
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "acl_ingress_local_metadata"))
                   "acl_drop") (e_v (v_bool T)))) (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in)]);
    ("acl_ingress.redirect_to_nexthop",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; T; T; T; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "acl_ingress_local_metadata"))
                   "nexthop_id_valid") (e_v (v_bool T)))
             (stmt_seq
                (stmt_ass
                   (lval_field
                      (lval_varname (varn_name "acl_ingress_local_metadata"))
                      "nexthop_id_value")
                   (e_var (varn_name "acl_ingress_nexthop_id")))
                (stmt_seq
                   (stmt_ass
                      (lval_field
                         (lval_varname
                            (varn_name "acl_ingress_local_metadata"))
                         "wcmp_group_id_valid") (e_v (v_bool F)))
                   (stmt_ass
                      (lval_field
                         (lval_varname
                            (varn_name "acl_ingress_standard_metadata"))
                         "mcast_grp")
                      (e_v
                         (v_bit
                            ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F],
                             16))))))) (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in);
      ("acl_ingress_nexthop_id",d_none)]);
    ("acl_ingress.redirect_to_ipmc_group",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; T; T; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "acl_ingress_standard_metadata"))
                   "mcast_grp")
                (e_var (varn_name "acl_ingress_multicast_group_id")))
             (stmt_seq
                (stmt_ass
                   (lval_field
                      (lval_varname (varn_name "acl_ingress_local_metadata"))
                      "nexthop_id_valid") (e_v (v_bool F)))
                (stmt_ass
                   (lval_field
                      (lval_varname (varn_name "acl_ingress_local_metadata"))
                      "wcmp_group_id_valid") (e_v (v_bool F)))))
          (stmt_ret (e_v v_bot))),
     [("acl_ingress_from_table",d_in); ("acl_ingress_hit",d_in);
      ("acl_ingress_multicast_group_id",d_none)]);
    ("routing_lookup.drop",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_lookup_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_lookup_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "routing_lookup_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "" "mark_to_drop")
                [e_var (varn_name "routing_lookup_standard_metadata")]))
          (stmt_ret (e_v v_bot))),
     [("routing_lookup_from_table",d_in); ("routing_lookup_hit",d_in)]);
    ("routing_lookup.set_wcmp_group_id",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_lookup_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_lookup_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "routing_lookup_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "routing_lookup_local_metadata"))
                   "wcmp_group_id_valid") (e_v (v_bool T)))
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "routing_lookup_local_metadata"))
                   "wcmp_group_id_value")
                (e_var (varn_name "routing_lookup_wcmp_group_id"))))
          (stmt_ret (e_v v_bot))),
     [("routing_lookup_from_table",d_in); ("routing_lookup_hit",d_in);
      ("routing_lookup_wcmp_group_id",d_none)]);
    ("routing_lookup.set_wcmp_group_id_and_metadata",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_lookup_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_lookup_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "routing_lookup_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass lval_null
                (e_call (funn_name "routing_lookup.set_wcmp_group_id")
                   [e_var (varn_name "routing_lookup_from_table");
                    e_var (varn_name "routing_lookup_hit");
                    e_var (varn_name "routing_lookup_wcmp_group_id")]))
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "routing_lookup_local_metadata"))
                   "route_metadata")
                (e_var (varn_name "routing_lookup_route_metadata"))))
          (stmt_ret (e_v v_bot))),
     [("routing_lookup_from_table",d_in); ("routing_lookup_hit",d_in);
      ("routing_lookup_wcmp_group_id",d_none);
      ("routing_lookup_route_metadata",d_none)]);
    ("routing_lookup.set_metadata_and_drop",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_lookup_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_lookup_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "routing_lookup_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; T; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "routing_lookup_local_metadata"))
                   "route_metadata")
                (e_var (varn_name "routing_lookup_route_metadata")))
             (stmt_ass lval_null
                (e_call (funn_ext "" "mark_to_drop")
                   [e_var (varn_name "routing_lookup_standard_metadata")])))
          (stmt_ret (e_v v_bot))),
     [("routing_lookup_from_table",d_in); ("routing_lookup_hit",d_in);
      ("routing_lookup_route_metadata",d_none)]);
    ("routing_lookup.set_nexthop_id_and_metadata",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_lookup_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_lookup_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "routing_lookup_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "routing_lookup_local_metadata"))
                   "nexthop_id_valid") (e_v (v_bool T)))
             (stmt_seq
                (stmt_ass
                   (lval_field
                      (lval_varname
                         (varn_name "routing_lookup_local_metadata"))
                      "nexthop_id_value")
                   (e_var (varn_name "routing_lookup_nexthop_id")))
                (stmt_ass
                   (lval_field
                      (lval_varname
                         (varn_name "routing_lookup_local_metadata"))
                      "route_metadata")
                   (e_var (varn_name "routing_lookup_route_metadata")))))
          (stmt_ret (e_v v_bot))),
     [("routing_lookup_from_table",d_in); ("routing_lookup_hit",d_in);
      ("routing_lookup_nexthop_id",d_none);
      ("routing_lookup_route_metadata",d_none)]);
    ("routing_lookup.set_multicast_group_id",
     stmt_seq
       (stmt_cond (e_var (varn_name "routing_lookup_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "routing_lookup_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "routing_lookup_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; T; F; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field
                (lval_varname (varn_name "routing_lookup_standard_metadata"))
                "mcast_grp")
             (e_var (varn_name "routing_lookup_multicast_group_id")))
          (stmt_ret (e_v v_bot))),
     [("routing_lookup_from_table",d_in); ("routing_lookup_hit",d_in);
      ("routing_lookup_multicast_group_id",d_none)]);
    ("l3_admit.admit_to_l3",
     stmt_seq
       (stmt_cond (e_var (varn_name "l3_admit_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "l3_admit_hit"));
                 ("miss",e_unop unop_neg (e_var (varn_name "l3_admit_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field (lval_varname (varn_name "l3_admit_local_metadata"))
                "admit_to_l3") (e_v (v_bool T))) (stmt_ret (e_v v_bot))),
     [("l3_admit_from_table",d_in); ("l3_admit_hit",d_in)]);
    ("tunnel_termination.tunnel_decap",
     stmt_seq
       (stmt_cond (e_var (varn_name "tunnel_termination_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "tunnel_termination_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var (varn_name "tunnel_termination_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_varname
                (varn_name "tunnel_termination_marked_for_ip_in_ipv6_decap"))
             (e_v (v_bool T))) (stmt_ret (e_v v_bot))),
     [("tunnel_termination_from_table",d_in);
      ("tunnel_termination_hit",d_in)]);
    ("acl_pre_ingress.set_vrf",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_pre_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_pre_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_pre_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "acl_pre_ingress_local_metadata"))
                   "vrf_id") (e_var (varn_name "acl_pre_ingress_vrf_id")))
             (stmt_ass lval_null
                (e_call (funn_ext "direct_counter" "count")
                   [e_var
                      (varn_name "acl_pre_ingress_acl_pre_ingress_counter")])))
          (stmt_ret (e_v v_bot))),
     [("acl_pre_ingress_from_table",d_in); ("acl_pre_ingress_hit",d_in);
      ("acl_pre_ingress_vrf_id",d_none)]);
    ("acl_pre_ingress.set_outer_vlan_id",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_pre_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_pre_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_pre_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "acl_pre_ingress_local_metadata"))
                   "vlan_id") (e_var (varn_name "acl_pre_ingress_vlan_id")))
             (stmt_ass lval_null
                (e_call (funn_ext "direct_counter" "count")
                   [e_var
                      (varn_name
                         "acl_pre_ingress_acl_pre_ingress_vlan_counter")])))
          (stmt_ret (e_v v_bot))),
     [("acl_pre_ingress_from_table",d_in); ("acl_pre_ingress_hit",d_in);
      ("acl_pre_ingress_vlan_id",d_none)]);
    ("acl_pre_ingress.set_acl_metadata",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_pre_ingress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_pre_ingress_hit"));
                 ("miss",
                  e_unop unop_neg (e_var (varn_name "acl_pre_ingress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; T; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname (varn_name "acl_pre_ingress_local_metadata"))
                   "acl_metadata")
                (e_var (varn_name "acl_pre_ingress_acl_metadata")))
             (stmt_ass lval_null
                (e_call (funn_ext "direct_counter" "count")
                   [e_var
                      (varn_name
                         "acl_pre_ingress_acl_pre_ingress_metadata_counter")])))
          (stmt_ret (e_v v_bot))),
     [("acl_pre_ingress_from_table",d_in); ("acl_pre_ingress_hit",d_in);
      ("acl_pre_ingress_acl_metadata",d_none)]);
    ("vlan_untag.disable_vlan_checks",
     stmt_seq
       (stmt_cond (e_var (varn_name "vlan_untag_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "vlan_untag_hit"));
                 ("miss",e_unop unop_neg (e_var (varn_name "vlan_untag_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass
             (lval_field
                (lval_varname (varn_name "vlan_untag_local_metadata"))
                "enable_vlan_checks") (e_v (v_bool F)))
          (stmt_ret (e_v v_bot))),
     [("vlan_untag_from_table",d_in); ("vlan_untag_hit",d_in)]);
    ("ingress",
     stmt_seq stmt_empty
       (stmt_seq
          (stmt_seq
             (stmt_seq
                (stmt_seq
                   (stmt_ass
                      (lval_varname (varn_name "packet_out_decap_headers"))
                      (e_var (varn_name "headers")))
                   (stmt_ass
                      (lval_varname
                         (varn_name "packet_out_decap_local_metadata"))
                      (e_var (varn_name "local_metadata"))))
                (stmt_ass
                   (lval_varname
                      (varn_name "packet_out_decap_standard_metadata"))
                   (e_var (varn_name "standard_metadata"))))
             (stmt_seq
                (stmt_seq stmt_empty
                   (stmt_seq
                      (stmt_cond
                         (e_binop
                            (e_call (funn_ext "header" "isValid")
                               [e_acc
                                  (e_var
                                     (varn_name "packet_out_decap_headers"))
                                  "packet_out_header"]) binop_bin_and
                            (e_binop
                               (e_acc
                                  (e_acc
                                     (e_var
                                        (varn_name "packet_out_decap_headers"))
                                     "packet_out_header") "submit_to_ingress")
                               binop_eq (e_v (v_bit ([F],1)))))
                         (stmt_block []
                            (stmt_seq
                               (stmt_ass
                                  (lval_field
                                     (lval_varname
                                        (varn_name
                                           "packet_out_decap_standard_metadata"))
                                     "egress_spec")
                                  (e_cast (cast_unsigned 9)
                                     (e_acc
                                        (e_acc
                                           (e_var
                                              (varn_name
                                                 "packet_out_decap_headers"))
                                           "packet_out_header") "egress_port")))
                               (stmt_ass
                                  (lval_field
                                     (lval_varname
                                        (varn_name
                                           "packet_out_decap_local_metadata"))
                                     "bypass_ingress") (e_v (v_bool T)))))
                         stmt_empty)
                      (stmt_ass lval_null
                         (e_call (funn_ext "header" "setInvalid")
                            [e_acc
                               (e_var (varn_name "packet_out_decap_headers"))
                               "packet_out_header"]))))
                (stmt_seq
                   (stmt_seq
                      (stmt_ass (lval_varname (varn_name "headers"))
                         (e_var (varn_name "packet_out_decap_headers")))
                      (stmt_ass (lval_varname (varn_name "local_metadata"))
                         (e_var (varn_name "packet_out_decap_local_metadata"))))
                   (stmt_ass (lval_varname (varn_name "standard_metadata"))
                      (e_var (varn_name "packet_out_decap_standard_metadata"))))))
          (stmt_cond
             (e_unop unop_neg
                (e_acc (e_var (varn_name "local_metadata")) "bypass_ingress"))
             (stmt_block []
                (stmt_seq
                   (stmt_seq
                      (stmt_seq
                         (stmt_seq
                            (stmt_ass
                               (lval_varname (varn_name "vlan_untag_headers"))
                               (e_var (varn_name "headers")))
                            (stmt_ass
                               (lval_varname
                                  (varn_name "vlan_untag_local_metadata"))
                               (e_var (varn_name "local_metadata"))))
                         (stmt_ass
                            (lval_varname
                               (varn_name "vlan_untag_standard_metadata"))
                            (e_var (varn_name "standard_metadata"))))
                      (stmt_seq
                         (stmt_seq stmt_empty
                            (stmt_seq
                               (stmt_cond
                                  (e_call (funn_ext "header" "isValid")
                                     [e_acc
                                        (e_var
                                           (varn_name "vlan_untag_headers"))
                                        "vlan"])
                                  (stmt_block []
                                     (stmt_seq
                                        (stmt_ass
                                           (lval_field
                                              (lval_varname
                                                 (varn_name
                                                    "vlan_untag_local_metadata"))
                                              "vlan_id")
                                           (e_acc
                                              (e_acc
                                                 (e_var
                                                    (varn_name
                                                       "vlan_untag_headers"))
                                                 "vlan") "vlan_id"))
                                        (stmt_seq
                                           (stmt_ass
                                              (lval_field
                                                 (lval_field
                                                    (lval_varname
                                                       (varn_name
                                                          "vlan_untag_headers"))
                                                    "ethernet") "ether_type")
                                              (e_acc
                                                 (e_acc
                                                    (e_var
                                                       (varn_name
                                                          "vlan_untag_headers"))
                                                    "vlan") "ether_type"))
                                           (stmt_ass lval_null
                                              (e_call
                                                 (funn_ext "header"
                                                    "setInvalid")
                                                 [e_acc
                                                    (e_var
                                                       (varn_name
                                                          "vlan_untag_headers"))
                                                    "vlan"])))))
                                  (stmt_block []
                                     (stmt_ass
                                        (lval_field
                                           (lval_varname
                                              (varn_name
                                                 "vlan_untag_local_metadata"))
                                           "vlan_id")
                                        (e_v
                                           (v_bit
                                              ([T; T; T; T; T; T; T; T; T; T;
                                                T; T],12))))))
                               (stmt_seq
                                  (stmt_ass
                                     (lval_field
                                        (lval_varname
                                           (varn_name
                                              "vlan_untag_local_metadata"))
                                        "enable_vlan_checks")
                                     (e_v (v_bool T)))
                                  (stmt_app
                                     "vlan_untag.disable_vlan_checks_table"
                                     [e_v (v_bit ([T],1))]))))
                         (stmt_seq
                            (stmt_seq
                               (stmt_ass (lval_varname (varn_name "headers"))
                                  (e_var (varn_name "vlan_untag_headers")))
                               (stmt_ass
                                  (lval_varname (varn_name "local_metadata"))
                                  (e_var
                                     (varn_name "vlan_untag_local_metadata"))))
                            (stmt_ass
                               (lval_varname (varn_name "standard_metadata"))
                               (e_var
                                  (varn_name "vlan_untag_standard_metadata"))))))
                   (stmt_seq
                      (stmt_seq
                         (stmt_seq
                            (stmt_seq
                               (stmt_ass
                                  (lval_varname
                                     (varn_name "acl_pre_ingress_headers"))
                                  (e_var (varn_name "headers")))
                               (stmt_ass
                                  (lval_varname
                                     (varn_name
                                        "acl_pre_ingress_local_metadata"))
                                  (e_var (varn_name "local_metadata"))))
                            (stmt_ass
                               (lval_varname
                                  (varn_name
                                     "acl_pre_ingress_standard_metadata"))
                               (e_var (varn_name "standard_metadata"))))
                         (stmt_seq
                            (stmt_seq
                               (stmt_seq
                                  (stmt_seq
                                     (stmt_seq
                                        (stmt_seq
                                           (stmt_seq
                                              (stmt_seq stmt_empty
                                                 (stmt_ass
                                                    (lval_varname
                                                       (varn_name
                                                          "acl_pre_ingress_dscp"))
                                                    (e_v
                                                       (v_bit
                                                          ([F; F; F; F; F; F],
                                                           6)))))
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "acl_pre_ingress_ecn"))
                                                 (e_v (v_bit ([F; F],2)))))
                                           (stmt_ass
                                              (lval_varname
                                                 (varn_name
                                                    "acl_pre_ingress_ip_protocol"))
                                              (e_v
                                                 (v_bit
                                                    ([F; F; F; F; F; F; F; F],
                                                     8)))))
                                        (stmt_ass lval_null
                                           (e_call
                                              (funn_inst "direct_counter")
                                              [e_var
                                                 (varn_name
                                                    "acl_pre_ingress_acl_pre_ingress_counter");
                                               e_v
                                                 (v_bit
                                                    ([F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; T; F],
                                                     32))])))
                                     (stmt_ass lval_null
                                        (e_call (funn_inst "direct_counter")
                                           [e_var
                                              (varn_name
                                                 "acl_pre_ingress_acl_pre_ingress_vlan_counter");
                                            e_v
                                              (v_bit
                                                 ([F; F; F; F; F; F; F; F; F;
                                                   F; F; F; F; F; F; F; F; F;
                                                   F; F; F; F; F; F; F; F; F;
                                                   F; F; F; T; F],32))])))
                                  (stmt_ass lval_null
                                     (e_call (funn_inst "direct_counter")
                                        [e_var
                                           (varn_name
                                              "acl_pre_ingress_acl_pre_ingress_metadata_counter");
                                         e_v
                                           (v_bit
                                              ([F; F; F; F; F; F; F; F; F; F;
                                                F; F; F; F; F; F; F; F; F; F;
                                                F; F; F; F; F; F; F; F; F; F;
                                                T; F],32))])))
                               (stmt_seq
                                  (stmt_cond
                                     (e_call (funn_ext "header" "isValid")
                                        [e_acc
                                           (e_var
                                              (varn_name
                                                 "acl_pre_ingress_headers"))
                                           "ipv4"])
                                     (stmt_block []
                                        (stmt_seq
                                           (stmt_ass
                                              (lval_varname
                                                 (varn_name
                                                    "acl_pre_ingress_dscp"))
                                              (e_acc
                                                 (e_acc
                                                    (e_var
                                                       (varn_name
                                                          "acl_pre_ingress_headers"))
                                                    "ipv4") "dscp"))
                                           (stmt_seq
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "acl_pre_ingress_ecn"))
                                                 (e_acc
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "acl_pre_ingress_headers"))
                                                       "ipv4") "ecn"))
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "acl_pre_ingress_ip_protocol"))
                                                 (e_acc
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "acl_pre_ingress_headers"))
                                                       "ipv4") "protocol")))))
                                     (stmt_cond
                                        (e_call (funn_ext "header" "isValid")
                                           [e_acc
                                              (e_var
                                                 (varn_name
                                                    "acl_pre_ingress_headers"))
                                              "ipv6"])
                                        (stmt_block []
                                           (stmt_seq
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "acl_pre_ingress_dscp"))
                                                 (e_acc
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "acl_pre_ingress_headers"))
                                                       "ipv6") "dscp"))
                                              (stmt_seq
                                                 (stmt_ass
                                                    (lval_varname
                                                       (varn_name
                                                          "acl_pre_ingress_ecn"))
                                                    (e_acc
                                                       (e_acc
                                                          (e_var
                                                             (varn_name
                                                                "acl_pre_ingress_headers"))
                                                          "ipv6") "ecn"))
                                                 (stmt_ass
                                                    (lval_varname
                                                       (varn_name
                                                          "acl_pre_ingress_ip_protocol"))
                                                    (e_acc
                                                       (e_acc
                                                          (e_var
                                                             (varn_name
                                                                "acl_pre_ingress_headers"))
                                                          "ipv6")
                                                       "next_header")))))
                                        stmt_empty))
                                  (stmt_app
                                     "acl_pre_ingress.acl_pre_ingress_table"
                                     [e_binop
                                        (e_call (funn_ext "header" "isValid")
                                           [e_acc
                                              (e_var
                                                 (varn_name
                                                    "acl_pre_ingress_headers"))
                                              "ipv4"]) binop_bin_or
                                        (e_call (funn_ext "header" "isValid")
                                           [e_acc
                                              (e_var
                                                 (varn_name
                                                    "acl_pre_ingress_headers"))
                                              "ipv6"]);
                                      e_call (funn_ext "header" "isValid")
                                        [e_acc
                                           (e_var
                                              (varn_name
                                                 "acl_pre_ingress_headers"))
                                           "ipv4"];
                                      e_call (funn_ext "header" "isValid")
                                        [e_acc
                                           (e_var
                                              (varn_name
                                                 "acl_pre_ingress_headers"))
                                           "ipv6"];
                                      e_acc
                                        (e_acc
                                           (e_var
                                              (varn_name
                                                 "acl_pre_ingress_headers"))
                                           "ethernet") "src_addr";
                                      e_acc
                                        (e_acc
                                           (e_var
                                              (varn_name
                                                 "acl_pre_ingress_headers"))
                                           "ethernet") "dst_addr";
                                      e_acc
                                        (e_acc
                                           (e_var
                                              (varn_name
                                                 "acl_pre_ingress_headers"))
                                           "ipv4") "dst_addr";
                                      e_slice
                                        (e_acc
                                           (e_acc
                                              (e_var
                                                 (varn_name
                                                    "acl_pre_ingress_headers"))
                                              "ipv6") "dst_addr")
                                        (e_v
                                           (v_bit
                                              ([F; F; F; F; F; F; F; F; F; T;
                                                T; T; T; T; T; T],16)))
                                        (e_v
                                           (v_bit
                                              ([F; F; F; F; F; F; F; F; F; T;
                                                F; F; F; F; F; F],16)));
                                      e_var
                                        (varn_name "acl_pre_ingress_dscp");
                                      e_var (varn_name "acl_pre_ingress_ecn");
                                      e_acc
                                        (e_var
                                           (varn_name
                                              "acl_pre_ingress_local_metadata"))
                                        "ingress_port"])))
                            (stmt_ass
                               (lval_varname (varn_name "local_metadata"))
                               (e_var
                                  (varn_name "acl_pre_ingress_local_metadata")))))
                      (stmt_seq
                         (stmt_seq
                            (stmt_seq
                               (stmt_seq
                                  (stmt_ass
                                     (lval_varname
                                        (varn_name
                                           "ingress_vlan_checks_headers"))
                                     (e_var (varn_name "headers")))
                                  (stmt_ass
                                     (lval_varname
                                        (varn_name
                                           "ingress_vlan_checks_local_metadata"))
                                     (e_var (varn_name "local_metadata"))))
                               (stmt_ass
                                  (lval_varname
                                     (varn_name
                                        "ingress_vlan_checks_standard_metadata"))
                                  (e_var (varn_name "standard_metadata"))))
                            (stmt_seq
                               (stmt_seq stmt_empty
                                  (stmt_cond
                                     (e_binop
                                        (e_acc
                                           (e_var
                                              (varn_name
                                                 "ingress_vlan_checks_local_metadata"))
                                           "enable_vlan_checks")
                                        binop_bin_and
                                        (e_unop unop_neg
                                           (e_binop
                                              (e_binop
                                                 (e_acc
                                                    (e_var
                                                       (varn_name
                                                          "ingress_vlan_checks_local_metadata"))
                                                    "vlan_id") binop_eq
                                                 (e_v
                                                    (v_bit
                                                       ([F; F; F; F; F; F; F;
                                                         F; F; F; F; F],12))))
                                              binop_bin_or
                                              (e_binop
                                                 (e_acc
                                                    (e_var
                                                       (varn_name
                                                          "ingress_vlan_checks_local_metadata"))
                                                    "vlan_id") binop_eq
                                                 (e_v
                                                    (v_bit
                                                       ([T; T; T; T; T; T; T;
                                                         T; T; T; T; T],12)))))))
                                     (stmt_block []
                                        (stmt_ass lval_null
                                           (e_call
                                              (funn_ext "" "mark_to_drop")
                                              [e_var
                                                 (varn_name
                                                    "ingress_vlan_checks_standard_metadata")])))
                                     stmt_empty))
                               (stmt_seq
                                  (stmt_seq
                                     (stmt_ass
                                        (lval_varname (varn_name "headers"))
                                        (e_var
                                           (varn_name
                                              "ingress_vlan_checks_headers")))
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name "local_metadata"))
                                        (e_var
                                           (varn_name
                                              "ingress_vlan_checks_local_metadata"))))
                                  (stmt_ass
                                     (lval_varname
                                        (varn_name "standard_metadata"))
                                     (e_var
                                        (varn_name
                                           "ingress_vlan_checks_standard_metadata"))))))
                         (stmt_seq
                            (stmt_seq
                               (stmt_seq
                                  (stmt_ass
                                     (lval_varname
                                        (varn_name
                                           "tunnel_termination_headers"))
                                     (e_var (varn_name "headers")))
                                  (stmt_ass
                                     (lval_varname
                                        (varn_name
                                           "tunnel_termination_local_metadata"))
                                     (e_var (varn_name "local_metadata"))))
                               (stmt_seq
                                  (stmt_seq
                                     (stmt_seq stmt_empty
                                        (stmt_ass
                                           (lval_varname
                                              (varn_name
                                                 "tunnel_termination_marked_for_ip_in_ipv6_decap"))
                                           (e_v (v_bool F))))
                                     (stmt_seq
                                        (stmt_cond
                                           (e_call
                                              (funn_ext "header" "isValid")
                                              [e_acc
                                                 (e_var
                                                    (varn_name
                                                       "tunnel_termination_headers"))
                                                 "ipv6"])
                                           (stmt_block []
                                              (stmt_cond
                                                 (e_binop
                                                    (e_binop
                                                       (e_acc
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "tunnel_termination_headers"))
                                                             "ipv6")
                                                          "next_header")
                                                       binop_eq
                                                       (e_v
                                                          (v_bit
                                                             ([F; F; F; F; F;
                                                               T; F; F],8))))
                                                    binop_bin_or
                                                    (e_binop
                                                       (e_acc
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "tunnel_termination_headers"))
                                                             "ipv6")
                                                          "next_header")
                                                       binop_eq
                                                       (e_v
                                                          (v_bit
                                                             ([F; F; T; F; T;
                                                               F; F; T],8)))))
                                                 (stmt_block []
                                                    (stmt_app
                                                       "tunnel_termination.ipv6_tunnel_termination_table"
                                                       [e_acc
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "tunnel_termination_headers"))
                                                             "ipv6")
                                                          "dst_addr";
                                                        e_acc
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "tunnel_termination_headers"))
                                                             "ipv6")
                                                          "src_addr"]))
                                                 stmt_empty)) stmt_empty)
                                        (stmt_cond
                                           (e_var
                                              (varn_name
                                                 "tunnel_termination_marked_for_ip_in_ipv6_decap"))
                                           (stmt_block []
                                              (stmt_seq
                                                 (stmt_ass lval_null
                                                    (e_call
                                                       (funn_ext "" "assert")
                                                       [e_call
                                                          (funn_ext "header"
                                                             "isValid")
                                                          [e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "tunnel_termination_headers"))
                                                             "ipv6"]]))
                                                 (stmt_seq
                                                    (stmt_ass lval_null
                                                       (e_call
                                                          (funn_ext ""
                                                             "assert")
                                                          [e_binop
                                                             (e_binop
                                                                (e_call
                                                                   (funn_ext
                                                                      "header"
                                                                      "isValid")
                                                                   [e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "tunnel_termination_headers"))
                                                                      "inner_ipv4"])
                                                                binop_bin_and
                                                                (e_unop
                                                                   unop_neg
                                                                   (e_call
                                                                      (funn_ext
                                                                         "header"
                                                                         "isValid")
                                                                      [e_acc
                                                                         (e_var
                                                                            (varn_name
                                                                               "tunnel_termination_headers"))
                                                                         "inner_ipv6"])))
                                                             binop_bin_or
                                                             (e_binop
                                                                (e_unop
                                                                   unop_neg
                                                                   (e_call
                                                                      (funn_ext
                                                                         "header"
                                                                         "isValid")
                                                                      [e_acc
                                                                         (e_var
                                                                            (varn_name
                                                                               "tunnel_termination_headers"))
                                                                         "inner_ipv4"]))
                                                                binop_bin_and
                                                                (e_call
                                                                   (funn_ext
                                                                      "header"
                                                                      "isValid")
                                                                   [e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "tunnel_termination_headers"))
                                                                      "inner_ipv6"]))]))
                                                    (stmt_seq
                                                       (stmt_ass lval_null
                                                          (e_call
                                                             (funn_ext
                                                                "header"
                                                                "setInvalid")
                                                             [e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "tunnel_termination_headers"))
                                                                "ipv6"]))
                                                       (stmt_seq
                                                          (stmt_cond
                                                             (e_call
                                                                (funn_ext
                                                                   "header"
                                                                   "isValid")
                                                                [e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "tunnel_termination_headers"))
                                                                   "inner_ipv4"])
                                                             (stmt_block []
                                                                (stmt_seq
                                                                   (stmt_ass
                                                                      (lval_field
                                                                         (lval_field
                                                                            (lval_varname
                                                                               (varn_name
                                                                                  "tunnel_termination_headers"))
                                                                            "ethernet")
                                                                         "ether_type")
                                                                      (e_v
                                                                         (v_bit
                                                                            ([F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              T;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F],
                                                                             16))))
                                                                   (stmt_seq
                                                                      (stmt_ass
                                                                         (lval_field
                                                                            (lval_varname
                                                                               (varn_name
                                                                                  "tunnel_termination_headers"))
                                                                            "ipv4")
                                                                         (e_acc
                                                                            (e_var
                                                                               (varn_name
                                                                                  "tunnel_termination_headers"))
                                                                            "inner_ipv4"))
                                                                      (stmt_ass
                                                                         lval_null
                                                                         (e_call
                                                                            (funn_ext
                                                                               "header"
                                                                               "setInvalid")
                                                                            [e_acc
                                                                               (e_var
                                                                                  (varn_name
                                                                                     "tunnel_termination_headers"))
                                                                               "inner_ipv4"])))))
                                                             stmt_empty)
                                                          (stmt_cond
                                                             (e_call
                                                                (funn_ext
                                                                   "header"
                                                                   "isValid")
                                                                [e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "tunnel_termination_headers"))
                                                                   "inner_ipv6"])
                                                             (stmt_block []
                                                                (stmt_seq
                                                                   (stmt_ass
                                                                      (lval_field
                                                                         (lval_field
                                                                            (lval_varname
                                                                               (varn_name
                                                                                  "tunnel_termination_headers"))
                                                                            "ethernet")
                                                                         "ether_type")
                                                                      (e_v
                                                                         (v_bit
                                                                            ([T;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              T;
                                                                              T;
                                                                              F;
                                                                              T;
                                                                              T;
                                                                              F;
                                                                              T;
                                                                              T;
                                                                              T;
                                                                              F;
                                                                              T],
                                                                             16))))
                                                                   (stmt_seq
                                                                      (stmt_ass
                                                                         (lval_field
                                                                            (lval_varname
                                                                               (varn_name
                                                                                  "tunnel_termination_headers"))
                                                                            "ipv6")
                                                                         (e_acc
                                                                            (e_var
                                                                               (varn_name
                                                                                  "tunnel_termination_headers"))
                                                                            "inner_ipv6"))
                                                                      (stmt_ass
                                                                         lval_null
                                                                         (e_call
                                                                            (funn_ext
                                                                               "header"
                                                                               "setInvalid")
                                                                            [e_acc
                                                                               (e_var
                                                                                  (varn_name
                                                                                     "tunnel_termination_headers"))
                                                                               "inner_ipv6"])))))
                                                             stmt_empty))))))
                                           stmt_empty)))
                                  (stmt_seq
                                     (stmt_ass
                                        (lval_varname (varn_name "headers"))
                                        (e_var
                                           (varn_name
                                              "tunnel_termination_headers")))
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name "local_metadata"))
                                        (e_var
                                           (varn_name
                                              "tunnel_termination_local_metadata"))))))
                            (stmt_seq
                               (stmt_seq
                                  (stmt_seq
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name
                                              "admit_google_system_mac_headers"))
                                        (e_var (varn_name "headers")))
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name
                                              "admit_google_system_mac_local_metadata"))
                                        (e_var (varn_name "local_metadata"))))
                                  (stmt_seq
                                     (stmt_seq stmt_empty
                                        (stmt_ass
                                           (lval_field
                                              (lval_varname
                                                 (varn_name
                                                    "admit_google_system_mac_local_metadata"))
                                              "admit_to_l3")
                                           (e_binop
                                              (e_binop
                                                 (e_acc
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "admit_google_system_mac_headers"))
                                                       "ethernet") "dst_addr")
                                                 binop_and
                                                 (e_v
                                                    (v_bit
                                                       ([F; F; F; F; F; F; F;
                                                         T; F; F; F; F; F; F;
                                                         F; F; F; F; F; F; F;
                                                         F; F; F; F; F; F; F;
                                                         F; F; F; F; F; F; F;
                                                         F; F; F; F; F; F; F;
                                                         F; F; F; F; F; F],48))))
                                              binop_eq
                                              (e_v
                                                 (v_bit
                                                    ([F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; F; F],
                                                     48))))))
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name "local_metadata"))
                                        (e_var
                                           (varn_name
                                              "admit_google_system_mac_local_metadata")))))
                               (stmt_seq
                                  (stmt_seq
                                     (stmt_seq
                                        (stmt_seq
                                           (stmt_ass
                                              (lval_varname
                                                 (varn_name
                                                    "l3_admit_headers"))
                                              (e_var (varn_name "headers")))
                                           (stmt_ass
                                              (lval_varname
                                                 (varn_name
                                                    "l3_admit_local_metadata"))
                                              (e_var
                                                 (varn_name "local_metadata"))))
                                        (stmt_ass
                                           (lval_varname
                                              (varn_name
                                                 "l3_admit_standard_metadata"))
                                           (e_var
                                              (varn_name "standard_metadata"))))
                                     (stmt_seq
                                        (stmt_seq stmt_empty
                                           (stmt_cond
                                              (e_binop
                                                 (e_acc
                                                    (e_var
                                                       (varn_name
                                                          "l3_admit_local_metadata"))
                                                    "enable_vlan_checks")
                                                 binop_bin_and
                                                 (e_unop unop_neg
                                                    (e_binop
                                                       (e_binop
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "l3_admit_local_metadata"))
                                                             "vlan_id")
                                                          binop_eq
                                                          (e_v
                                                             (v_bit
                                                                ([F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F],
                                                                 12))))
                                                       binop_bin_or
                                                       (e_binop
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "l3_admit_local_metadata"))
                                                             "vlan_id")
                                                          binop_eq
                                                          (e_v
                                                             (v_bit
                                                                ([T; T; T; T;
                                                                  T; T; T; T;
                                                                  T; T; T; T],
                                                                 12)))))))
                                              (stmt_block []
                                                 (stmt_ass
                                                    (lval_field
                                                       (lval_varname
                                                          (varn_name
                                                             "l3_admit_local_metadata"))
                                                       "admit_to_l3")
                                                    (e_v (v_bool F))))
                                              (stmt_block []
                                                 (stmt_app
                                                    "l3_admit.l3_admit_table"
                                                    [e_acc
                                                       (e_acc
                                                          (e_var
                                                             (varn_name
                                                                "l3_admit_headers"))
                                                          "ethernet")
                                                       "dst_addr";
                                                     e_acc
                                                       (e_var
                                                          (varn_name
                                                             "l3_admit_local_metadata"))
                                                       "ingress_port"]))))
                                        (stmt_ass
                                           (lval_varname
                                              (varn_name "local_metadata"))
                                           (e_var
                                              (varn_name
                                                 "l3_admit_local_metadata")))))
                                  (stmt_seq
                                     (stmt_seq
                                        (stmt_seq
                                           (stmt_seq
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "routing_lookup_headers"))
                                                 (e_var (varn_name "headers")))
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "routing_lookup_local_metadata"))
                                                 (e_var
                                                    (varn_name
                                                       "local_metadata"))))
                                           (stmt_ass
                                              (lval_varname
                                                 (varn_name
                                                    "routing_lookup_standard_metadata"))
                                              (e_var
                                                 (varn_name
                                                    "standard_metadata"))))
                                        (stmt_seq
                                           (stmt_seq stmt_empty
                                              (stmt_seq
                                                 (stmt_ass lval_null
                                                    (e_call
                                                       (funn_ext ""
                                                          "mark_to_drop")
                                                       [e_var
                                                          (varn_name
                                                             "routing_lookup_standard_metadata")]))
                                                 (stmt_seq
                                                    (stmt_app
                                                       "routing_lookup.vrf_table"
                                                       [e_acc
                                                          (e_var
                                                             (varn_name
                                                                "routing_lookup_local_metadata"))
                                                          "vrf_id"])
                                                    (stmt_cond
                                                       (e_call
                                                          (funn_ext "header"
                                                             "isValid")
                                                          [e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "routing_lookup_headers"))
                                                             "ipv4"])
                                                       (stmt_block []
                                                          (stmt_cond
                                                             (e_binop
                                                                (e_binop
                                                                   (e_acc
                                                                      (e_acc
                                                                         (e_var
                                                                            (varn_name
                                                                               "routing_lookup_headers"))
                                                                         "ipv4")
                                                                      "dst_addr")
                                                                   binop_and
                                                                   (e_v
                                                                      (v_bit
                                                                         ([T;
                                                                           T;
                                                                           T;
                                                                           T;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F],
                                                                          32))))
                                                                binop_eq
                                                                (e_v
                                                                   (v_bit
                                                                      ([T; T;
                                                                        T; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F],
                                                                       32))))
                                                             (stmt_block []
                                                                (stmt_cond
                                                                   (e_binop
                                                                      (e_binop
                                                                         (e_slice
                                                                            (e_acc
                                                                               (e_acc
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "routing_lookup_headers"))
                                                                                  "ethernet")
                                                                               "dst_addr")
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    T;
                                                                                    F;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T],
                                                                                   16)))
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    T;
                                                                                    T;
                                                                                    F;
                                                                                    F;
                                                                                    F],
                                                                                   16))))
                                                                         binop_eq
                                                                         (e_v
                                                                            (v_bit
                                                                               ([F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 T;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 T;
                                                                                 F;
                                                                                 T;
                                                                                 T;
                                                                                 T;
                                                                                 T;
                                                                                 F],
                                                                                24))))
                                                                      binop_bin_and
                                                                      (e_binop
                                                                         (e_slice
                                                                            (e_acc
                                                                               (e_acc
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "routing_lookup_headers"))
                                                                                  "ethernet")
                                                                               "dst_addr")
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    T;
                                                                                    F;
                                                                                    T;
                                                                                    T;
                                                                                    T],
                                                                                   16)))
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    T;
                                                                                    F;
                                                                                    T;
                                                                                    T;
                                                                                    T],
                                                                                   16))))
                                                                         binop_eq
                                                                         (e_v
                                                                            (v_bit
                                                                               ([F],
                                                                                1)))))
                                                                   (stmt_block
                                                                      []
                                                                      (stmt_seq
                                                                         (stmt_app
                                                                            "routing_lookup.ipv4_multicast_table"
                                                                            [e_acc
                                                                               (e_var
                                                                                  (varn_name
                                                                                     "routing_lookup_local_metadata"))
                                                                               "vrf_id";
                                                                             e_acc
                                                                               (e_acc
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "routing_lookup_headers"))
                                                                                  "ipv4")
                                                                               "dst_addr"])
                                                                         (stmt_ass
                                                                            (lval_field
                                                                               (lval_varname
                                                                                  (varn_name
                                                                                     "routing_lookup_local_metadata"))
                                                                               "ipmc_table_hit")
                                                                            (e_binop
                                                                               (e_acc
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "routing_lookup_standard_metadata"))
                                                                                  "mcast_grp")
                                                                               binop_neq
                                                                               (e_v
                                                                                  (v_bit
                                                                                     ([F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F],
                                                                                      16)))))))
                                                                   stmt_empty))
                                                             (stmt_block []
                                                                (stmt_cond
                                                                   (e_binop
                                                                      (e_binop
                                                                         (e_slice
                                                                            (e_acc
                                                                               (e_acc
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "routing_lookup_headers"))
                                                                                  "ethernet")
                                                                               "dst_addr")
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    T;
                                                                                    F;
                                                                                    T;
                                                                                    F;
                                                                                    F;
                                                                                    F],
                                                                                   16)))
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    T;
                                                                                    F;
                                                                                    T;
                                                                                    F;
                                                                                    F;
                                                                                    F],
                                                                                   16))))
                                                                         binop_eq
                                                                         (e_v
                                                                            (v_bit
                                                                               ([F],
                                                                                1))))
                                                                      binop_bin_and
                                                                      (e_acc
                                                                         (e_var
                                                                            (varn_name
                                                                               "routing_lookup_local_metadata"))
                                                                         "admit_to_l3"))
                                                                   (stmt_block
                                                                      []
                                                                      (stmt_app
                                                                         "routing_lookup.ipv4_table"
                                                                         [e_acc
                                                                            (e_var
                                                                               (varn_name
                                                                                  "routing_lookup_local_metadata"))
                                                                            "vrf_id";
                                                                          e_acc
                                                                            (e_acc
                                                                               (e_var
                                                                                  (varn_name
                                                                                     "routing_lookup_headers"))
                                                                               "ipv4")
                                                                            "dst_addr"]))
                                                                   stmt_empty))))
                                                       (stmt_cond
                                                          (e_call
                                                             (funn_ext
                                                                "header"
                                                                "isValid")
                                                             [e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "routing_lookup_headers"))
                                                                "ipv6"])
                                                          (stmt_block []
                                                             (stmt_cond
                                                                (e_binop
                                                                   (e_binop
                                                                      (e_acc
                                                                         (e_acc
                                                                            (e_var
                                                                               (varn_name
                                                                                  "routing_lookup_headers"))
                                                                            "ipv6")
                                                                         "dst_addr")
                                                                      binop_and
                                                                      (e_v
                                                                         (v_bit
                                                                            ([T;
                                                                              T;
                                                                              T;
                                                                              T;
                                                                              T;
                                                                              T;
                                                                              T;
                                                                              T;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F],
                                                                             128))))
                                                                   binop_eq
                                                                   (e_v
                                                                      (v_bit
                                                                         ([T;
                                                                           T;
                                                                           T;
                                                                           T;
                                                                           T;
                                                                           T;
                                                                           T;
                                                                           T;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F],
                                                                          128))))
                                                                (stmt_block
                                                                   []
                                                                   (stmt_cond
                                                                      (e_binop
                                                                         (e_slice
                                                                            (e_acc
                                                                               (e_acc
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "routing_lookup_headers"))
                                                                                  "ethernet")
                                                                               "dst_addr")
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    T;
                                                                                    F;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T],
                                                                                   16)))
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    T;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F],
                                                                                   16))))
                                                                         binop_eq
                                                                         (e_v
                                                                            (v_bit
                                                                               ([F;
                                                                                 F;
                                                                                 T;
                                                                                 T;
                                                                                 F;
                                                                                 F;
                                                                                 T;
                                                                                 T;
                                                                                 F;
                                                                                 F;
                                                                                 T;
                                                                                 T;
                                                                                 F;
                                                                                 F;
                                                                                 T;
                                                                                 T],
                                                                                16))))
                                                                      (stmt_block
                                                                         []
                                                                         (stmt_seq
                                                                            (stmt_app
                                                                               "routing_lookup.ipv6_multicast_table"
                                                                               [e_acc
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "routing_lookup_local_metadata"))
                                                                                  "vrf_id";
                                                                                e_acc
                                                                                  (e_acc
                                                                                     (e_var
                                                                                        (varn_name
                                                                                           "routing_lookup_headers"))
                                                                                     "ipv6")
                                                                                  "dst_addr"])
                                                                            (stmt_ass
                                                                               (lval_field
                                                                                  (lval_varname
                                                                                     (varn_name
                                                                                        "routing_lookup_local_metadata"))
                                                                                  "ipmc_table_hit")
                                                                               (e_binop
                                                                                  (e_acc
                                                                                     (e_var
                                                                                        (varn_name
                                                                                           "routing_lookup_standard_metadata"))
                                                                                     "mcast_grp")
                                                                                  binop_neq
                                                                                  (e_v
                                                                                     (v_bit
                                                                                        ([F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F],
                                                                                         16)))))))
                                                                      stmt_empty))
                                                                (stmt_block
                                                                   []
                                                                   (stmt_cond
                                                                      (e_binop
                                                                         (e_binop
                                                                            (e_slice
                                                                               (e_acc
                                                                                  (e_acc
                                                                                     (e_var
                                                                                        (varn_name
                                                                                           "routing_lookup_headers"))
                                                                                     "ethernet")
                                                                                  "dst_addr")
                                                                               (e_v
                                                                                  (v_bit
                                                                                     ([F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       T;
                                                                                       F;
                                                                                       T;
                                                                                       F;
                                                                                       F;
                                                                                       F],
                                                                                      16)))
                                                                               (e_v
                                                                                  (v_bit
                                                                                     ([F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       T;
                                                                                       F;
                                                                                       T;
                                                                                       F;
                                                                                       F;
                                                                                       F],
                                                                                      16))))
                                                                            binop_eq
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F],
                                                                                   1))))
                                                                         binop_bin_and
                                                                         (e_acc
                                                                            (e_var
                                                                               (varn_name
                                                                                  "routing_lookup_local_metadata"))
                                                                            "admit_to_l3"))
                                                                      (stmt_block
                                                                         []
                                                                         (stmt_app
                                                                            "routing_lookup.ipv6_table"
                                                                            [e_acc
                                                                               (e_var
                                                                                  (varn_name
                                                                                     "routing_lookup_local_metadata"))
                                                                               "vrf_id";
                                                                             e_acc
                                                                               (e_acc
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "routing_lookup_headers"))
                                                                                  "ipv6")
                                                                               "dst_addr"]))
                                                                      stmt_empty))))
                                                          stmt_empty)))))
                                           (stmt_seq
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "local_metadata"))
                                                 (e_var
                                                    (varn_name
                                                       "routing_lookup_local_metadata")))
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "standard_metadata"))
                                                 (e_var
                                                    (varn_name
                                                       "routing_lookup_standard_metadata"))))))
                                     (stmt_seq
                                        (stmt_seq
                                           (stmt_seq
                                              (stmt_seq
                                                 (stmt_ass
                                                    (lval_varname
                                                       (varn_name
                                                          "acl_ingress_headers"))
                                                    (e_var
                                                       (varn_name "headers")))
                                                 (stmt_ass
                                                    (lval_varname
                                                       (varn_name
                                                          "acl_ingress_local_metadata"))
                                                    (e_var
                                                       (varn_name
                                                          "local_metadata"))))
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "acl_ingress_standard_metadata"))
                                                 (e_var
                                                    (varn_name
                                                       "standard_metadata"))))
                                           (stmt_seq
                                              (stmt_seq
                                                 (stmt_seq
                                                    (stmt_seq
                                                       (stmt_seq
                                                          (stmt_seq
                                                             (stmt_seq
                                                                (stmt_seq
                                                                   (stmt_seq
                                                                      (stmt_seq
                                                                         (stmt_seq
                                                                            (stmt_seq
                                                                               (stmt_seq
                                                                                  stmt_empty
                                                                                  (stmt_ass
                                                                                     (lval_varname
                                                                                        (varn_name
                                                                                           "acl_ingress_ttl"))
                                                                                     (e_v
                                                                                        (v_bit
                                                                                           ([F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F],
                                                                                            8)))))
                                                                               (stmt_ass
                                                                                  (lval_varname
                                                                                     (varn_name
                                                                                        "acl_ingress_dscp"))
                                                                                  (e_v
                                                                                     (v_bit
                                                                                        ([F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F],
                                                                                         6)))))
                                                                            (stmt_ass
                                                                               (lval_varname
                                                                                  (varn_name
                                                                                     "acl_ingress_ecn"))
                                                                               (e_v
                                                                                  (v_bit
                                                                                     ([F;
                                                                                       F],
                                                                                      2)))))
                                                                         (stmt_ass
                                                                            (lval_varname
                                                                               (varn_name
                                                                                  "acl_ingress_ip_protocol"))
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F],
                                                                                   8)))))
                                                                      (stmt_ass
                                                                         (lval_varname
                                                                            (varn_name
                                                                               "acl_ingress_cancel_copy"))
                                                                         (e_v
                                                                            (v_bool
                                                                               F))))
                                                                   (stmt_ass
                                                                      lval_null
                                                                      (e_call
                                                                         (funn_inst
                                                                            "direct_meter")
                                                                         [e_var
                                                                            (varn_name
                                                                               "acl_ingress_acl_ingress_meter");
                                                                          e_v
                                                                            (v_bit
                                                                               ([F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 T],
                                                                                32));
                                                                          e_v
                                                                            (v_bit
                                                                               ([F;
                                                                                 F],
                                                                                2))])))
                                                                (stmt_ass
                                                                   lval_null
                                                                   (e_call
                                                                      (funn_inst
                                                                         "direct_meter")
                                                                      [e_var
                                                                         (varn_name
                                                                            "acl_ingress_acl_ingress_qos_meter");
                                                                       e_v
                                                                         (v_bit
                                                                            ([F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              T],
                                                                             32));
                                                                       e_v
                                                                         (v_bit
                                                                            ([F;
                                                                              F],
                                                                             2))])))
                                                             (stmt_ass
                                                                lval_null
                                                                (e_call
                                                                   (funn_inst
                                                                      "direct_counter")
                                                                   [e_var
                                                                      (varn_name
                                                                         "acl_ingress_acl_ingress_counter");
                                                                    e_v
                                                                      (v_bit
                                                                         ([F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           F;
                                                                           T;
                                                                           F],
                                                                          32))])))
                                                          (stmt_ass lval_null
                                                             (e_call
                                                                (funn_inst
                                                                   "direct_counter")
                                                                [e_var
                                                                   (varn_name
                                                                      "acl_ingress_acl_ingress_qos_counter");
                                                                 e_v
                                                                   (v_bit
                                                                      ([F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        T; F],
                                                                       32))])))
                                                       (stmt_ass lval_null
                                                          (e_call
                                                             (funn_inst
                                                                "direct_counter")
                                                             [e_var
                                                                (varn_name
                                                                   "acl_ingress_acl_ingress_counting_counter");
                                                              e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     T; F],32))])))
                                                    (stmt_ass lval_null
                                                       (e_call
                                                          (funn_inst
                                                             "direct_counter")
                                                          [e_var
                                                             (varn_name
                                                                "acl_ingress_acl_ingress_security_counter");
                                                           e_v
                                                             (v_bit
                                                                ([F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; T; F],
                                                                 32))])))
                                                 (stmt_seq
                                                    (stmt_cond
                                                       (e_call
                                                          (funn_ext "header"
                                                             "isValid")
                                                          [e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "acl_ingress_headers"))
                                                             "ipv4"])
                                                       (stmt_block []
                                                          (stmt_seq
                                                             (stmt_ass
                                                                (lval_varname
                                                                   (varn_name
                                                                      "acl_ingress_ttl"))
                                                                (e_acc
                                                                   (e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "acl_ingress_headers"))
                                                                      "ipv4")
                                                                   "ttl"))
                                                             (stmt_seq
                                                                (stmt_ass
                                                                   (lval_varname
                                                                      (varn_name
                                                                         "acl_ingress_dscp"))
                                                                   (e_acc
                                                                      (e_acc
                                                                         (e_var
                                                                            (varn_name
                                                                               "acl_ingress_headers"))
                                                                         "ipv4")
                                                                      "dscp"))
                                                                (stmt_seq
                                                                   (stmt_ass
                                                                      (lval_varname
                                                                         (varn_name
                                                                            "acl_ingress_ecn"))
                                                                      (e_acc
                                                                         (e_acc
                                                                            (e_var
                                                                               (varn_name
                                                                                  "acl_ingress_headers"))
                                                                            "ipv4")
                                                                         "ecn"))
                                                                   (stmt_ass
                                                                      (lval_varname
                                                                         (varn_name
                                                                            "acl_ingress_ip_protocol"))
                                                                      (e_acc
                                                                         (e_acc
                                                                            (e_var
                                                                               (varn_name
                                                                                  "acl_ingress_headers"))
                                                                            "ipv4")
                                                                         "protocol"))))))
                                                       (stmt_cond
                                                          (e_call
                                                             (funn_ext
                                                                "header"
                                                                "isValid")
                                                             [e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_ingress_headers"))
                                                                "ipv6"])
                                                          (stmt_block []
                                                             (stmt_seq
                                                                (stmt_ass
                                                                   (lval_varname
                                                                      (varn_name
                                                                         "acl_ingress_ttl"))
                                                                   (e_acc
                                                                      (e_acc
                                                                         (e_var
                                                                            (varn_name
                                                                               "acl_ingress_headers"))
                                                                         "ipv6")
                                                                      "hop_limit"))
                                                                (stmt_seq
                                                                   (stmt_ass
                                                                      (lval_varname
                                                                         (varn_name
                                                                            "acl_ingress_dscp"))
                                                                      (e_acc
                                                                         (e_acc
                                                                            (e_var
                                                                               (varn_name
                                                                                  "acl_ingress_headers"))
                                                                            "ipv6")
                                                                         "dscp"))
                                                                   (stmt_seq
                                                                      (stmt_ass
                                                                         (lval_varname
                                                                            (varn_name
                                                                               "acl_ingress_ecn"))
                                                                         (e_acc
                                                                            (e_acc
                                                                               (e_var
                                                                                  (varn_name
                                                                                     "acl_ingress_headers"))
                                                                               "ipv6")
                                                                            "ecn"))
                                                                      (stmt_ass
                                                                         (lval_varname
                                                                            (varn_name
                                                                               "acl_ingress_ip_protocol"))
                                                                         (e_acc
                                                                            (e_acc
                                                                               (e_var
                                                                                  (varn_name
                                                                                     "acl_ingress_headers"))
                                                                               "ipv6")
                                                                            "next_header"))))))
                                                          stmt_empty))
                                                    (stmt_seq
                                                       (stmt_app
                                                          "acl_ingress.acl_ingress_table"
                                                          [e_binop
                                                             (e_call
                                                                (funn_ext
                                                                   "header"
                                                                   "isValid")
                                                                [e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "acl_ingress_headers"))
                                                                   "ipv4"])
                                                             binop_bin_or
                                                             (e_call
                                                                (funn_ext
                                                                   "header"
                                                                   "isValid")
                                                                [e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "acl_ingress_headers"))
                                                                   "ipv6"]);
                                                           e_call
                                                             (funn_ext
                                                                "header"
                                                                "isValid")
                                                             [e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_ingress_headers"))
                                                                "ipv4"];
                                                           e_call
                                                             (funn_ext
                                                                "header"
                                                                "isValid")
                                                             [e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_ingress_headers"))
                                                                "ipv6"];
                                                           e_acc
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_ingress_headers"))
                                                                "ethernet")
                                                             "ether_type";
                                                           e_acc
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_ingress_headers"))
                                                                "ethernet")
                                                             "dst_addr";
                                                           e_acc
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_ingress_headers"))
                                                                "ipv4")
                                                             "src_addr";
                                                           e_acc
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_ingress_headers"))
                                                                "ipv4")
                                                             "dst_addr";
                                                           e_slice
                                                             (e_acc
                                                                (e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "acl_ingress_headers"))
                                                                   "ipv6")
                                                                "src_addr")
                                                             (e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     T; T; T;
                                                                     T; T; T;
                                                                     T],16)))
                                                             (e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     T; F; F;
                                                                     F; F; F;
                                                                     F],16)));
                                                           e_slice
                                                             (e_acc
                                                                (e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "acl_ingress_headers"))
                                                                   "ipv6")
                                                                "dst_addr")
                                                             (e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     T; T; T;
                                                                     T; T; T;
                                                                     T],16)))
                                                             (e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     T; F; F;
                                                                     F; F; F;
                                                                     F],16)));
                                                           e_var
                                                             (varn_name
                                                                "acl_ingress_ttl");
                                                           e_var
                                                             (varn_name
                                                                "acl_ingress_dscp");
                                                           e_var
                                                             (varn_name
                                                                "acl_ingress_ecn");
                                                           e_var
                                                             (varn_name
                                                                "acl_ingress_ip_protocol");
                                                           e_acc
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_ingress_headers"))
                                                                "icmp")
                                                             "type";
                                                           e_acc
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_ingress_headers"))
                                                                "icmp")
                                                             "type";
                                                           e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "acl_ingress_local_metadata"))
                                                             "l4_src_port";
                                                           e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "acl_ingress_local_metadata"))
                                                             "l4_dst_port";
                                                           e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "acl_ingress_local_metadata"))
                                                             "ingress_port";
                                                           e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "acl_ingress_local_metadata"))
                                                             "route_metadata"])
                                                       (stmt_seq
                                                          (stmt_app
                                                             "acl_ingress.acl_ingress_counting_table"
                                                             [e_binop
                                                                (e_call
                                                                   (funn_ext
                                                                      "header"
                                                                      "isValid")
                                                                   [e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "acl_ingress_headers"))
                                                                      "ipv4"])
                                                                binop_bin_or
                                                                (e_call
                                                                   (funn_ext
                                                                      "header"
                                                                      "isValid")
                                                                   [e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "acl_ingress_headers"))
                                                                      "ipv6"]);
                                                              e_call
                                                                (funn_ext
                                                                   "header"
                                                                   "isValid")
                                                                [e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "acl_ingress_headers"))
                                                                   "ipv4"];
                                                              e_call
                                                                (funn_ext
                                                                   "header"
                                                                   "isValid")
                                                                [e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "acl_ingress_headers"))
                                                                   "ipv6"];
                                                              e_var
                                                                (varn_name
                                                                   "acl_ingress_dscp");
                                                              e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_ingress_local_metadata"))
                                                                "route_metadata"])
                                                          (stmt_seq
                                                             (stmt_app
                                                                "acl_ingress.acl_ingress_qos_table"
                                                                [e_binop
                                                                   (e_call
                                                                      (funn_ext
                                                                         "header"
                                                                         "isValid")
                                                                      [e_acc
                                                                         (e_var
                                                                            (varn_name
                                                                               "acl_ingress_headers"))
                                                                         "ipv4"])
                                                                   binop_bin_or
                                                                   (e_call
                                                                      (funn_ext
                                                                         "header"
                                                                         "isValid")
                                                                      [e_acc
                                                                         (e_var
                                                                            (varn_name
                                                                               "acl_ingress_headers"))
                                                                         "ipv6"]);
                                                                 e_call
                                                                   (funn_ext
                                                                      "header"
                                                                      "isValid")
                                                                   [e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "acl_ingress_headers"))
                                                                      "ipv4"];
                                                                 e_call
                                                                   (funn_ext
                                                                      "header"
                                                                      "isValid")
                                                                   [e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "acl_ingress_headers"))
                                                                      "ipv6"];
                                                                 e_acc
                                                                   (e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "acl_ingress_headers"))
                                                                      "ethernet")
                                                                   "ether_type";
                                                                 e_var
                                                                   (varn_name
                                                                      "acl_ingress_ttl");
                                                                 e_var
                                                                   (varn_name
                                                                      "acl_ingress_ip_protocol");
                                                                 e_acc
                                                                   (e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "acl_ingress_headers"))
                                                                      "icmp")
                                                                   "type";
                                                                 e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "acl_ingress_local_metadata"))
                                                                   "l4_dst_port";
                                                                 e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "acl_ingress_local_metadata"))
                                                                   "l4_src_port";
                                                                 e_acc
                                                                   (e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "acl_ingress_headers"))
                                                                      "icmp")
                                                                   "type";
                                                                 e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "acl_ingress_local_metadata"))
                                                                   "route_metadata"])
                                                             (stmt_cond
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_ingress_cancel_copy"))
                                                                (stmt_block
                                                                   []
                                                                   (stmt_ass
                                                                      (lval_field
                                                                         (lval_varname
                                                                            (varn_name
                                                                               "acl_ingress_local_metadata"))
                                                                         "marked_to_copy")
                                                                      (e_v
                                                                         (v_bool
                                                                            F))))
                                                                stmt_empty))))))
                                              (stmt_seq
                                                 (stmt_ass
                                                    (lval_varname
                                                       (varn_name
                                                          "local_metadata"))
                                                    (e_var
                                                       (varn_name
                                                          "acl_ingress_local_metadata")))
                                                 (stmt_ass
                                                    (lval_varname
                                                       (varn_name
                                                          "standard_metadata"))
                                                    (e_var
                                                       (varn_name
                                                          "acl_ingress_standard_metadata"))))))
                                        (stmt_seq
                                           (stmt_seq
                                              (stmt_seq
                                                 (stmt_seq
                                                    (stmt_ass
                                                       (lval_varname
                                                          (varn_name
                                                             "routing_resolution_headers"))
                                                       (e_var
                                                          (varn_name
                                                             "headers")))
                                                    (stmt_ass
                                                       (lval_varname
                                                          (varn_name
                                                             "routing_resolution_local_metadata"))
                                                       (e_var
                                                          (varn_name
                                                             "local_metadata"))))
                                                 (stmt_ass
                                                    (lval_varname
                                                       (varn_name
                                                          "routing_resolution_standard_metadata"))
                                                    (e_var
                                                       (varn_name
                                                          "standard_metadata"))))
                                              (stmt_seq
                                                 (stmt_seq
                                                    (stmt_seq
                                                       (stmt_seq
                                                          (stmt_seq
                                                             (stmt_seq
                                                                stmt_empty
                                                                (stmt_ass
                                                                   (lval_varname
                                                                      (varn_name
                                                                         "routing_resolution_tunnel_id_valid"))
                                                                   (e_v
                                                                      (v_bool
                                                                         F))))
                                                             (stmt_ass
                                                                (lval_varname
                                                                   (varn_name
                                                                      "routing_resolution_router_interface_id_valid"))
                                                                (e_v
                                                                   (v_bool F))))
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "routing_resolution_neighbor_id_valid"))
                                                             (e_v (v_bool F))))
                                                       (stmt_ass lval_null
                                                          (e_call
                                                             (funn_inst
                                                                "action_selector")
                                                             [e_var
                                                                (varn_name
                                                                   "routing_resolution_wcmp_group_selector");
                                                              e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; T;
                                                                     F; T],32));
                                                              e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; T; T;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F],32));
                                                              e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     T; F; F;
                                                                     F; F],32))])))
                                                    (stmt_seq
                                                       (stmt_cond
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "routing_resolution_local_metadata"))
                                                             "admit_to_l3")
                                                          (stmt_block []
                                                             (stmt_seq
                                                                (stmt_cond
                                                                   (e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "routing_resolution_local_metadata"))
                                                                      "wcmp_group_id_valid")
                                                                   (stmt_block
                                                                      []
                                                                      (stmt_app
                                                                         "routing_resolution.wcmp_group_table"
                                                                         [e_acc
                                                                            (e_var
                                                                               (varn_name
                                                                                  "routing_resolution_local_metadata"))
                                                                            "wcmp_group_id_value";
                                                                          e_acc
                                                                            (e_var
                                                                               (varn_name
                                                                                  "routing_resolution_local_metadata"))
                                                                            "wcmp_selector_input"]))
                                                                   stmt_empty)
                                                                (stmt_cond
                                                                   (e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "routing_resolution_local_metadata"))
                                                                      "nexthop_id_valid")
                                                                   (stmt_block
                                                                      []
                                                                      (stmt_seq
                                                                         (stmt_app
                                                                            "routing_resolution.nexthop_table"
                                                                            [e_acc
                                                                               (e_var
                                                                                  (varn_name
                                                                                     "routing_resolution_local_metadata"))
                                                                               "nexthop_id_value"])
                                                                         (stmt_seq
                                                                            (stmt_cond
                                                                               (e_var
                                                                                  (varn_name
                                                                                     "routing_resolution_tunnel_id_valid"))
                                                                               (stmt_block
                                                                                  []
                                                                                  (stmt_app
                                                                                     "routing_resolution.tunnel_table"
                                                                                     [e_var
                                                                                        (varn_name
                                                                                           "routing_resolution_tunnel_id_value")]))
                                                                               stmt_empty)
                                                                            (stmt_cond
                                                                               (e_binop
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "routing_resolution_router_interface_id_valid"))
                                                                                  binop_bin_and
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "routing_resolution_neighbor_id_valid")))
                                                                               (stmt_block
                                                                                  []
                                                                                  (stmt_seq
                                                                                     (stmt_app
                                                                                        "routing_resolution.router_interface_table"
                                                                                        [e_var
                                                                                           (varn_name
                                                                                              "routing_resolution_router_interface_id_value")])
                                                                                     (stmt_app
                                                                                        "routing_resolution.neighbor_table"
                                                                                        [e_var
                                                                                           (varn_name
                                                                                              "routing_resolution_router_interface_id_value");
                                                                                         e_var
                                                                                           (varn_name
                                                                                              "routing_resolution_neighbor_id_value")])))
                                                                               stmt_empty))))
                                                                   stmt_empty)))
                                                          stmt_empty)
                                                       (stmt_seq
                                                          (stmt_ass
                                                             (lval_field
                                                                (lval_varname
                                                                   (varn_name
                                                                      "routing_resolution_local_metadata"))
                                                                "packet_in_target_egress_port")
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "routing_resolution_standard_metadata"))
                                                                "egress_spec"))
                                                          (stmt_seq
                                                             (stmt_ass
                                                                (lval_field
                                                                   (lval_varname
                                                                      (varn_name
                                                                         "routing_resolution_local_metadata"))
                                                                   "packet_in_ingress_port")
                                                                (e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "routing_resolution_standard_metadata"))
                                                                   "ingress_port"))
                                                             (stmt_cond
                                                                (e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "routing_resolution_local_metadata"))
                                                                   "acl_drop")
                                                                (stmt_block
                                                                   []
                                                                   (stmt_ass
                                                                      lval_null
                                                                      (e_call
                                                                         (funn_ext
                                                                            ""
                                                                            "mark_to_drop")
                                                                         [e_var
                                                                            (varn_name
                                                                               "routing_resolution_standard_metadata")])))
                                                                stmt_empty)))))
                                                 (stmt_seq
                                                    (stmt_ass
                                                       (lval_varname
                                                          (varn_name
                                                             "local_metadata"))
                                                       (e_var
                                                          (varn_name
                                                             "routing_resolution_local_metadata")))
                                                    (stmt_ass
                                                       (lval_varname
                                                          (varn_name
                                                             "standard_metadata"))
                                                       (e_var
                                                          (varn_name
                                                             "routing_resolution_standard_metadata"))))))
                                           (stmt_seq
                                              (stmt_seq
                                                 (stmt_seq
                                                    (stmt_seq
                                                       (stmt_ass
                                                          (lval_varname
                                                             (varn_name
                                                                "mirror_session_lookup_headers"))
                                                          (e_var
                                                             (varn_name
                                                                "headers")))
                                                       (stmt_ass
                                                          (lval_varname
                                                             (varn_name
                                                                "mirror_session_lookup_local_metadata"))
                                                          (e_var
                                                             (varn_name
                                                                "local_metadata"))))
                                                    (stmt_ass
                                                       (lval_varname
                                                          (varn_name
                                                             "mirror_session_lookup_standard_metadata"))
                                                       (e_var
                                                          (varn_name
                                                             "standard_metadata"))))
                                                 (stmt_seq
                                                    (stmt_seq stmt_empty
                                                       (stmt_cond
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "mirror_session_lookup_local_metadata"))
                                                             "marked_to_mirror")
                                                          (stmt_block []
                                                             (stmt_app
                                                                "mirror_session_lookup.mirror_session_table"
                                                                [e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "mirror_session_lookup_local_metadata"))
                                                                   "mirror_session_id"]))
                                                          stmt_empty))
                                                    (stmt_seq
                                                       (stmt_seq
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "headers"))
                                                             (e_var
                                                                (varn_name
                                                                   "mirror_session_lookup_headers")))
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "local_metadata"))
                                                             (e_var
                                                                (varn_name
                                                                   "mirror_session_lookup_local_metadata"))))
                                                       (stmt_ass
                                                          (lval_varname
                                                             (varn_name
                                                                "standard_metadata"))
                                                          (e_var
                                                             (varn_name
                                                                "mirror_session_lookup_standard_metadata"))))))
                                              (stmt_seq
                                                 (stmt_seq
                                                    (stmt_seq
                                                       (stmt_seq
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "ingress_cloning_headers"))
                                                             (e_var
                                                                (varn_name
                                                                   "headers")))
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "ingress_cloning_local_metadata"))
                                                             (e_var
                                                                (varn_name
                                                                   "local_metadata"))))
                                                       (stmt_ass
                                                          (lval_varname
                                                             (varn_name
                                                                "ingress_cloning_standard_metadata"))
                                                          (e_var
                                                             (varn_name
                                                                "standard_metadata"))))
                                                    (stmt_seq
                                                       (stmt_seq stmt_empty
                                                          (stmt_app
                                                             "ingress_cloning.ingress_clone_table"
                                                             [e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "ingress_cloning_local_metadata"))
                                                                "marked_to_copy";
                                                              e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "ingress_cloning_local_metadata"))
                                                                "marked_to_mirror";
                                                              e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "ingress_cloning_local_metadata"))
                                                                "mirror_egress_port"]))
                                                       (stmt_seq
                                                          (stmt_seq
                                                             (stmt_ass
                                                                (lval_varname
                                                                   (varn_name
                                                                      "headers"))
                                                                (e_var
                                                                   (varn_name
                                                                      "ingress_cloning_headers")))
                                                             (stmt_ass
                                                                (lval_varname
                                                                   (varn_name
                                                                      "local_metadata"))
                                                                (e_var
                                                                   (varn_name
                                                                      "ingress_cloning_local_metadata"))))
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "standard_metadata"))
                                                             (e_var
                                                                (varn_name
                                                                   "ingress_cloning_standard_metadata"))))))
                                                 (stmt_seq
                                                    (stmt_seq
                                                       (stmt_seq
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "drop_martians_headers"))
                                                             (e_var
                                                                (varn_name
                                                                   "headers")))
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "drop_martians_local_metadata"))
                                                             (e_var
                                                                (varn_name
                                                                   "local_metadata"))))
                                                       (stmt_ass
                                                          (lval_varname
                                                             (varn_name
                                                                "drop_martians_standard_metadata"))
                                                          (e_var
                                                             (varn_name
                                                                "standard_metadata"))))
                                                    (stmt_seq
                                                       (stmt_seq stmt_empty
                                                          (stmt_cond
                                                             (e_binop
                                                                (e_binop
                                                                   (e_call
                                                                      (funn_ext
                                                                         "header"
                                                                         "isValid")
                                                                      [e_acc
                                                                         (e_var
                                                                            (varn_name
                                                                               "drop_martians_headers"))
                                                                         "ipv6"])
                                                                   binop_bin_and
                                                                   (e_binop
                                                                      (e_binop
                                                                         (e_binop
                                                                            (e_binop
                                                                               (e_acc
                                                                                  (e_acc
                                                                                     (e_var
                                                                                        (varn_name
                                                                                           "drop_martians_headers"))
                                                                                     "ipv6")
                                                                                  "src_addr")
                                                                               binop_and
                                                                               (e_v
                                                                                  (v_bit
                                                                                     ([T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F],
                                                                                      128))))
                                                                            binop_eq
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F],
                                                                                   128))))
                                                                         binop_bin_or
                                                                         (e_binop
                                                                            (e_binop
                                                                               (e_acc
                                                                                  (e_acc
                                                                                     (e_var
                                                                                        (varn_name
                                                                                           "drop_martians_headers"))
                                                                                     "ipv6")
                                                                                  "src_addr")
                                                                               binop_and
                                                                               (e_v
                                                                                  (v_bit
                                                                                     ([T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T],
                                                                                      128))))
                                                                            binop_eq
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    T],
                                                                                   128)))))
                                                                      binop_bin_or
                                                                      (e_binop
                                                                         (e_binop
                                                                            (e_acc
                                                                               (e_acc
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "drop_martians_headers"))
                                                                                  "ipv6")
                                                                               "dst_addr")
                                                                            binop_and
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T],
                                                                                   128))))
                                                                         binop_eq
                                                                         (e_v
                                                                            (v_bit
                                                                               ([F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 T],
                                                                                128))))))
                                                                binop_bin_or
                                                                (e_binop
                                                                   (e_call
                                                                      (funn_ext
                                                                         "header"
                                                                         "isValid")
                                                                      [e_acc
                                                                         (e_var
                                                                            (varn_name
                                                                               "drop_martians_headers"))
                                                                         "ipv4"])
                                                                   binop_bin_and
                                                                   (e_binop
                                                                      (e_binop
                                                                         (e_binop
                                                                            (e_binop
                                                                               (e_binop
                                                                                  (e_binop
                                                                                     (e_acc
                                                                                        (e_acc
                                                                                           (e_var
                                                                                              (varn_name
                                                                                                 "drop_martians_headers"))
                                                                                           "ipv4")
                                                                                        "src_addr")
                                                                                     binop_and
                                                                                     (e_v
                                                                                        (v_bit
                                                                                           ([T;
                                                                                             T;
                                                                                             T;
                                                                                             T;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F],
                                                                                            32))))
                                                                                  binop_eq
                                                                                  (e_v
                                                                                     (v_bit
                                                                                        ([T;
                                                                                          T;
                                                                                          T;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F;
                                                                                          F],
                                                                                         32))))
                                                                               binop_bin_or
                                                                               (e_binop
                                                                                  (e_acc
                                                                                     (e_acc
                                                                                        (e_var
                                                                                           (varn_name
                                                                                              "drop_martians_headers"))
                                                                                        "ipv4")
                                                                                     "src_addr")
                                                                                  binop_eq
                                                                                  (e_v
                                                                                     (v_bit
                                                                                        ([T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T;
                                                                                          T],
                                                                                         32)))))
                                                                            binop_bin_or
                                                                            (e_binop
                                                                               (e_acc
                                                                                  (e_acc
                                                                                     (e_var
                                                                                        (varn_name
                                                                                           "drop_martians_headers"))
                                                                                     "ipv4")
                                                                                  "dst_addr")
                                                                               binop_eq
                                                                               (e_v
                                                                                  (v_bit
                                                                                     ([T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T],
                                                                                      32)))))
                                                                         binop_bin_or
                                                                         (e_binop
                                                                            (e_binop
                                                                               (e_acc
                                                                                  (e_acc
                                                                                     (e_var
                                                                                        (varn_name
                                                                                           "drop_martians_headers"))
                                                                                     "ipv4")
                                                                                  "src_addr")
                                                                               binop_and
                                                                               (e_v
                                                                                  (v_bit
                                                                                     ([T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       T;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F],
                                                                                      32))))
                                                                            binop_eq
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F],
                                                                                   32)))))
                                                                      binop_bin_or
                                                                      (e_binop
                                                                         (e_binop
                                                                            (e_acc
                                                                               (e_acc
                                                                                  (e_var
                                                                                     (varn_name
                                                                                        "drop_martians_headers"))
                                                                                  "ipv4")
                                                                               "dst_addr")
                                                                            binop_and
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    T;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F],
                                                                                   32))))
                                                                         binop_eq
                                                                         (e_v
                                                                            (v_bit
                                                                               ([F;
                                                                                 T;
                                                                                 T;
                                                                                 T;
                                                                                 T;
                                                                                 T;
                                                                                 T;
                                                                                 T;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F;
                                                                                 F],
                                                                                32)))))))
                                                             (stmt_block []
                                                                (stmt_ass
                                                                   lval_null
                                                                   (e_call
                                                                      (funn_ext
                                                                         ""
                                                                         "mark_to_drop")
                                                                      [e_var
                                                                         (varn_name
                                                                            "drop_martians_standard_metadata")])))
                                                             stmt_empty))
                                                       (stmt_seq
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "local_metadata"))
                                                             (e_var
                                                                (varn_name
                                                                   "drop_martians_local_metadata")))
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "standard_metadata"))
                                                             (e_var
                                                                (varn_name
                                                                   "drop_martians_standard_metadata"))))))))))))))))))
             stmt_empty)),[])],
   [(varn_name "drop_martians_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "drop_martians_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "drop_martians_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "ingress_cloning_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "ingress_cloning_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "ingress_cloning_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "mirror_session_lookup_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "mirror_session_lookup_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "mirror_session_lookup_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "routing_resolution_tunnel_id_valid",tau_bool,NONE);
    (varn_name "routing_resolution_tunnel_id_value",tau_bit 10,NONE);
    (varn_name "routing_resolution_router_interface_id_valid",tau_bool,NONE);
    (varn_name "routing_resolution_router_interface_id_value",tau_bit 10,NONE);
    (varn_name "routing_resolution_neighbor_id_valid",tau_bool,NONE);
    (varn_name "routing_resolution_neighbor_id_value",tau_bit 128,NONE);
    (varn_name "routing_resolution_wcmp_group_selector",tau_ext,NONE);
    (varn_name "routing_resolution_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "routing_resolution_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "routing_resolution_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "acl_ingress_ttl",tau_bit 8,NONE);
    (varn_name "acl_ingress_dscp",tau_bit 6,NONE);
    (varn_name "acl_ingress_ecn",tau_bit 2,NONE);
    (varn_name "acl_ingress_ip_protocol",tau_bit 8,NONE);
    (varn_name "acl_ingress_cancel_copy",tau_bool,NONE);
    (varn_name "acl_ingress_acl_ingress_meter",tau_ext,NONE);
    (varn_name "acl_ingress_acl_ingress_qos_meter",tau_ext,NONE);
    (varn_name "acl_ingress_acl_ingress_counter",tau_ext,NONE);
    (varn_name "acl_ingress_acl_ingress_qos_counter",tau_ext,NONE);
    (varn_name "acl_ingress_acl_ingress_counting_counter",tau_ext,NONE);
    (varn_name "acl_ingress_acl_ingress_security_counter",tau_ext,NONE);
    (varn_name "acl_ingress_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "acl_ingress_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "acl_ingress_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "routing_lookup_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "routing_lookup_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "routing_lookup_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "l3_admit_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "l3_admit_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "l3_admit_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "admit_google_system_mac_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "admit_google_system_mac_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "tunnel_termination_marked_for_ip_in_ipv6_decap",tau_bool,NONE);
    (varn_name "tunnel_termination_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "tunnel_termination_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "ingress_vlan_checks_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "ingress_vlan_checks_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "ingress_vlan_checks_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "acl_pre_ingress_dscp",tau_bit 6,NONE);
    (varn_name "acl_pre_ingress_ecn",tau_bit 2,NONE);
    (varn_name "acl_pre_ingress_ip_protocol",tau_bit 8,NONE);
    (varn_name "acl_pre_ingress_acl_pre_ingress_counter",tau_ext,NONE);
    (varn_name "acl_pre_ingress_acl_pre_ingress_vlan_counter",tau_ext,NONE);
    (varn_name "acl_pre_ingress_acl_pre_ingress_metadata_counter",tau_ext,
     NONE);
    (varn_name "acl_pre_ingress_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "acl_pre_ingress_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "acl_pre_ingress_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "vlan_untag_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "vlan_untag_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "vlan_untag_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "packet_out_decap_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "packet_out_decap_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "packet_out_decap_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE)],[],
   [("ingress_cloning.ingress_clone_table",[mk_exact; mk_exact; mk_optional],
     "NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("mirror_session_lookup.mirror_session_table",[mk_exact],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("routing_resolution.neighbor_table",[mk_exact; mk_exact],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("routing_resolution.router_interface_table",[mk_exact],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("routing_resolution.nexthop_table",[mk_exact],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("routing_resolution.tunnel_table",[mk_exact],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("routing_resolution.wcmp_group_table",[mk_exact; mk_selector],
     "NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("acl_ingress.acl_ingress_table",
     [mk_optional; mk_optional; mk_optional; mk_ternary; mk_ternary;
      mk_ternary; mk_ternary; mk_ternary; mk_ternary; mk_ternary; mk_ternary;
      mk_ternary; mk_ternary; mk_ternary; mk_ternary; mk_ternary; mk_ternary;
      mk_optional; mk_optional],"NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("acl_ingress.acl_ingress_qos_table",
     [mk_optional; mk_optional; mk_optional; mk_ternary; mk_ternary;
      mk_ternary; mk_ternary; mk_ternary; mk_ternary; mk_ternary; mk_ternary],
     "NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("acl_ingress.acl_ingress_counting_table",
     [mk_optional; mk_optional; mk_optional; mk_ternary; mk_ternary],
     "NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("acl_ingress.acl_ingress_mirror_and_redirect_table",
     [mk_optional; mk_optional; mk_optional; mk_ternary; mk_ternary;
      mk_optional; mk_optional],"NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("acl_ingress.acl_ingress_security_table",
     [mk_optional; mk_optional; mk_optional; mk_ternary],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("routing_lookup.vrf_table",[mk_exact],"no_action",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("routing_lookup.ipv4_table",[mk_exact; mk_lpm],"routing_lookup.drop",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("routing_lookup.ipv6_table",[mk_exact; mk_lpm],"routing_lookup.drop",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("routing_lookup.ipv4_multicast_table",[mk_exact; mk_exact],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("routing_lookup.ipv6_multicast_table",[mk_exact; mk_exact],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("l3_admit.l3_admit_table",[mk_ternary; mk_optional],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("tunnel_termination.ipv6_tunnel_termination_table",
     [mk_ternary; mk_ternary],"NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("acl_pre_ingress.acl_pre_ingress_table",
     [mk_optional; mk_optional; mk_optional; mk_ternary; mk_ternary;
      mk_ternary; mk_ternary; mk_ternary; mk_ternary; mk_optional],
     "NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("acl_pre_ingress.acl_pre_ingress_vlan_table",
     [mk_optional; mk_optional; mk_optional; mk_ternary; mk_ternary],
     "NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("acl_pre_ingress.acl_pre_ingress_metadata_table",
     [mk_optional; mk_optional; mk_optional; mk_ternary; mk_ternary;
      mk_ternary; mk_ternary],"NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("vlan_untag.disable_vlan_checks_table",[mk_ternary],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)])]);
  ("egress",pbl_type_control,
   [("headers",d_inout); ("local_metadata",d_inout);
    ("standard_metadata",d_inout)],
   [("acl_egress.acl_egress_forward",
     stmt_seq
       (stmt_cond (e_var (varn_name "acl_egress_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",e_var (varn_name "acl_egress_hit"));
                 ("miss",e_unop unop_neg (e_var (varn_name "acl_egress_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; F],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_ass lval_null
             (e_call (funn_ext "direct_counter" "count")
                [e_var (varn_name "acl_egress_acl_egress_counter")]))
          (stmt_ret (e_v v_bot))),
     [("acl_egress_from_table",d_in); ("acl_egress_hit",d_in)]);
    ("packet_rewrites.multicast_rewrites.l2_multicast_passthrough",
     stmt_seq
       (stmt_cond
          (e_var (varn_name "packet_rewrites_multicast_rewrites_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",
                  e_var (varn_name "packet_rewrites_multicast_rewrites_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var
                       (varn_name "packet_rewrites_multicast_rewrites_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; T; F; F],32)))]))
          stmt_empty) (stmt_seq stmt_empty (stmt_ret (e_v v_bot))),
     [("packet_rewrites_multicast_rewrites_from_table",d_in);
      ("packet_rewrites_multicast_rewrites_hit",d_in)]);
    ("packet_rewrites.multicast_rewrites.set_multicast_src_mac",
     stmt_seq
       (stmt_cond
          (e_var (varn_name "packet_rewrites_multicast_rewrites_from_table"))
          (stmt_ass (lval_varname (varn_name "gen_apply_result"))
             (e_struct
                [("hit",
                  e_var (varn_name "packet_rewrites_multicast_rewrites_hit"));
                 ("miss",
                  e_unop unop_neg
                    (e_var
                       (varn_name "packet_rewrites_multicast_rewrites_hit")));
                 ("action_run",
                  e_v
                    (v_bit
                       ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                         F; F; F; F; F; F; F; F; F; F; F; F; F; T; T],32)))]))
          stmt_empty)
       (stmt_seq
          (stmt_seq
             (stmt_ass
                (lval_field
                   (lval_varname
                      (varn_name
                         "packet_rewrites_multicast_rewrites_local_metadata"))
                   "enable_src_mac_rewrite") (e_v (v_bool T)))
             (stmt_seq
                (stmt_ass
                   (lval_field
                      (lval_field
                         (lval_varname
                            (varn_name
                               "packet_rewrites_multicast_rewrites_local_metadata"))
                         "packet_rewrites") "src_mac")
                   (e_var
                      (varn_name "packet_rewrites_multicast_rewrites_src_mac")))
                (stmt_ass
                   (lval_field
                      (lval_field
                         (lval_varname
                            (varn_name
                               "packet_rewrites_multicast_rewrites_local_metadata"))
                         "packet_rewrites") "vlan_id")
                   (e_v (v_bit ([T; T; T; T; T; T; T; T; T; T; T; T],12))))))
          (stmt_ret (e_v v_bot))),
     [("packet_rewrites_multicast_rewrites_from_table",d_in);
      ("packet_rewrites_multicast_rewrites_hit",d_in);
      ("packet_rewrites_multicast_rewrites_src_mac",d_none)]);
    ("egress",
     stmt_seq stmt_empty
       (stmt_seq
          (stmt_seq
             (stmt_seq
                (stmt_seq
                   (stmt_ass
                      (lval_varname (varn_name "packet_in_encap_headers"))
                      (e_var (varn_name "headers")))
                   (stmt_ass
                      (lval_varname
                         (varn_name "packet_in_encap_local_metadata"))
                      (e_var (varn_name "local_metadata"))))
                (stmt_ass
                   (lval_varname
                      (varn_name "packet_in_encap_standard_metadata"))
                   (e_var (varn_name "standard_metadata"))))
             (stmt_seq (stmt_seq stmt_empty stmt_empty)
                (stmt_seq
                   (stmt_seq
                      (stmt_ass (lval_varname (varn_name "headers"))
                         (e_var (varn_name "packet_in_encap_headers")))
                      (stmt_ass (lval_varname (varn_name "local_metadata"))
                         (e_var (varn_name "packet_in_encap_local_metadata"))))
                   (stmt_ass (lval_varname (varn_name "standard_metadata"))
                      (e_var (varn_name "packet_in_encap_standard_metadata"))))))
          (stmt_cond
             (e_unop unop_neg
                (e_binop
                   (e_binop
                      (e_acc (e_var (varn_name "standard_metadata"))
                         "instance_type") binop_eq
                      (e_v
                         (v_bit
                            ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                              F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T],
                             32)))) binop_bin_and
                   (e_binop
                      (e_acc (e_var (varn_name "standard_metadata"))
                         "egress_rid") binop_eq
                      (e_v
                         (v_bit
                            ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T],
                             16))))))
             (stmt_block []
                (stmt_seq
                   (stmt_seq
                      (stmt_seq
                         (stmt_seq
                            (stmt_ass
                               (lval_varname
                                  (varn_name "packet_rewrites_headers"))
                               (e_var (varn_name "headers")))
                            (stmt_ass
                               (lval_varname
                                  (varn_name "packet_rewrites_local_metadata"))
                               (e_var (varn_name "local_metadata"))))
                         (stmt_ass
                            (lval_varname
                               (varn_name "packet_rewrites_standard_metadata"))
                            (e_var (varn_name "standard_metadata"))))
                      (stmt_seq
                         (stmt_seq stmt_empty
                            (stmt_seq
                               (stmt_cond
                                  (e_binop
                                     (e_acc
                                        (e_var
                                           (varn_name
                                              "packet_rewrites_standard_metadata"))
                                        "instance_type") binop_eq
                                     (e_v
                                        (v_bit
                                           ([F; F; F; F; F; F; F; F; F; F; F;
                                             F; F; F; F; F; F; F; F; F; F; F;
                                             F; F; F; F; F; F; F; T; F; T],32))))
                                  (stmt_block []
                                     (stmt_seq
                                        (stmt_ass
                                           (lval_field
                                              (lval_varname
                                                 (varn_name
                                                    "packet_rewrites_local_metadata"))
                                              "enable_decrement_ttl")
                                           (e_v (v_bool T)))
                                        (stmt_seq
                                           (stmt_seq
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "packet_rewrites_multicast_rewrites_local_metadata"))
                                                 (e_var
                                                    (varn_name
                                                       "packet_rewrites_local_metadata")))
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "packet_rewrites_multicast_rewrites_standard_metadata"))
                                                 (e_var
                                                    (varn_name
                                                       "packet_rewrites_standard_metadata"))))
                                           (stmt_seq
                                              (stmt_seq
                                                 (stmt_seq
                                                    (stmt_seq stmt_empty
                                                       (stmt_ass
                                                          (lval_varname
                                                             (varn_name
                                                                "packet_rewrites_multicast_rewrites_multicast_replica_port"))
                                                          (e_cast
                                                             (cast_unsigned 9)
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "packet_rewrites_multicast_rewrites_standard_metadata"))
                                                                "egress_port"))))
                                                    (stmt_ass
                                                       (lval_varname
                                                          (varn_name
                                                             "packet_rewrites_multicast_rewrites_multicast_replica_instance"))
                                                       (e_acc
                                                          (e_var
                                                             (varn_name
                                                                "packet_rewrites_multicast_rewrites_standard_metadata"))
                                                          "egress_rid")))
                                                 (stmt_app
                                                    "packet_rewrites.multicast_rewrites.multicast_router_interface_table"
                                                    [e_var
                                                       (varn_name
                                                          "packet_rewrites_multicast_rewrites_multicast_replica_port");
                                                     e_var
                                                       (varn_name
                                                          "packet_rewrites_multicast_rewrites_multicast_replica_instance")]))
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "packet_rewrites_local_metadata"))
                                                 (e_var
                                                    (varn_name
                                                       "packet_rewrites_multicast_rewrites_local_metadata")))))))
                                  stmt_empty)
                               (stmt_seq
                                  (stmt_cond
                                     (e_acc
                                        (e_var
                                           (varn_name
                                              "packet_rewrites_local_metadata"))
                                        "enable_src_mac_rewrite")
                                     (stmt_block []
                                        (stmt_ass
                                           (lval_field
                                              (lval_field
                                                 (lval_varname
                                                    (varn_name
                                                       "packet_rewrites_headers"))
                                                 "ethernet") "src_addr")
                                           (e_acc
                                              (e_acc
                                                 (e_var
                                                    (varn_name
                                                       "packet_rewrites_local_metadata"))
                                                 "packet_rewrites") "src_mac")))
                                     stmt_empty)
                                  (stmt_seq
                                     (stmt_cond
                                        (e_acc
                                           (e_var
                                              (varn_name
                                                 "packet_rewrites_local_metadata"))
                                           "enable_dst_mac_rewrite")
                                        (stmt_block []
                                           (stmt_ass
                                              (lval_field
                                                 (lval_field
                                                    (lval_varname
                                                       (varn_name
                                                          "packet_rewrites_headers"))
                                                    "ethernet") "dst_addr")
                                              (e_acc
                                                 (e_acc
                                                    (e_var
                                                       (varn_name
                                                          "packet_rewrites_local_metadata"))
                                                    "packet_rewrites")
                                                 "dst_mac"))) stmt_empty)
                                     (stmt_seq
                                        (stmt_cond
                                           (e_acc
                                              (e_var
                                                 (varn_name
                                                    "packet_rewrites_local_metadata"))
                                              "enable_vlan_rewrite")
                                           (stmt_block []
                                              (stmt_ass
                                                 (lval_field
                                                    (lval_varname
                                                       (varn_name
                                                          "packet_rewrites_local_metadata"))
                                                    "vlan_id")
                                                 (e_acc
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "packet_rewrites_local_metadata"))
                                                       "packet_rewrites")
                                                    "vlan_id"))) stmt_empty)
                                        (stmt_seq
                                           (stmt_cond
                                              (e_call
                                                 (funn_ext "header" "isValid")
                                                 [e_acc
                                                    (e_var
                                                       (varn_name
                                                          "packet_rewrites_headers"))
                                                    "ipv4"])
                                              (stmt_block []
                                                 (stmt_seq
                                                    (stmt_cond
                                                       (e_binop
                                                          (e_binop
                                                             (e_acc
                                                                (e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "packet_rewrites_headers"))
                                                                   "ipv4")
                                                                "ttl")
                                                             binop_gt
                                                             (e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F],8))))
                                                          binop_bin_and
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "packet_rewrites_local_metadata"))
                                                             "enable_decrement_ttl"))
                                                       (stmt_block []
                                                          (stmt_ass
                                                             (lval_field
                                                                (lval_field
                                                                   (lval_varname
                                                                      (varn_name
                                                                         "packet_rewrites_headers"))
                                                                   "ipv4")
                                                                "ttl")
                                                             (e_binop
                                                                (e_acc
                                                                   (e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "packet_rewrites_headers"))
                                                                      "ipv4")
                                                                   "ttl")
                                                                binop_sub
                                                                (e_v
                                                                   (v_bit
                                                                      ([F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; T],
                                                                       8))))))
                                                       stmt_empty)
                                                    (stmt_cond
                                                       (e_binop
                                                          (e_acc
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "packet_rewrites_headers"))
                                                                "ipv4") "ttl")
                                                          binop_eq
                                                          (e_v
                                                             (v_bit
                                                                ([F; F; F; F;
                                                                  F; F; F; F],
                                                                 8))))
                                                       (stmt_ass lval_null
                                                          (e_call
                                                             (funn_ext ""
                                                                "mark_to_drop")
                                                             [e_var
                                                                (varn_name
                                                                   "packet_rewrites_standard_metadata")]))
                                                       stmt_empty)))
                                              stmt_empty)
                                           (stmt_cond
                                              (e_call
                                                 (funn_ext "header" "isValid")
                                                 [e_acc
                                                    (e_var
                                                       (varn_name
                                                          "packet_rewrites_headers"))
                                                    "ipv6"])
                                              (stmt_block []
                                                 (stmt_seq
                                                    (stmt_cond
                                                       (e_binop
                                                          (e_binop
                                                             (e_acc
                                                                (e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "packet_rewrites_headers"))
                                                                   "ipv6")
                                                                "hop_limit")
                                                             binop_gt
                                                             (e_v
                                                                (v_bit
                                                                   ([F; F; F;
                                                                     F; F; F;
                                                                     F; F],8))))
                                                          binop_bin_and
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "packet_rewrites_local_metadata"))
                                                             "enable_decrement_ttl"))
                                                       (stmt_block []
                                                          (stmt_ass
                                                             (lval_field
                                                                (lval_field
                                                                   (lval_varname
                                                                      (varn_name
                                                                         "packet_rewrites_headers"))
                                                                   "ipv6")
                                                                "hop_limit")
                                                             (e_binop
                                                                (e_acc
                                                                   (e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "packet_rewrites_headers"))
                                                                      "ipv6")
                                                                   "hop_limit")
                                                                binop_sub
                                                                (e_v
                                                                   (v_bit
                                                                      ([F; F;
                                                                        F; F;
                                                                        F; F;
                                                                        F; T],
                                                                       8))))))
                                                       stmt_empty)
                                                    (stmt_cond
                                                       (e_binop
                                                          (e_acc
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "packet_rewrites_headers"))
                                                                "ipv6")
                                                             "hop_limit")
                                                          binop_eq
                                                          (e_v
                                                             (v_bit
                                                                ([F; F; F; F;
                                                                  F; F; F; F],
                                                                 8))))
                                                       (stmt_ass lval_null
                                                          (e_call
                                                             (funn_ext ""
                                                                "mark_to_drop")
                                                             [e_var
                                                                (varn_name
                                                                   "packet_rewrites_standard_metadata")]))
                                                       stmt_empty)))
                                              stmt_empty)))))))
                         (stmt_seq
                            (stmt_seq
                               (stmt_ass (lval_varname (varn_name "headers"))
                                  (e_var
                                     (varn_name "packet_rewrites_headers")))
                               (stmt_ass
                                  (lval_varname (varn_name "local_metadata"))
                                  (e_var
                                     (varn_name
                                        "packet_rewrites_local_metadata"))))
                            (stmt_ass
                               (lval_varname (varn_name "standard_metadata"))
                               (e_var
                                  (varn_name
                                     "packet_rewrites_standard_metadata"))))))
                   (stmt_seq
                      (stmt_seq
                         (stmt_seq
                            (stmt_seq
                               (stmt_ass
                                  (lval_varname
                                     (varn_name "mirroring_encap_headers"))
                                  (e_var (varn_name "headers")))
                               (stmt_ass
                                  (lval_varname
                                     (varn_name
                                        "mirroring_encap_local_metadata"))
                                  (e_var (varn_name "local_metadata"))))
                            (stmt_ass
                               (lval_varname
                                  (varn_name
                                     "mirroring_encap_standard_metadata"))
                               (e_var (varn_name "standard_metadata"))))
                         (stmt_seq
                            (stmt_seq stmt_empty
                               (stmt_cond
                                  (e_binop
                                     (e_binop
                                        (e_acc
                                           (e_var
                                              (varn_name
                                                 "mirroring_encap_standard_metadata"))
                                           "instance_type") binop_eq
                                        (e_v
                                           (v_bit
                                              ([F; F; F; F; F; F; F; F; F; F;
                                                F; F; F; F; F; F; F; F; F; F;
                                                F; F; F; F; F; F; F; F; F; F;
                                                F; T],32)))) binop_bin_and
                                     (e_binop
                                        (e_acc
                                           (e_var
                                              (varn_name
                                                 "mirroring_encap_standard_metadata"))
                                           "egress_rid") binop_eq
                                        (e_v
                                           (v_bit
                                              ([F; F; F; F; F; F; F; F; F; F;
                                                F; F; F; F; T; F],16)))))
                                  (stmt_block []
                                     (stmt_seq
                                        (stmt_ass lval_null
                                           (e_call
                                              (funn_ext "header" "setValid")
                                              [e_acc
                                                 (e_var
                                                    (varn_name
                                                       "mirroring_encap_headers"))
                                                 "mirror_encap_ethernet"]))
                                        (stmt_seq
                                           (stmt_ass
                                              (lval_field
                                                 (lval_field
                                                    (lval_varname
                                                       (varn_name
                                                          "mirroring_encap_headers"))
                                                    "mirror_encap_ethernet")
                                                 "src_addr")
                                              (e_acc
                                                 (e_var
                                                    (varn_name
                                                       "mirroring_encap_local_metadata"))
                                                 "mirror_encap_src_mac"))
                                           (stmt_seq
                                              (stmt_ass
                                                 (lval_field
                                                    (lval_field
                                                       (lval_varname
                                                          (varn_name
                                                             "mirroring_encap_headers"))
                                                       "mirror_encap_ethernet")
                                                    "dst_addr")
                                                 (e_acc
                                                    (e_var
                                                       (varn_name
                                                          "mirroring_encap_local_metadata"))
                                                    "mirror_encap_dst_mac"))
                                              (stmt_seq
                                                 (stmt_ass
                                                    (lval_field
                                                       (lval_field
                                                          (lval_varname
                                                             (varn_name
                                                                "mirroring_encap_headers"))
                                                          "mirror_encap_ethernet")
                                                       "ether_type")
                                                    (e_v
                                                       (v_bit
                                                          ([T; F; F; F; F; F;
                                                            F; T; F; F; F; F;
                                                            F; F; F; F],16))))
                                                 (stmt_seq
                                                    (stmt_ass lval_null
                                                       (e_call
                                                          (funn_ext "header"
                                                             "setValid")
                                                          [e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "mirroring_encap_headers"))
                                                             "mirror_encap_vlan"]))
                                                    (stmt_seq
                                                       (stmt_ass
                                                          (lval_field
                                                             (lval_field
                                                                (lval_varname
                                                                   (varn_name
                                                                      "mirroring_encap_headers"))
                                                                "mirror_encap_vlan")
                                                             "ether_type")
                                                          (e_v
                                                             (v_bit
                                                                ([T; F; F; F;
                                                                  F; T; T; F;
                                                                  T; T; F; T;
                                                                  T; T; F; T],
                                                                 16))))
                                                       (stmt_seq
                                                          (stmt_ass
                                                             (lval_field
                                                                (lval_field
                                                                   (lval_varname
                                                                      (varn_name
                                                                         "mirroring_encap_headers"))
                                                                   "mirror_encap_vlan")
                                                                "vlan_id")
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "mirroring_encap_local_metadata"))
                                                                "mirror_encap_vlan_id"))
                                                          (stmt_seq
                                                             (stmt_ass
                                                                lval_null
                                                                (e_call
                                                                   (funn_ext
                                                                      "header"
                                                                      "setValid")
                                                                   [e_acc
                                                                      (e_var
                                                                         (varn_name
                                                                            "mirroring_encap_headers"))
                                                                      "mirror_encap_ipv6"]))
                                                             (stmt_seq
                                                                (stmt_ass
                                                                   (lval_field
                                                                      (lval_field
                                                                         (lval_varname
                                                                            (varn_name
                                                                               "mirroring_encap_headers"))
                                                                         "mirror_encap_ipv6")
                                                                      "version")
                                                                   (e_v
                                                                      (v_bit
                                                                         ([F;
                                                                           T;
                                                                           T;
                                                                           F],
                                                                          4))))
                                                                (stmt_seq
                                                                   (stmt_ass
                                                                      (lval_field
                                                                         (lval_field
                                                                            (lval_varname
                                                                               (varn_name
                                                                                  "mirroring_encap_headers"))
                                                                            "mirror_encap_ipv6")
                                                                         "dscp")
                                                                      (e_v
                                                                         (v_bit
                                                                            ([F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F;
                                                                              F],
                                                                             6))))
                                                                   (stmt_seq
                                                                      (stmt_ass
                                                                         (lval_field
                                                                            (lval_field
                                                                               (lval_varname
                                                                                  (varn_name
                                                                                     "mirroring_encap_headers"))
                                                                               "mirror_encap_ipv6")
                                                                            "ecn")
                                                                         (e_v
                                                                            (v_bit
                                                                               ([F;
                                                                                 F],
                                                                                2))))
                                                                      (stmt_seq
                                                                         (stmt_ass
                                                                            (lval_field
                                                                               (lval_field
                                                                                  (lval_varname
                                                                                     (varn_name
                                                                                        "mirroring_encap_headers"))
                                                                                  "mirror_encap_ipv6")
                                                                               "hop_limit")
                                                                            (e_v
                                                                               (v_bit
                                                                                  ([F;
                                                                                    F;
                                                                                    F;
                                                                                    T;
                                                                                    F;
                                                                                    F;
                                                                                    F;
                                                                                    F],
                                                                                   8))))
                                                                         (stmt_seq
                                                                            (stmt_ass
                                                                               (lval_field
                                                                                  (lval_field
                                                                                     (lval_varname
                                                                                        (varn_name
                                                                                           "mirroring_encap_headers"))
                                                                                     "mirror_encap_ipv6")
                                                                                  "flow_label")
                                                                               (e_v
                                                                                  (v_bit
                                                                                     ([F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F;
                                                                                       F],
                                                                                      20))))
                                                                            (stmt_seq
                                                                               (stmt_ass
                                                                                  (lval_field
                                                                                     (lval_field
                                                                                        (lval_varname
                                                                                           (varn_name
                                                                                              "mirroring_encap_headers"))
                                                                                        "mirror_encap_ipv6")
                                                                                     "payload_length")
                                                                                  (e_binop
                                                                                     (e_binop
                                                                                        (e_binop
                                                                                           (e_cast
                                                                                              (cast_unsigned
                                                                                                 16)
                                                                                              (e_acc
                                                                                                 (e_var
                                                                                                    (varn_name
                                                                                                       "mirroring_encap_standard_metadata"))
                                                                                                 "packet_length"))
                                                                                           binop_add
                                                                                           (e_v
                                                                                              (v_bit
                                                                                                 ([F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F;
                                                                                                   T;
                                                                                                   F;
                                                                                                   F;
                                                                                                   F],
                                                                                                  16))))
                                                                                        binop_add
                                                                                        (e_v
                                                                                           (v_bit
                                                                                              ([F;
                                                                                                F;
                                                                                                F;
                                                                                                F;
                                                                                                F;
                                                                                                F;
                                                                                                F;
                                                                                                F;
                                                                                                F;
                                                                                                F;
                                                                                                F;
                                                                                                T;
                                                                                                F;
                                                                                                F;
                                                                                                F;
                                                                                                F],
                                                                                               16))))
                                                                                     binop_add
                                                                                     (e_v
                                                                                        (v_bit
                                                                                           ([F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             T;
                                                                                             T;
                                                                                             T;
                                                                                             F;
                                                                                             F],
                                                                                            16)))))
                                                                               (stmt_seq
                                                                                  (stmt_ass
                                                                                     (lval_field
                                                                                        (lval_field
                                                                                           (lval_varname
                                                                                              (varn_name
                                                                                                 "mirroring_encap_headers"))
                                                                                           "mirror_encap_ipv6")
                                                                                        "next_header")
                                                                                     (e_v
                                                                                        (v_bit
                                                                                           ([F;
                                                                                             F;
                                                                                             F;
                                                                                             T;
                                                                                             F;
                                                                                             F;
                                                                                             F;
                                                                                             T],
                                                                                            8))))
                                                                                  (stmt_seq
                                                                                     (stmt_ass
                                                                                        (lval_field
                                                                                           (lval_field
                                                                                              (lval_varname
                                                                                                 (varn_name
                                                                                                    "mirroring_encap_headers"))
                                                                                              "mirror_encap_ipv6")
                                                                                           "src_addr")
                                                                                        (e_acc
                                                                                           (e_var
                                                                                              (varn_name
                                                                                                 "mirroring_encap_local_metadata"))
                                                                                           "mirror_encap_src_ip"))
                                                                                     (stmt_seq
                                                                                        (stmt_ass
                                                                                           (lval_field
                                                                                              (lval_field
                                                                                                 (lval_varname
                                                                                                    (varn_name
                                                                                                       "mirroring_encap_headers"))
                                                                                                 "mirror_encap_ipv6")
                                                                                              "dst_addr")
                                                                                           (e_acc
                                                                                              (e_var
                                                                                                 (varn_name
                                                                                                    "mirroring_encap_local_metadata"))
                                                                                              "mirror_encap_dst_ip"))
                                                                                        (stmt_seq
                                                                                           (stmt_ass
                                                                                              lval_null
                                                                                              (e_call
                                                                                                 (funn_ext
                                                                                                    "header"
                                                                                                    "setValid")
                                                                                                 [e_acc
                                                                                                    (e_var
                                                                                                       (varn_name
                                                                                                          "mirroring_encap_headers"))
                                                                                                    "mirror_encap_udp"]))
                                                                                           (stmt_seq
                                                                                              (stmt_ass
                                                                                                 (lval_field
                                                                                                    (lval_field
                                                                                                       (lval_varname
                                                                                                          (varn_name
                                                                                                             "mirroring_encap_headers"))
                                                                                                       "mirror_encap_udp")
                                                                                                    "src_port")
                                                                                                 (e_acc
                                                                                                    (e_var
                                                                                                       (varn_name
                                                                                                          "mirroring_encap_local_metadata"))
                                                                                                    "mirror_encap_udp_src_port"))
                                                                                              (stmt_seq
                                                                                                 (stmt_ass
                                                                                                    (lval_field
                                                                                                       (lval_field
                                                                                                          (lval_varname
                                                                                                             (varn_name
                                                                                                                "mirroring_encap_headers"))
                                                                                                          "mirror_encap_udp")
                                                                                                       "dst_port")
                                                                                                    (e_acc
                                                                                                       (e_var
                                                                                                          (varn_name
                                                                                                             "mirroring_encap_local_metadata"))
                                                                                                       "mirror_encap_udp_dst_port"))
                                                                                                 (stmt_seq
                                                                                                    (stmt_ass
                                                                                                       (lval_field
                                                                                                          (lval_field
                                                                                                             (lval_varname
                                                                                                                (varn_name
                                                                                                                   "mirroring_encap_headers"))
                                                                                                             "mirror_encap_udp")
                                                                                                          "hdr_length")
                                                                                                       (e_acc
                                                                                                          (e_acc
                                                                                                             (e_var
                                                                                                                (varn_name
                                                                                                                   "mirroring_encap_headers"))
                                                                                                             "mirror_encap_ipv6")
                                                                                                          "payload_length"))
                                                                                                    (stmt_seq
                                                                                                       (stmt_ass
                                                                                                          (lval_field
                                                                                                             (lval_field
                                                                                                                (lval_varname
                                                                                                                   (varn_name
                                                                                                                      "mirroring_encap_headers"))
                                                                                                                "mirror_encap_udp")
                                                                                                             "checksum")
                                                                                                          (e_v
                                                                                                             (v_bit
                                                                                                                ([F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F;
                                                                                                                  F],
                                                                                                                 16))))
                                                                                                       (stmt_seq
                                                                                                          (stmt_ass
                                                                                                             lval_null
                                                                                                             (e_call
                                                                                                                (funn_ext
                                                                                                                   "header"
                                                                                                                   "setValid")
                                                                                                                [e_acc
                                                                                                                   (e_var
                                                                                                                      (varn_name
                                                                                                                         "mirroring_encap_headers"))
                                                                                                                   "ipfix"]))
                                                                                                          (stmt_ass
                                                                                                             lval_null
                                                                                                             (e_call
                                                                                                                (funn_ext
                                                                                                                   "header"
                                                                                                                   "setValid")
                                                                                                                [e_acc
                                                                                                                   (e_var
                                                                                                                      (varn_name
                                                                                                                         "mirroring_encap_headers"))
                                                                                                                   "psamp_extended"]))))))))))))))))))))))))))
                                  stmt_empty))
                            (stmt_seq
                               (stmt_seq
                                  (stmt_ass
                                     (lval_varname (varn_name "headers"))
                                     (e_var
                                        (varn_name "mirroring_encap_headers")))
                                  (stmt_ass
                                     (lval_varname
                                        (varn_name "local_metadata"))
                                     (e_var
                                        (varn_name
                                           "mirroring_encap_local_metadata"))))
                               (stmt_ass
                                  (lval_varname
                                     (varn_name "standard_metadata"))
                                  (e_var
                                     (varn_name
                                        "mirroring_encap_standard_metadata"))))))
                      (stmt_seq
                         (stmt_seq
                            (stmt_seq
                               (stmt_seq
                                  (stmt_ass
                                     (lval_varname
                                        (varn_name
                                           "egress_vlan_checks_headers"))
                                     (e_var (varn_name "headers")))
                                  (stmt_ass
                                     (lval_varname
                                        (varn_name
                                           "egress_vlan_checks_local_metadata"))
                                     (e_var (varn_name "local_metadata"))))
                               (stmt_ass
                                  (lval_varname
                                     (varn_name
                                        "egress_vlan_checks_standard_metadata"))
                                  (e_var (varn_name "standard_metadata"))))
                            (stmt_seq
                               (stmt_seq stmt_empty
                                  (stmt_cond
                                     (e_acc
                                        (e_var
                                           (varn_name
                                              "egress_vlan_checks_local_metadata"))
                                        "enable_vlan_checks")
                                     (stmt_block []
                                        (stmt_cond
                                           (e_binop
                                              (e_binop
                                                 (e_binop
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "egress_vlan_checks_standard_metadata"))
                                                       "instance_type")
                                                    binop_eq
                                                    (e_v
                                                       (v_bit
                                                          ([F; F; F; F; F; F;
                                                            F; F; F; F; F; F;
                                                            F; F; F; F; F; F;
                                                            F; F; F; F; F; F;
                                                            F; F; F; F; F; F;
                                                            F; T],32))))
                                                 binop_bin_and
                                                 (e_binop
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "egress_vlan_checks_standard_metadata"))
                                                       "egress_rid") binop_eq
                                                    (e_v
                                                       (v_bit
                                                          ([F; F; F; F; F; F;
                                                            F; F; F; F; F; F;
                                                            F; F; T; F],16)))))
                                              binop_bin_and
                                              (e_unop unop_neg
                                                 (e_binop
                                                    (e_binop
                                                       (e_acc
                                                          (e_var
                                                             (varn_name
                                                                "egress_vlan_checks_local_metadata"))
                                                          "mirror_encap_vlan_id")
                                                       binop_eq
                                                       (e_v
                                                          (v_bit
                                                             ([F; F; F; F; F;
                                                               F; F; F; F; F;
                                                               F; F],12))))
                                                    binop_bin_or
                                                    (e_binop
                                                       (e_acc
                                                          (e_var
                                                             (varn_name
                                                                "egress_vlan_checks_local_metadata"))
                                                          "mirror_encap_vlan_id")
                                                       binop_eq
                                                       (e_v
                                                          (v_bit
                                                             ([T; T; T; T; T;
                                                               T; T; T; T; T;
                                                               T; T],12)))))))
                                           (stmt_block []
                                              (stmt_ass lval_null
                                                 (e_call
                                                    (funn_ext ""
                                                       "mark_to_drop")
                                                    [e_var
                                                       (varn_name
                                                          "egress_vlan_checks_standard_metadata")])))
                                           (stmt_cond
                                              (e_binop
                                                 (e_unop unop_neg
                                                    (e_binop
                                                       (e_binop
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "egress_vlan_checks_standard_metadata"))
                                                             "instance_type")
                                                          binop_eq
                                                          (e_v
                                                             (v_bit
                                                                ([F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; T],
                                                                 32))))
                                                       binop_bin_and
                                                       (e_binop
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "egress_vlan_checks_standard_metadata"))
                                                             "egress_rid")
                                                          binop_eq
                                                          (e_v
                                                             (v_bit
                                                                ([F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; T],
                                                                 16))))))
                                                 binop_bin_and
                                                 (e_unop unop_neg
                                                    (e_binop
                                                       (e_binop
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "egress_vlan_checks_local_metadata"))
                                                             "vlan_id")
                                                          binop_eq
                                                          (e_v
                                                             (v_bit
                                                                ([F; F; F; F;
                                                                  F; F; F; F;
                                                                  F; F; F; F],
                                                                 12))))
                                                       binop_bin_or
                                                       (e_binop
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "egress_vlan_checks_local_metadata"))
                                                             "vlan_id")
                                                          binop_eq
                                                          (e_v
                                                             (v_bit
                                                                ([T; T; T; T;
                                                                  T; T; T; T;
                                                                  T; T; T; T],
                                                                 12)))))))
                                              (stmt_block []
                                                 (stmt_ass lval_null
                                                    (e_call
                                                       (funn_ext ""
                                                          "mark_to_drop")
                                                       [e_var
                                                          (varn_name
                                                             "egress_vlan_checks_standard_metadata")])))
                                              stmt_empty))) stmt_empty))
                               (stmt_seq
                                  (stmt_seq
                                     (stmt_ass
                                        (lval_varname (varn_name "headers"))
                                        (e_var
                                           (varn_name
                                              "egress_vlan_checks_headers")))
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name "local_metadata"))
                                        (e_var
                                           (varn_name
                                              "egress_vlan_checks_local_metadata"))))
                                  (stmt_ass
                                     (lval_varname
                                        (varn_name "standard_metadata"))
                                     (e_var
                                        (varn_name
                                           "egress_vlan_checks_standard_metadata"))))))
                         (stmt_seq
                            (stmt_seq
                               (stmt_seq
                                  (stmt_seq
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name "vlan_tag_headers"))
                                        (e_var (varn_name "headers")))
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name
                                              "vlan_tag_local_metadata"))
                                        (e_var (varn_name "local_metadata"))))
                                  (stmt_ass
                                     (lval_varname
                                        (varn_name
                                           "vlan_tag_standard_metadata"))
                                     (e_var (varn_name "standard_metadata"))))
                               (stmt_seq
                                  (stmt_seq stmt_empty
                                     (stmt_cond
                                        (e_binop
                                           (e_unop unop_neg
                                              (e_binop
                                                 (e_binop
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "vlan_tag_local_metadata"))
                                                       "vlan_id") binop_eq
                                                    (e_v
                                                       (v_bit
                                                          ([F; F; F; F; F; F;
                                                            F; F; F; F; F; F],
                                                           12))))
                                                 binop_bin_or
                                                 (e_binop
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "vlan_tag_local_metadata"))
                                                       "vlan_id") binop_eq
                                                    (e_v
                                                       (v_bit
                                                          ([T; T; T; T; T; T;
                                                            T; T; T; T; T; T],
                                                           12))))))
                                           binop_bin_and
                                           (e_unop unop_neg
                                              (e_binop
                                                 (e_binop
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "vlan_tag_standard_metadata"))
                                                       "instance_type")
                                                    binop_eq
                                                    (e_v
                                                       (v_bit
                                                          ([F; F; F; F; F; F;
                                                            F; F; F; F; F; F;
                                                            F; F; F; F; F; F;
                                                            F; F; F; F; F; F;
                                                            F; F; F; F; F; F;
                                                            F; T],32))))
                                                 binop_bin_and
                                                 (e_binop
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "vlan_tag_standard_metadata"))
                                                       "egress_rid") binop_eq
                                                    (e_v
                                                       (v_bit
                                                          ([F; F; F; F; F; F;
                                                            F; F; F; F; F; F;
                                                            F; F; T; F],16)))))))
                                        (stmt_block []
                                           (stmt_seq
                                              (stmt_ass lval_null
                                                 (e_call
                                                    (funn_ext "header"
                                                       "setValid")
                                                    [e_acc
                                                       (e_var
                                                          (varn_name
                                                             "vlan_tag_headers"))
                                                       "vlan"]))
                                              (stmt_seq
                                                 (stmt_ass
                                                    (lval_field
                                                       (lval_field
                                                          (lval_varname
                                                             (varn_name
                                                                "vlan_tag_headers"))
                                                          "vlan")
                                                       "priority_code_point")
                                                    (e_v
                                                       (v_bit ([F; F; F],3))))
                                                 (stmt_seq
                                                    (stmt_ass
                                                       (lval_field
                                                          (lval_field
                                                             (lval_varname
                                                                (varn_name
                                                                   "vlan_tag_headers"))
                                                             "vlan")
                                                          "drop_eligible_indicator")
                                                       (e_v (v_bit ([F],1))))
                                                    (stmt_seq
                                                       (stmt_ass
                                                          (lval_field
                                                             (lval_field
                                                                (lval_varname
                                                                   (varn_name
                                                                      "vlan_tag_headers"))
                                                                "vlan")
                                                             "vlan_id")
                                                          (e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "vlan_tag_local_metadata"))
                                                             "vlan_id"))
                                                       (stmt_seq
                                                          (stmt_ass
                                                             (lval_field
                                                                (lval_field
                                                                   (lval_varname
                                                                      (varn_name
                                                                         "vlan_tag_headers"))
                                                                   "vlan")
                                                                "ether_type")
                                                             (e_acc
                                                                (e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "vlan_tag_headers"))
                                                                   "ethernet")
                                                                "ether_type"))
                                                          (stmt_ass
                                                             (lval_field
                                                                (lval_field
                                                                   (lval_varname
                                                                      (varn_name
                                                                         "vlan_tag_headers"))
                                                                   "ethernet")
                                                                "ether_type")
                                                             (e_v
                                                                (v_bit
                                                                   ([T; F; F;
                                                                     F; F; F;
                                                                     F; T; F;
                                                                     F; F; F;
                                                                     F; F; F;
                                                                     F],16))))))))))
                                        stmt_empty))
                                  (stmt_seq
                                     (stmt_seq
                                        (stmt_ass
                                           (lval_varname
                                              (varn_name "headers"))
                                           (e_var
                                              (varn_name "vlan_tag_headers")))
                                        (stmt_ass
                                           (lval_varname
                                              (varn_name "local_metadata"))
                                           (e_var
                                              (varn_name
                                                 "vlan_tag_local_metadata"))))
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name "standard_metadata"))
                                        (e_var
                                           (varn_name
                                              "vlan_tag_standard_metadata"))))))
                            (stmt_seq
                               (stmt_seq
                                  (stmt_seq
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name "acl_egress_headers"))
                                        (e_var (varn_name "headers")))
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name
                                              "acl_egress_local_metadata"))
                                        (e_var (varn_name "local_metadata"))))
                                  (stmt_ass
                                     (lval_varname
                                        (varn_name
                                           "acl_egress_standard_metadata"))
                                     (e_var (varn_name "standard_metadata"))))
                               (stmt_seq
                                  (stmt_seq
                                     (stmt_seq
                                        (stmt_seq
                                           (stmt_seq
                                              (stmt_seq stmt_empty
                                                 (stmt_ass
                                                    (lval_varname
                                                       (varn_name
                                                          "acl_egress_dscp"))
                                                    (e_v
                                                       (v_bit
                                                          ([F; F; F; F; F; F],
                                                           6)))))
                                              (stmt_ass
                                                 (lval_varname
                                                    (varn_name
                                                       "acl_egress_ip_protocol"))
                                                 (e_v
                                                    (v_bit
                                                       ([F; F; F; F; F; F; F;
                                                         F],8)))))
                                           (stmt_ass lval_null
                                              (e_call
                                                 (funn_inst "direct_counter")
                                                 [e_var
                                                    (varn_name
                                                       "acl_egress_acl_egress_counter");
                                                  e_v
                                                    (v_bit
                                                       ([F; F; F; F; F; F; F;
                                                         F; F; F; F; F; F; F;
                                                         F; F; F; F; F; F; F;
                                                         F; F; F; F; F; F; F;
                                                         F; F; T; F],32))])))
                                        (stmt_ass lval_null
                                           (e_call
                                              (funn_inst "direct_counter")
                                              [e_var
                                                 (varn_name
                                                    "acl_egress_acl_egress_dhcp_to_host_counter");
                                               e_v
                                                 (v_bit
                                                    ([F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; F; F;
                                                      F; F; F; F; F; F; T; F],
                                                     32))])))
                                     (stmt_cond
                                        (e_binop
                                           (e_acc
                                              (e_var
                                                 (varn_name
                                                    "acl_egress_standard_metadata"))
                                              "egress_port") binop_neq
                                           (e_v
                                              (v_bit
                                                 ([T; T; T; T; T; T; T; T; F],
                                                  9))))
                                        (stmt_block []
                                           (stmt_seq
                                              (stmt_cond
                                                 (e_call
                                                    (funn_ext "header"
                                                       "isValid")
                                                    [e_acc
                                                       (e_var
                                                          (varn_name
                                                             "acl_egress_headers"))
                                                       "ipv4"])
                                                 (stmt_block []
                                                    (stmt_seq
                                                       (stmt_ass
                                                          (lval_varname
                                                             (varn_name
                                                                "acl_egress_dscp"))
                                                          (e_acc
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_egress_headers"))
                                                                "ipv4")
                                                             "dscp"))
                                                       (stmt_ass
                                                          (lval_varname
                                                             (varn_name
                                                                "acl_egress_ip_protocol"))
                                                          (e_acc
                                                             (e_acc
                                                                (e_var
                                                                   (varn_name
                                                                      "acl_egress_headers"))
                                                                "ipv4")
                                                             "protocol"))))
                                                 (stmt_cond
                                                    (e_call
                                                       (funn_ext "header"
                                                          "isValid")
                                                       [e_acc
                                                          (e_var
                                                             (varn_name
                                                                "acl_egress_headers"))
                                                          "ipv6"])
                                                    (stmt_block []
                                                       (stmt_seq
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "acl_egress_dscp"))
                                                             (e_acc
                                                                (e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "acl_egress_headers"))
                                                                   "ipv6")
                                                                "dscp"))
                                                          (stmt_ass
                                                             (lval_varname
                                                                (varn_name
                                                                   "acl_egress_ip_protocol"))
                                                             (e_acc
                                                                (e_acc
                                                                   (e_var
                                                                      (varn_name
                                                                         "acl_egress_headers"))
                                                                   "ipv6")
                                                                "next_header"))))
                                                    (stmt_block []
                                                       (stmt_ass
                                                          (lval_varname
                                                             (varn_name
                                                                "acl_egress_ip_protocol"))
                                                          (e_v
                                                             (v_bit
                                                                ([F; F; F; F;
                                                                  F; F; F; F],
                                                                 8)))))))
                                              (stmt_seq
                                                 (stmt_app
                                                    "acl_egress.acl_egress_table"
                                                    [e_acc
                                                       (e_acc
                                                          (e_var
                                                             (varn_name
                                                                "acl_egress_headers"))
                                                          "ethernet")
                                                       "ether_type";
                                                     e_var
                                                       (varn_name
                                                          "acl_egress_ip_protocol");
                                                     e_acc
                                                       (e_var
                                                          (varn_name
                                                             "acl_egress_local_metadata"))
                                                       "l4_dst_port";
                                                     e_cast (cast_unsigned 9)
                                                       (e_acc
                                                          (e_var
                                                             (varn_name
                                                                "acl_egress_standard_metadata"))
                                                          "egress_port");
                                                     e_binop
                                                       (e_call
                                                          (funn_ext "header"
                                                             "isValid")
                                                          [e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "acl_egress_headers"))
                                                             "ipv4"])
                                                       binop_bin_or
                                                       (e_call
                                                          (funn_ext "header"
                                                             "isValid")
                                                          [e_acc
                                                             (e_var
                                                                (varn_name
                                                                   "acl_egress_headers"))
                                                             "ipv6"]);
                                                     e_call
                                                       (funn_ext "header"
                                                          "isValid")
                                                       [e_acc
                                                          (e_var
                                                             (varn_name
                                                                "acl_egress_headers"))
                                                          "ipv4"];
                                                     e_call
                                                       (funn_ext "header"
                                                          "isValid")
                                                       [e_acc
                                                          (e_var
                                                             (varn_name
                                                                "acl_egress_headers"))
                                                          "ipv6"];
                                                     e_var
                                                       (varn_name
                                                          "acl_egress_dscp")])
                                                 (stmt_cond
                                                    (e_acc
                                                       (e_var
                                                          (varn_name
                                                             "acl_egress_local_metadata"))
                                                       "acl_drop")
                                                    (stmt_block []
                                                       (stmt_ass lval_null
                                                          (e_call
                                                             (funn_ext ""
                                                                "mark_to_drop")
                                                             [e_var
                                                                (varn_name
                                                                   "acl_egress_standard_metadata")])))
                                                    stmt_empty)))) stmt_empty))
                                  (stmt_seq
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name "local_metadata"))
                                        (e_var
                                           (varn_name
                                              "acl_egress_local_metadata")))
                                     (stmt_ass
                                        (lval_varname
                                           (varn_name "standard_metadata"))
                                        (e_var
                                           (varn_name
                                              "acl_egress_standard_metadata")))))))))))
             stmt_empty)),[])],
   [(varn_name "acl_egress_dscp",tau_bit 6,NONE);
    (varn_name "acl_egress_ip_protocol",tau_bit 8,NONE);
    (varn_name "acl_egress_acl_egress_counter",tau_ext,NONE);
    (varn_name "acl_egress_acl_egress_dhcp_to_host_counter",tau_ext,NONE);
    (varn_name "acl_egress_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "acl_egress_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "acl_egress_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "vlan_tag_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "vlan_tag_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "vlan_tag_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "egress_vlan_checks_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "egress_vlan_checks_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "egress_vlan_checks_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "mirroring_encap_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "mirroring_encap_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "mirroring_encap_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "packet_rewrites_multicast_rewrites_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "packet_rewrites_multicast_rewrites_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name
       "packet_rewrites_multicast_rewrites_multicast_replica_instance",
     tau_bit 16,NONE);
    (varn_name "packet_rewrites_multicast_rewrites_multicast_replica_port",
     tau_bit 9,NONE);
    (varn_name "packet_rewrites_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "packet_rewrites_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "packet_rewrites_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE);
    (varn_name "packet_in_encap_standard_metadata",
     tau_xtl struct_ty_struct
       [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
        ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
        ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
        ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
        ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
        ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
        ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
        ("parser_error",tau_bit 32); ("priority",tau_bit 3)],NONE);
    (varn_name "packet_in_encap_local_metadata",
     tau_xtl struct_ty_struct
       [("enable_vlan_checks",tau_bool); ("vlan_id",tau_bit 12);
        ("admit_to_l3",tau_bool); ("vrf_id",tau_bit 10);
        ("enable_decrement_ttl",tau_bool);
        ("enable_src_mac_rewrite",tau_bool);
        ("enable_dst_mac_rewrite",tau_bool);
        ("enable_vlan_rewrite",tau_bool);
        ("packet_rewrites",
         tau_xtl struct_ty_struct
           [("src_mac",tau_bit 48); ("dst_mac",tau_bit 48);
            ("vlan_id",tau_bit 12)]); ("l4_src_port",tau_bit 16);
        ("l4_dst_port",tau_bit 16); ("wcmp_selector_input",tau_bit 16);
        ("apply_tunnel_decap_at_end_of_pre_ingress",tau_bool);
        ("apply_tunnel_encap_at_egress",tau_bool);
        ("tunnel_encap_src_ipv6",tau_bit 128);
        ("tunnel_encap_dst_ipv6",tau_bit 128); ("marked_to_copy",tau_bool);
        ("marked_to_mirror",tau_bool); ("mirror_session_id",tau_bit 10);
        ("mirror_egress_port",tau_bit 9);
        ("mirror_encap_src_mac",tau_bit 48);
        ("mirror_encap_dst_mac",tau_bit 48);
        ("mirror_encap_vlan_id",tau_bit 12);
        ("mirror_encap_src_ip",tau_bit 128);
        ("mirror_encap_dst_ip",tau_bit 128);
        ("mirror_encap_udp_src_port",tau_bit 16);
        ("mirror_encap_udp_dst_port",tau_bit 16);
        ("packet_in_ingress_port",tau_bit 9);
        ("packet_in_target_egress_port",tau_bit 9); ("color",tau_bit 2);
        ("ingress_port",tau_bit 9); ("route_metadata",tau_bit 6);
        ("acl_metadata",tau_bit 8); ("bypass_ingress",tau_bool);
        ("wcmp_group_id_valid",tau_bool); ("wcmp_group_id_value",tau_bit 12);
        ("nexthop_id_valid",tau_bool); ("nexthop_id_value",tau_bit 10);
        ("ipmc_table_hit",tau_bool); ("acl_drop",tau_bool)],NONE);
    (varn_name "packet_in_encap_headers",
     tau_xtl struct_ty_struct
       [("packet_out_header",
         tau_xtl struct_ty_header
           [("egress_port",tau_bit 9); ("submit_to_ingress",tau_bit 1);
            ("unused_pad",tau_bit 6)]);
        ("mirror_encap_ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("mirror_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("mirror_encap_udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("ipfix",
         tau_xtl struct_ty_header
           [("version_number",tau_bit 16); ("length",tau_bit 16);
            ("export_time",tau_bit 32); ("sequence_number",tau_bit 32);
            ("observation_domain_id",tau_bit 32)]);
        ("psamp_extended",
         tau_xtl struct_ty_header
           [("template_id",tau_bit 16); ("length",tau_bit 16);
            ("observation_time",tau_bit 64); ("flowset",tau_bit 16);
            ("next_hop_index",tau_bit 16); ("epoch",tau_bit 16);
            ("ingress_port",tau_bit 16); ("egress_port",tau_bit 16);
            ("user_meta_field",tau_bit 16); ("dlb_id",tau_bit 8);
            ("variable_length",tau_bit 8);
            ("packet_sampled_length",tau_bit 16)]);
        ("ethernet",
         tau_xtl struct_ty_header
           [("dst_addr",tau_bit 48); ("src_addr",tau_bit 48);
            ("ether_type",tau_bit 16)]);
        ("vlan",
         tau_xtl struct_ty_header
           [("priority_code_point",tau_bit 3);
            ("drop_eligible_indicator",tau_bit 1); ("vlan_id",tau_bit 12);
            ("ether_type",tau_bit 16)]);
        ("tunnel_encap_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("tunnel_encap_gre",
         tau_xtl struct_ty_header
           [("checksum_present",tau_bit 1); ("routing_present",tau_bit 1);
            ("key_present",tau_bit 1); ("sequence_present",tau_bit 1);
            ("strict_source_route",tau_bit 1);
            ("recursion_control",tau_bit 3);
            ("acknowledgement_present",tau_bit 1); ("flags",tau_bit 4);
            ("version",tau_bit 3); ("protocol",tau_bit 16)]);
        ("ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("inner_ipv4",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("ihl",tau_bit 4); ("dscp",tau_bit 6);
            ("ecn",tau_bit 2); ("total_len",tau_bit 16);
            ("identification",tau_bit 16); ("reserved",tau_bit 1);
            ("do_not_fragment",tau_bit 1); ("more_fragments",tau_bit 1);
            ("frag_offset",tau_bit 13); ("ttl",tau_bit 8);
            ("protocol",tau_bit 8); ("header_checksum",tau_bit 16);
            ("src_addr",tau_bit 32); ("dst_addr",tau_bit 32)]);
        ("inner_ipv6",
         tau_xtl struct_ty_header
           [("version",tau_bit 4); ("dscp",tau_bit 6); ("ecn",tau_bit 2);
            ("flow_label",tau_bit 20); ("payload_length",tau_bit 16);
            ("next_header",tau_bit 8); ("hop_limit",tau_bit 8);
            ("src_addr",tau_bit 128); ("dst_addr",tau_bit 128)]);
        ("icmp",
         tau_xtl struct_ty_header
           [("type",tau_bit 8); ("code",tau_bit 8); ("checksum",tau_bit 16);
            ("rest_of_header",tau_bit 32)]);
        ("tcp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("seq_no",tau_bit 32); ("ack_no",tau_bit 32);
            ("data_offset",tau_bit 4); ("res",tau_bit 4);
            ("flags",tau_bit 8); ("window",tau_bit 16);
            ("checksum",tau_bit 16); ("urgent_ptr",tau_bit 16)]);
        ("udp",
         tau_xtl struct_ty_header
           [("src_port",tau_bit 16); ("dst_port",tau_bit 16);
            ("hdr_length",tau_bit 16); ("checksum",tau_bit 16)]);
        ("arp",
         tau_xtl struct_ty_header
           [("hw_type",tau_bit 16); ("proto_type",tau_bit 16);
            ("hw_addr_len",tau_bit 8); ("proto_addr_len",tau_bit 8);
            ("opcode",tau_bit 16); ("sender_hw_addr",tau_bit 48);
            ("sender_proto_addr",tau_bit 32); ("target_hw_addr",tau_bit 48);
            ("target_proto_addr",tau_bit 32)])],NONE)],[],
   [("acl_egress.acl_egress_table",
     [mk_ternary; mk_ternary; mk_ternary; mk_optional; mk_optional;
      mk_optional; mk_optional; mk_ternary],"NoAction",
     [e_v (v_bool T); e_v (v_bool F)]);
    ("acl_egress.acl_egress_dhcp_to_host_table",
     [mk_optional; mk_optional; mk_optional; mk_ternary; mk_ternary;
      mk_optional],"NoAction",[e_v (v_bool T); e_v (v_bool F)]);
    ("packet_rewrites.multicast_rewrites.multicast_router_interface_table",
     [mk_exact; mk_exact],"NoAction",[e_v (v_bool T); e_v (v_bool F)])])],
 [("postparser",ffblock_ff v1model_postparser); ("preingress",ffblock_ff v1model_preingress)],
 v1model_input_f
   (v_struct
      [("packet_out_header",
        v_header F
          [("egress_port",
            v_bit ([F; F; F; F; F; F; F; F; F],9));
           ("submit_to_ingress",v_bit ([F],1));
           ("unused_pad",v_bit ([F; F; F; F; F; F],6))]);
       ("mirror_encap_ethernet",
        v_header F
          [("dst_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F],
               48));
           ("src_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F],
               48));
           ("ether_type",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16))]);
       ("mirror_encap_vlan",
        v_header F
          [("priority_code_point",v_bit ([F; F; F],3));
           ("drop_eligible_indicator",v_bit ([F],1));
           ("vlan_id",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F],
               12));
           ("ether_type",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16))]);
       ("mirror_encap_ipv6",
        v_header F
          [("version",v_bit ([F; F; F; F],4));
           ("dscp",v_bit ([F; F; F; F; F; F],6));
           ("ecn",v_bit ([F; F],2));
           ("flow_label",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],20));
           ("payload_length",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("next_header",v_bit ([F; F; F; F; F; F; F; F],8));
           ("hop_limit",v_bit ([F; F; F; F; F; F; F; F],8));
           ("src_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],128));
           ("dst_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],128))]);
       ("mirror_encap_udp",
        v_header F
          [("src_port",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("dst_port",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("hdr_length",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("checksum",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16))]);
       ("ipfix",
        v_header F
          [("version_number",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("length",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("export_time",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32));
           ("sequence_number",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32));
           ("observation_domain_id",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32))]);
       ("psamp_extended",
        v_header F
          [("template_id",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("length",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("observation_time",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],64));
           ("flowset",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("next_hop_index",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("epoch",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("ingress_port",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("egress_port",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("user_meta_field",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("dlb_id",v_bit ([F; F; F; F; F; F; F; F],8));
           ("variable_length",
            v_bit ([F; F; F; F; F; F; F; F],8));
           ("packet_sampled_length",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16))]);
       ("ethernet",
        v_header F
          [("dst_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F],
               48));
           ("src_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F],
               48));
           ("ether_type",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16))]);
       ("vlan",
        v_header F
          [("priority_code_point",v_bit ([F; F; F],3));
           ("drop_eligible_indicator",v_bit ([F],1));
           ("vlan_id",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F],
               12));
           ("ether_type",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16))]);
       ("tunnel_encap_ipv6",
        v_header F
          [("version",v_bit ([F; F; F; F],4));
           ("dscp",v_bit ([F; F; F; F; F; F],6));
           ("ecn",v_bit ([F; F],2));
           ("flow_label",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],20));
           ("payload_length",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("next_header",v_bit ([F; F; F; F; F; F; F; F],8));
           ("hop_limit",v_bit ([F; F; F; F; F; F; F; F],8));
           ("src_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],128));
           ("dst_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],128))]);
       ("tunnel_encap_gre",
        v_header F
          [("checksum_present",v_bit ([F],1));
           ("routing_present",v_bit ([F],1));
           ("key_present",v_bit ([F],1));
           ("sequence_present",v_bit ([F],1));
           ("strict_source_route",v_bit ([F],1));
           ("recursion_control",v_bit ([F; F; F],3));
           ("acknowledgement_present",v_bit ([F],1));
           ("flags",v_bit ([F; F; F; F],4));
           ("version",v_bit ([F; F; F],3));
           ("protocol",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16))]);
       ("ipv4",
        v_header F
          [("version",v_bit ([F; F; F; F],4));
           ("ihl",v_bit ([F; F; F; F],4));
           ("dscp",v_bit ([F; F; F; F; F; F],6));
           ("ecn",v_bit ([F; F],2));
           ("total_len",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("identification",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16)); ("reserved",v_bit ([F],1));
           ("do_not_fragment",v_bit ([F],1));
           ("more_fragments",v_bit ([F],1));
           ("frag_offset",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F],13));
           ("ttl",v_bit ([F; F; F; F; F; F; F; F],8));
           ("protocol",v_bit ([F; F; F; F; F; F; F; F],8));
           ("header_checksum",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("src_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32));
           ("dst_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32))]);
       ("ipv6",
        v_header F
          [("version",v_bit ([F; F; F; F],4));
           ("dscp",v_bit ([F; F; F; F; F; F],6));
           ("ecn",v_bit ([F; F],2));
           ("flow_label",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],20));
           ("payload_length",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("next_header",v_bit ([F; F; F; F; F; F; F; F],8));
           ("hop_limit",v_bit ([F; F; F; F; F; F; F; F],8));
           ("src_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],128));
           ("dst_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],128))]);
       ("inner_ipv4",
        v_header F
          [("version",v_bit ([F; F; F; F],4));
           ("ihl",v_bit ([F; F; F; F],4));
           ("dscp",v_bit ([F; F; F; F; F; F],6));
           ("ecn",v_bit ([F; F],2));
           ("total_len",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("identification",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16)); ("reserved",v_bit ([F],1));
           ("do_not_fragment",v_bit ([F],1));
           ("more_fragments",v_bit ([F],1));
           ("frag_offset",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F],13));
           ("ttl",v_bit ([F; F; F; F; F; F; F; F],8));
           ("protocol",v_bit ([F; F; F; F; F; F; F; F],8));
           ("header_checksum",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("src_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32));
           ("dst_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32))]);
       ("inner_ipv6",
        v_header F
          [("version",v_bit ([F; F; F; F],4));
           ("dscp",v_bit ([F; F; F; F; F; F],6));
           ("ecn",v_bit ([F; F],2));
           ("flow_label",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],20));
           ("payload_length",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("next_header",v_bit ([F; F; F; F; F; F; F; F],8));
           ("hop_limit",v_bit ([F; F; F; F; F; F; F; F],8));
           ("src_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],128));
           ("dst_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],128))]);
       ("icmp",
        v_header F
          [("type",v_bit ([F; F; F; F; F; F; F; F],8));
           ("code",v_bit ([F; F; F; F; F; F; F; F],8));
           ("checksum",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("rest_of_header",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32))]);
       ("tcp",
        v_header F
          [("src_port",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("dst_port",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("seq_no",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32));
           ("ack_no",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32));
           ("data_offset",v_bit ([F; F; F; F],4));
           ("res",v_bit ([F; F; F; F],4));
           ("flags",v_bit ([F; F; F; F; F; F; F; F],8));
           ("window",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("checksum",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("urgent_ptr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16))]);
       ("udp",
        v_header F
          [("src_port",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("dst_port",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("hdr_length",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("checksum",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16))]);
       ("arp",
        v_header F
          [("hw_type",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("proto_type",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("hw_addr_len",v_bit ([F; F; F; F; F; F; F; F],8));
           ("proto_addr_len",
            v_bit ([F; F; F; F; F; F; F; F],8));
           ("opcode",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F],16));
           ("sender_hw_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F],
               48));
           ("sender_proto_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32));
           ("target_hw_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F],
               48));
           ("target_proto_addr",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F],32))])],
    v_struct
      [("enable_vlan_checks",v_bool F);
       ("vlan_id",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F],12));
       ("admit_to_l3",v_bool F);
       ("vrf_id",
        v_bit ([F; F; F; F; F; F; F; F; F; F],10));
       ("enable_decrement_ttl",v_bool F);
       ("enable_src_mac_rewrite",v_bool F);
       ("enable_dst_mac_rewrite",v_bool F);
       ("enable_vlan_rewrite",v_bool F);
       ("packet_rewrites",
        v_struct
          [("src_mac",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F],
               48));
           ("dst_mac",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F;
                F; F; F; F; F; F; F; F; F; F; F; F],
               48));
           ("vlan_id",
            v_bit
              ([F; F; F; F; F; F; F; F; F; F; F; F],
               12))]);
       ("l4_src_port",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F],16));
       ("l4_dst_port",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F],16));
       ("wcmp_selector_input",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F],16));
       ("apply_tunnel_decap_at_end_of_pre_ingress",v_bool F);
       ("apply_tunnel_encap_at_egress",v_bool F);
       ("tunnel_encap_src_ipv6",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F],128));
       ("tunnel_encap_dst_ipv6",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F],128));
       ("marked_to_copy",v_bool F); ("marked_to_mirror",v_bool F);
       ("mirror_session_id",
        v_bit ([F; F; F; F; F; F; F; F; F; F],10));
       ("mirror_egress_port",
        v_bit ([F; F; F; F; F; F; F; F; F],9));
       ("mirror_encap_src_mac",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F],48));
       ("mirror_encap_dst_mac",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F],48));
       ("mirror_encap_vlan_id",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F],12));
       ("mirror_encap_src_ip",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F],128));
       ("mirror_encap_dst_ip",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F; F; F; F; F; F; F; F; F],128));
       ("mirror_encap_udp_src_port",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F],16));
       ("mirror_encap_udp_dst_port",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F; F;
            F; F; F],16));
       ("packet_in_ingress_port",
        v_bit ([F; F; F; F; F; F; F; F; F],9));
       ("packet_in_target_egress_port",
        v_bit ([F; F; F; F; F; F; F; F; F],9));
       ("color",v_bit ([F; F],2));
       ("ingress_port",
        v_bit ([F; F; F; F; F; F; F; F; F],9));
       ("route_metadata",v_bit ([F; F; F; F; F; F],6));
       ("acl_metadata",v_bit ([F; F; F; F; F; F; F; F],8));
       ("bypass_ingress",v_bool F); ("wcmp_group_id_valid",v_bool F);
       ("wcmp_group_id_value",
        v_bit
          ([F; F; F; F; F; F; F; F; F; F; F; F],12));
       ("nexthop_id_valid",v_bool F);
       ("nexthop_id_value",
        v_bit ([F; F; F; F; F; F; F; F; F; F],10));
       ("ipmc_table_hit",v_bool F); ("acl_drop",v_bool F)]),
 v1model_output_f,v1model_copyin_pbl,v1model_copyout_pbl,
 v1model_apply_table_f,
 [("header",NONE,
   [("isValid",[("this",d_in)],header_is_valid);
    ("setValid",[("this",d_inout)],header_set_valid);
    ("setInvalid",[("this",d_inout)],header_set_invalid)]);
  ("",NONE,
   [("mark_to_drop",[("standard_metadata",d_inout)],v1model_mark_to_drop);
    ("verify",[("condition",d_in); ("err",d_in)],v1model_verify);
    ("verify_checksum",
     [("condition",d_in); ("data",d_in); ("checksum",d_in); ("algo",d_none)],
     v1model_verify_checksum);
    ("update_checksum",
     [("condition",d_in); ("data",d_in); ("checksum",d_inout);
      ("algo",d_none)],v1model_update_checksum)]);
  ("packet_in",NONE,
   [("extract",[("this",d_in); ("headerLvalue",d_out)],
     v1model_packet_in_extract);
    ("lookahead",[("this",d_in); ("targ1",d_in)],v1model_packet_in_lookahead);
    ("advance",[("this",d_in); ("bits",d_in)],v1model_packet_in_advance)]);
  ("packet_out",NONE,
   [("emit",[("this",d_in); ("data",d_in)],v1model_packet_out_emit)]);
  ("direct_counter", (SOME ([("this", d_out); ("type", d_none)], v1model_direct_counter_construct),
   [("count",[("this",d_out)],v1model_direct_counter_count)]));
  ("direct_meter", (SOME ([("this", d_out); ("type", d_none); ("targ1", d_in)], v1model_direct_meter_construct), []));
  ("action_selector", (SOME ([("this", d_out); ("algorithm", d_none); ("size", d_none); ("outputWidth", d_none)], v1model_action_selector_construct), []))(* ;
  ("register",
   SOME
     ([("this",d_out); ("size",d_none); ("targ1",d_in)],register_construct),
   [("read",[("this",d_in); ("result",d_out); ("index",d_in)],register_read);
    ("write",[("this",d_in); ("index",d_in); ("value",d_in)],register_write)]);
  ("ipsec_crypt",SOME ([("this",d_out)],ipsec_crypt_construct),
   [("decrypt_aes_ctr",
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout);
      ("standard_metadata",d_inout); ("key",d_in); ("key_hmac",d_in)],
     ipsec_crypt_decrypt_aes_ctr);
    ("encrypt_aes_ctr",
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout); ("key",d_in);
      ("key_hmac",d_in)],ipsec_crypt_encrypt_aes_ctr);
    ("encrypt_null",[("this",d_in); ("ipv4",d_inout); ("esp",d_inout)],
     ipsec_crypt_encrypt_null);
    ("decrypt_null",
     [("this",d_in); ("ipv4",d_inout); ("esp",d_inout);
      ("standard_metadata",d_inout)],ipsec_crypt_decrypt_null)])
      *)],
 [("NoAction",
   stmt_seq
     (stmt_cond (e_var (varn_name "from_table"))
        (stmt_ass (lval_varname (varn_name "gen_apply_result"))
           (e_struct
              [("hit",e_var (varn_name "hit"));
               ("miss",e_unop unop_neg (e_var (varn_name "hit")));
               ("action_run",
                e_v
                  (v_bit
                     ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                       F; F; F; F; F; F; F; F; F; F; F; F; F; F],32)))]))
        stmt_empty) (stmt_seq stmt_empty (stmt_ret (e_v v_bot))),
   [("from_table",d_in); ("hit",d_in)]);
  ("no_action",
   stmt_seq
     (stmt_cond (e_var (varn_name "from_table"))
        (stmt_ass (lval_varname (varn_name "gen_apply_result"))
           (e_struct
              [("hit",e_var (varn_name "hit"));
               ("miss",e_unop unop_neg (e_var (varn_name "hit")));
               ("action_run",
                e_v
                  (v_bit
                     ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                       F; F; F; F; F; F; F; F; F; F; F; F; F; T],32)))]))
        stmt_empty) (stmt_seq stmt_empty (stmt_ret (e_v v_bot))),
   [("from_table",d_in); ("hit",d_in)]);
  ("set_nexthop_id",
   stmt_seq
     (stmt_cond (e_var (varn_name "from_table"))
        (stmt_ass (lval_varname (varn_name "gen_apply_result"))
           (e_struct
              [("hit",e_var (varn_name "hit"));
               ("miss",e_unop unop_neg (e_var (varn_name "hit")));
               ("action_run",
                e_v
                  (v_bit
                     ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                       F; F; F; F; F; F; F; F; F; F; F; F; T; F],32)))]))
        stmt_empty)
     (stmt_seq
        (stmt_seq
           (stmt_ass
              (lval_field (lval_varname (varn_name "local_metadata"))
                 "nexthop_id_valid") (e_v (v_bool T)))
           (stmt_ass
              (lval_field (lval_varname (varn_name "local_metadata"))
                 "nexthop_id_value") (e_var (varn_name "nexthop_id"))))
        (stmt_ret (e_v v_bot))),
   [("from_table",d_in); ("hit",d_in); ("local_metadata",d_inout);
    ("nexthop_id",d_none)]);
  ("acl_drop",
   stmt_seq
     (stmt_cond (e_var (varn_name "from_table"))
        (stmt_ass (lval_varname (varn_name "gen_apply_result"))
           (e_struct
              [("hit",e_var (varn_name "hit"));
               ("miss",e_unop unop_neg (e_var (varn_name "hit")));
               ("action_run",
                e_v
                  (v_bit
                     ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                       F; F; F; F; F; F; F; F; F; F; F; F; T; T],32)))]))
        stmt_empty)
     (stmt_seq
        (stmt_ass
           (lval_field (lval_varname (varn_name "local_metadata")) "acl_drop")
           (e_v (v_bool T))) (stmt_ret (e_v v_bot))),
   [("from_table",d_in); ("hit",d_in); ("local_metadata",d_inout)])]):v1model_ascope actx”;

(*
[mk_ternary; mk_optional]

MAC destination and ingress port:
(w48, w9)
S1ETH1_MAC="02:11:22:33:44:03" and port 1

maybe also

S1ETH2_MAC="02:11:22:33:44:04" and port 2
        
 hex_to_bool_list "021122334403"
 EVAL “fixwidth 9 $ n2v 1”

 hex_to_bool_list "021122334404"
*)
val l3_admit_tbl =
 “("l3_admit.l3_admit_table",
   tbl_regular
   [(([s_sing $ v_bit
         ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F; T; F; F; F; T; F;
           F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F; F; F; F; F; F; F; T; T],48);
       s_sing $ v_bit ([F; F; F; F; F; F; F; F; T],9)],4),
     "l3_admit.admit_to_l3",
     [e_v (v_bool T); e_v (v_bool T)]);
    (([s_sing $ v_bit
         ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F; T; F; F; F; T; F;
           F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F; F; F; F; F; F; T; F; F],48);
       s_sing $ v_bit ([F; F; F; F; F; F; F; T; F],9)],4),
     "l3_admit.admit_to_l3",
     [e_v (v_bool T); e_v (v_bool T)]);
   ]):(string # tbl)”;
   
(* TODO: Is it OK to define "nexthop" to just correspond to ports?

[mk_exact; mk_lpm]

VRF ID and IPv4 destination address 
(w10, w32)

0 and 10.0.0.2

 VRF ID is just kDefaultVrf, which is 0.
   
 EVAL “fixwidth 10 $ n2v 0”
 hex_to_bool_list "0a.00.00.02"

 EVAL “fixwidth 10 $ n2v 0”
 hex_to_bool_list "0a.00.00.01"

 EVAL “fixwidth 10 $ n2v 2”


 bool_list_to_hex “[F; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F;
                    F; F; F; F; F; F; F; F; F; F; F; T; F]”

*)
val ipv4_tbl =
 “("routing_lookup.ipv4_table",
   tbl_regular
   [(([s_sing $ v_bit
         ([F; F; F; F; F; F; F; F; F; F],10);
       s_sing $ v_bit ([F; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
           F; F; F; F; F; F; T; F],32)],4),
     "set_nexthop_id",
     [e_v (v_bool T); e_v (v_bool T); (e_var (varn_name "routing_lookup_local_metadata"));
      e_v $ v_bit ([F; F; F; F; F; F; F; F; T; F],10)]);
    (([s_sing $ v_bit
         ([F; F; F; F; F; F; F; F; F; F],10);
       s_sing $ v_bit ([F; F; F; F; T; F; T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
F; F; F; F; F; F; F; T],32)],4),
     "set_nexthop_id",
     [e_v (v_bool T); e_v (v_bool T); (e_var (varn_name "routing_lookup_local_metadata"));
      e_v $ v_bit ([F; F; F; F; F; F; F; F; F; T],10)])
   ]):(string # tbl)”;


(*

[mk_exact]

Nexthop ID
w10

 EVAL “fixwidth 10 $ n2v 2”

 EVAL “fixwidth 10 $ n2v 1”

Router interface ID, Neighbour ID which is always an IPv6 address...

*)
val nexthop_tbl =
 “("routing_resolution.nexthop_table",
   tbl_regular
   [(([s_sing $ v_bit
         ([F; F; F; F; F; F; F; F; T; F],10)],4),
       "routing_resolution.set_ip_nexthop",
       [e_v (v_bool T); e_v (v_bool T);
        e_v $ v_bit ([F; F; F; F; F; F; F; F; T; F],10);
        e_v $ v_bit ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                      F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                      F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                      F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                      F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                      F; F; F; F; F; F; T; F],128)]);
    (([s_sing $ v_bit
         ([F; F; F; F; F; F; F; F; F; T],10)],4),
      "routing_resolution.set_ip_nexthop",
      [e_v (v_bool T); e_v (v_bool T);
       e_v $ v_bit ([F; F; F; F; F; F; F; F; F; T],10);
       e_v $ v_bit ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                     F; F; F; F; F; F; F; T],128)])
   ]):(string # tbl)”;

(*

[mk_exact]

Router interface ID
w10

Port ID (9 bits) and MAC address (48 bits)

S1ETH2_MAC
 hex_to_bool_list "021122334404"
     
S1ETH1_MAC
 hex_to_bool_list "021122334403"

*)
val router_interface_tbl =
 “("routing_resolution.router_interface_table",
   tbl_regular
   [(([s_sing $ v_bit
         ([F; F; F; F; F; F; F; F; T; F],10)],4),
     "routing_resolution.set_port_and_src_mac",
     [e_v (v_bool T); e_v (v_bool T);
      e_v $ v_bit ([F; F; F; F; F; F; F; T; F],9);
      e_v $ v_bit ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F; T; F; F; F; T; F;
                    F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F; F; F; F; F; F; T; F; F],48)]);
    (([s_sing $ v_bit
         ([F; F; F; F; F; F; F; F; F; T],10)],4),
     "routing_resolution.set_port_and_src_mac",
     [e_v (v_bool T); e_v (v_bool T);
      e_v $ v_bit ([F; F; F; F; F; F; F; F; T],9);
      e_v $ v_bit ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F; T; F; F; F; T; F;
                    F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F; F; F; F; F; F; F; T; T],48)])
   ]):(string # tbl)”;

(*

[mk_exact; mk_exact]

Router interface ID and neighbor ID (IPv6 address)
(w10, w128)

VETH2_MAC
 hex_to_bool_list "021122334402"
     
VETH1_MAC
 hex_to_bool_list "021122334401"

*)
val neighbor_tbl =
 “("routing_resolution.neighbor_table",
   tbl_regular
   [(([s_sing $ v_bit
         ([F; F; F; F; F; F; F; F; T; F],10);
       s_sing $ v_bit
         ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
           F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
           F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
           F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
           F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
           F; F; F; F; F; F; T; F],128)],4),
     "routing_resolution.set_dst_mac",
     [e_v (v_bool T); e_v (v_bool T);
      e_v $ v_bit ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F; T; F; F; F; T; F;
                    F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F; F; F; F; F; F; F; T; F],48)]);
    (([s_sing $ v_bit
         ([F; F; F; F; F; F; F; F; F; T],10);
       s_sing $ v_bit
         ([F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
           F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
           F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
           F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
           F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
           F; F; F; F; F; F; F; T],128)],4),
     "routing_resolution.set_dst_mac",
     [e_v (v_bool T); e_v (v_bool T);
      e_v $ v_bit ([F; F; F; F; F; F; T; F; F; F; F; T; F; F; F; T; F; F; T; F; F; F; T; F;
                    F; F; T; T; F; F; T; T; F; T; F; F; F; T; F; F; F; F; F; F; F; F; F; T],48)])
   ]):(string # tbl)”;

(* TODO: Apart from the table and extern configurations, this seems close to a generic P4 initial state *)
val google_fbr_astate = “((0,[],[],0,[],[("parseError",v_bit (fixwidth 32 (n2v 0),32))],
  [("ingress_cloning.ingress_clone_table",tbl_regular []);
   ("mirror_session_lookup.mirror_session_table",tbl_regular []);
   ^neighbor_tbl;
   ^router_interface_tbl;
   ^nexthop_tbl;
   ("routing_resolution.tunnel_table",tbl_regular []);
   ("routing_resolution.wcmp_group_table",tbl_regular []);
   ("acl_ingress.acl_ingress_table",tbl_regular []);
   ("acl_ingress.acl_ingress_qos_table",tbl_regular []);
   ("acl_ingress.acl_ingress_counting_table",tbl_regular []);
   ("acl_ingress.acl_ingress_mirror_and_redirect_table",tbl_regular []);
   ("acl_ingress.acl_ingress_security_table",tbl_regular []);
   ("routing_lookup.vrf_table",tbl_regular []);
   ^ipv4_tbl;
   ("routing_lookup.ipv6_table",tbl_regular []);
   ("routing_lookup.ipv4_multicast_table",tbl_regular []);
   ("routing_lookup.ipv6_multicast_table",tbl_regular []);
   ^l3_admit_tbl;
   ("tunnel_termination.ipv6_tunnel_termination_table",tbl_regular []);
   ("acl_pre_ingress.acl_pre_ingress_table",tbl_regular []);
   ("acl_pre_ingress.acl_pre_ingress_vlan_table",tbl_regular []);
   ("acl_pre_ingress.acl_pre_ingress_metadata_table",tbl_regular []);
   ("vlan_untag.disable_vlan_checks_table",tbl_regular []);
   ("acl_egress.acl_egress_table",tbl_regular []);
   ("acl_egress.acl_egress_dhcp_to_host_table",tbl_regular []);
   ("packet_rewrites.multicast_rewrites.multicast_router_interface_table",tbl_regular [])]),
 [[(varn_name "gen_apply_result",
    v_struct
      [("hit",v_bool F); ("miss",v_bool F);
       ("action_run",v_bit (REPLICATE 32 F,32))],NONE)]],
 arch_frame_list_empty,status_running):v1model_ascope astate”;

(******************)
(* Example input: *)
(*

(*******************
IPV4 EXECUTION PATH:
Arch input port should not be SAI_P4_CPU_PORT (510),

ethernet.ether_type should be ETHERTYPE_IPV4 (0x0800)
headers.ipv4.protocol should be IP_PROTOCOL_UDP (0x11)

Direct meters are read in:
acl_copy
(acl_trap, indirectly)
acl_forward
acl_ingress.set_qos_queue_and_cancel_copy_above_rate_limit
acl_ingress.set_cpu_and_multicast_queues_and_deny_above_rate_limit
acl_ingress.set_cpu_queue_and_deny_above_rate_limit

But these are only triggered in the acl_ingress_table and acl_ingress_qos_table tables,
which are unpopulated, only resulting in NoAction.

Still, direct meters need to be instantiated.

        
*)

val port = “1:num”
val components = ["ethernet", "ipv4", "udp"]
val fixed_fields = [("ethernet.dst_addr", 2272611484675),
                    ("ethernet.ether_type", 2048),
                    ("ipv4.protocol", 17),
                    ("ipv4.dst_addr", 167772162)]
val input_bits_tm = p4_cake_auxLib.v1model_get_input google_fbr_actx fixed_fields components
(* Test: EVAL “LENGTH ^input_bits_tm” *)
val input_tm = mk_pair (input_bits_tm, port)

(* Test: *)
(* 239: application of "vlan_untag.disable_vlan_checks_table" *)
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 239”

(* 280: Instantiating the direct_counter "acl_pre_ingress_acl_pre_ingress_counter" *)
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 280”

(* 600: Instantiating "acl_ingress_acl_ingress_meter" *)
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 599”

(* 700: Applying "acl_ingress.acl_ingress_table" *)
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 700”

rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 825”

(* 833: Instantiating action selector, start of routing_resolution *)   
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 833”

(* 551: Just before applying ipv4_table *)
#3 $ dest_astate $ dest_some $ rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 551”

rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 552”

rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 1289”

(* TODO: Why is the packet not output in the final stage? *)
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 1459”



rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 1453”


(*******************
IPV6 EXECUTION PATH:
Arch input port should be SAI_P4_CPU_PORT (510),

ethernet.ether_type should be ETHERTYPE_IPV6 (0x86dd or 34525)
ipv6.next_header should be IP_PROTOCOL_IPV6 (0x29 or 41)
inner_ipv6.next_header should be IP_PROTOCOL_TCP (0x06 or 6)
*)

val port = “510:num”
(* The header components to include in the input packet *)
val components = ["packet_out_header", "ethernet", "ipv6", "inner_ipv6", "tcp"]
(* Fields that have fixed values (other fields are random) *)
val fixed_fields = [("ethernet.ether_type", 34525), ("ipv6.next_header", 41), ("inner_ipv6.next_header", 6)]
val input_bits_tm = p4_cake_auxLib.v1model_get_input google_fbr_actx fixed_fields components
val input_tm = mk_pair (input_bits_tm, port)

(* Packet accepted at step 140: *)
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 139”
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 140”
(* verify_ipv4_checksum block starts at step 143: (~2.5s to EVAL up until this point) *)
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx'' (p4_append_input_list [^input_tm] ^google_fbr_astate) 143”
(* verify_ipv4_checksum finishes at 199 steps *)
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx'' (p4_append_input_list [^input_tm] ^google_fbr_astate) 199”

rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx'' (p4_append_input_list [^input_tm] ^google_fbr_astate) 300”
(* After 436, execution encounters instantiation of the direct_counter "acl_egress_acl_egress_counter", which must
 * be properly modeled before continuing *)
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx'' (p4_append_input_list [^input_tm] ^google_fbr_astate) 436”
(* 735 steps should output the outgoing packet *)
rhs $ concl $ EVAL “arch_multi_exec ^google_fbr_actx (p4_append_input_list [^input_tm] ^google_fbr_astate) 735”


(* For copy-pasting to command-line:

val string_input = String.implode $ deparse_bool_list $ fst $ listSyntax.dest_list input_tm

*)
*)

(** Transformation **)

(* ~3min *)
val (dict', actx', astate') =
 transform_program cake_dict_tm "v1model" google_fbr_actx google_fbr_astate;

(* Test of IPv4 path:
        
rhs $ concl $ EVAL “arch_multi_exec' ^actx' (THE $ p4_append_input_list' [^input_tm] ^astate') 1650”

val res = rhs $ concl $ EVAL “FLAT $ MAP w2v [2w; 17w; 34w; 51w; 68w; 2w; 2w; 17w; 34w; 51w; 68w; 4w; 8w; 0w;
           115w; 56w; 193w; 72w; 9w; 86w; 65w; 54w; 16w; 17w; 117w; 245w;
           138w; 93w; 102w; 140w; 10w; 0w; 0w; 2w; 19w; 178w; 240w; 250w;
           97w; 211w; 187w; 190w:word8]”;

bool_list_to_hex res
*)

val dict'' = invert_dict dict';

val progname = Theory.current_theory();
val dict = dict'';
val actx = actx';
val astate = astate';
(* Around 2000 steps should suffice *)
val n_max = “2000:num”;
val debug_mode = false;
val inlogic = false;

val _ = p4_cake_wrapper_ffiLib.translate_p4 progname dict actx astate n_max debug_mode inlogic;

val _ = export_theory ();

structure p4_exec_wrapper_ffiLib :> p4_exec_wrapper_ffiLib = struct

(* Core HOL4 *)
open HolKernel boolLib Parse bossLib;

(* HOL4P4 *)
open p4Theory p4_auxTheory p4_exec_semTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_progLib basisFunctionsLib
     eval_cake_compile_x64Lib;
open fromSexpTheory;

val _ = intLib.deprecate_int();

(* Note that this function only adds inlined CakeML code - it translates no HOL4
 * definitions. *)
(* TODO: Add common debug functions to a new ProgScript file *)
fun append_prog_p4_wrapper debug_mode () =
 let
   val _ = append_prog o process_topdecs $ 
    ‘exception InputError string;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Convert 16-bit integer to two bytes in big-endian order *)
    fun int_to_byte2 i bytes offset =
      (* Note: This assumes 16-bit integers *)
      let
	val b0 = Word8.fromInt (i div 256);
	val b1 = Word8.fromInt (i mod 256);
      in
	Word8Array.update bytes offset b0;
	Word8Array.update bytes (offset + 1) b1
      end;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Convert two bytes in big-endian order to 16-bit integer *)
    fun byte2_to_int bytes offset =
      let
	val b0 = Word8.toInt (Word8Array.sub bytes offset);
	val b1 = Word8.toInt (Word8Array.sub bytes (offset + 1));
      in
	b0 * 256 + b1
      end;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Convert 32-bit integer to eight bytes in big-endian order (for socket descriptors) *)
    fun int_to_byte8 i bytes offset =
      (* Note: This assumes 32-bit integers *)
      let
	val _ = int_to_byte2 0 bytes offset;
	val _ = int_to_byte2 0 bytes (offset + 2);
	val _ = int_to_byte2 (i div 65536) bytes (offset + 4);
	val _ = int_to_byte2 (i mod 65536) bytes (offset + 6)
      in
	()
      end;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Convert eight bytes in big-endian order to integer *)
    fun byte8_to_int bytes offset =
      (* Note: This is a simplification and assumes 32-bit integers *)
      let
	val high = byte2_to_int bytes (offset + 4);
	val low = byte2_to_int bytes (offset + 6);
      in
	high * 65536 + low
      end;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Utility function for converting from array to string *)
    fun array_to_string arr =
      let
	val len = Word8Array.length arr;
	fun loop i acc =
	  if i < 0 then acc
	  else loop (i-1) (String.str(Char.chr(Word8.toInt(Word8Array.sub arr i))) ^ acc)
      in
	loop (len - 1) ""
      end;’;
(*
   val _ = append_prog o process_topdecs $
    ‘fun array_to_hex_string arr =
      let
	val len = Word8Array.length arr;

	(* Convert a Word8 to its hex representation *)
	fun word8_to_hex w =
	  let
	    val i = Word8.toInt w;
	    val hex_chars = "0123456789ABCDEF";
	    val hi = String.sub hex_chars (i div 16);
	    val lo = String.sub hex_chars (i mod 16);
	  in
	    String.str hi ^ String.str lo
	  end;

	(* Build the string with spaces between hex values *)
	fun loop i acc =
	  if i < 0 then acc
	  else 
	    let
	      val hex = word8_to_hex (Word8Array.sub arr i);
	      val new_acc = 
		if i = len - 1 then hex ^ acc
		else hex ^ " " ^ acc
	    in
	      loop (i-1) new_acc
	    end
      in
	loop (len - 1) ""
      end;

    (* Convert integer to eight bytes (for socket descriptors) - returns a string *)
    fun int_to_byte8_string i =
      let
	val buffer = Word8Array.array 8 (Word8.fromInt 0);
	val _ = int_to_byte8 i buffer 0;
      in
	array_to_string buffer
      end;’
   ;
*)

   val _ = append_prog o process_topdecs $
   ‘(* String to Word8Array utility function *)
    fun string_to_buffer str =
      let
	val len = String.size str;
	val buffer = Word8Array.array len (Word8.fromInt 0);
	fun fill_buffer i =
	  if i >= len then ()
	  else (
	    Word8Array.update buffer i (Word8.fromInt (Char.ord (String.sub str i)));
	    fill_buffer (i + 1)
	  )
      in
	fill_buffer 0;
	buffer
      end;

   (* Word8Array to String utility function *)
    fun buffer_to_string buffer = array_to_string buffer;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Set socket buffer size (receive or send) *)
    fun set_socket_buffer_size sock_fd buffer_size is_send =
      let
        (* Create buffer with socket descriptor, buffer size, and buffer type *)
        val req_buffer = Word8Array.array 17 (Word8.fromInt 0);
        val _ = int_to_byte8 sock_fd req_buffer 0;
        val _ = int_to_byte8 buffer_size req_buffer 8;
        (* Set buffer type: 0 = receive buffer, 1 = send buffer *)
        val _ = Word8Array.update req_buffer 16 (Word8.fromInt (if is_send then 1 else 0));
        
        (* Result buffer with status and actual buffer size *)
        val result_buffer = Word8Array.array 9 (Word8.fromInt 0);
      in
        #(set_socket_buffer_size) (buffer_to_string req_buffer) result_buffer;
        if Word8.toInt (Word8Array.sub result_buffer 0) = 0 then
          Some (byte8_to_int result_buffer 1)
        else
          None
      end;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Close a raw socket *)
    fun close sock_fd =
      let
        (* Create buffer with socket descriptor *)
        val fd_buffer = Word8Array.array 8 (Word8.fromInt 0);
        val _ = int_to_byte8 sock_fd fd_buffer 0;
        
        (* Status buffer *)
        val result_buffer = Word8Array.array 1 (Word8.fromInt 0);
      in
        #(raw_socket_close) (buffer_to_string fd_buffer) result_buffer;
        Word8.toInt (Word8Array.sub result_buffer 0) = 0
      end;’
   ;

   (* Add raw socket interface functions *)
   val _ = append_prog o process_topdecs $
    ‘(* Create a raw socket, optionally with buffer sizes for sending and receiving *)
    fun raw_socket_create rcvbuf_size sndbuf_size =
      let
        val result_buffer = Word8Array.array 9 (Word8.fromInt 0);
      in
        #(raw_socket_create) "" result_buffer;
        if Word8.toInt (Word8Array.sub result_buffer 0) = 0 then
          let
            val sock_fd = byte8_to_int result_buffer 1;
            
            (* Set receive buffer size if provided *)
            val rcv_result = 
              case rcvbuf_size of
                None => Some 0
              | Some size => set_socket_buffer_size sock_fd size False;
            
            (* Set send buffer size if provided *)
            val snd_result = 
              case sndbuf_size of
                None => Some 0
              | Some size => set_socket_buffer_size sock_fd size True;
          in
            case (rcv_result, snd_result) of
              (Some _, Some _) => Some sock_fd
            | _ => 
                (* Failed to set buffer sizes, close socket and return NONE *)
                let
                  val _ = close sock_fd
                in
                  None
                end
          end
        else
          None
      end;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Get interface index *)
    fun get_interface_index sock_fd interface_name =
      let
	val fd_buffer = Word8Array.array 8 (Word8.fromInt 0);
	val _ = int_to_byte8 sock_fd fd_buffer 0;
	
	(* Combine socket descriptor with interface name *)
	val req_buffer = Word8Array.array (8 + String.size interface_name + 1) (Word8.fromInt 0);
	val _ = Word8Array.copy fd_buffer 0 8 req_buffer 0;
	
	(* Add interface name after the socket descriptor *)
	val name_buffer = string_to_buffer interface_name;
	val _ = Word8Array.copy name_buffer 0 (Word8Array.length name_buffer) req_buffer 8;
	
	(* Add null terminator *)
	val _ = Word8Array.update req_buffer (8 + String.size interface_name) (Word8.fromInt 0);
	
	(* Result buffer for the interface index *)
	val result_buffer = Word8Array.array 9 (Word8.fromInt 0);
      in
	#(get_interface_index) (buffer_to_string req_buffer) result_buffer;
	if Word8.toInt (Word8Array.sub result_buffer 0) = 0 then
	  Some (byte8_to_int result_buffer 1)
	else
	  None
      end;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Get interface MTU *)
    fun get_interface_mtu sock_fd interface_name =
      let
	val fd_buffer = Word8Array.array 8 (Word8.fromInt 0);
	val _ = int_to_byte8 sock_fd fd_buffer 0;
	
	(* Combine socket descriptor with interface name *)
	val req_buffer = Word8Array.array (8 + String.size interface_name + 1) (Word8.fromInt 0);
	val _ = Word8Array.copy fd_buffer 0 8 req_buffer 0;
	
	(* Add interface name after the socket descriptor *)
	val name_buffer = string_to_buffer interface_name;
	val _ = Word8Array.copy name_buffer 0 (Word8Array.length name_buffer) req_buffer 8;
	
	(* Add null terminator *)
	val _ = Word8Array.update req_buffer (8 + String.size interface_name) (Word8.fromInt 0);
	
	(* Result buffer for the MTU *)
	val result_buffer = Word8Array.array 9 (Word8.fromInt 0);
      in
	#(get_interface_mtu) (buffer_to_string req_buffer) result_buffer;
	if Word8.toInt (Word8Array.sub result_buffer 0) = 0 then
	  Some (byte8_to_int result_buffer 1)
	else
	  None
      end;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Bind raw socket to interface *)
    fun raw_socket_bind sock_fd if_index =
      let
	(* Create buffer with socket descriptor and interface index *)
	val req_buffer = Word8Array.array 16 (Word8.fromInt 0);
	val _ = int_to_byte8 sock_fd req_buffer 0;
	val _ = int_to_byte8 if_index req_buffer 8;
	
	(* Status buffer *)
	val result_buffer = Word8Array.array 1 (Word8.fromInt 0);
      in
	#(raw_socket_bind) (buffer_to_string req_buffer) result_buffer;
	Word8.toInt (Word8Array.sub result_buffer 0) = 0
      end;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Receive packet from raw socket *)
    fun raw_socket_recv sock_fd max_bytes =
      let  
	val fd_buffer = Word8Array.array 8 (Word8.fromInt 0);
	val _ = int_to_byte8 sock_fd fd_buffer 0;

	(* Result buffer with space for status, bytes read, and data *)
	val result_buffer = Word8Array.array (max_bytes + 4) (Word8.fromInt 0);
        (* Note: this assumes max_bytes is at most 65535. *)
	val _ = int_to_byte2 max_bytes result_buffer 0;

	val _ = #(raw_socket_recv) (buffer_to_string fd_buffer) result_buffer;
      in
	if Word8.toInt (Word8Array.sub result_buffer 0) = 0 then
	  let
	    val bytes_read = byte2_to_int result_buffer 1;

	    val packet_data = Word8Array.array bytes_read (Word8.fromInt 0);

	    (* Copy received data to a new array *)
	    val _ = Word8Array.copy result_buffer 4 bytes_read packet_data 0;
	  in
	    Some packet_data
	  end
	else
	   None
      end;’;

   val _ = append_prog o process_topdecs $
    ‘(* Send packet to raw socket *)
    fun raw_socket_send sock_fd data =
      let
	val fd_buffer = Word8Array.array 8 (Word8.fromInt 0);
	val _ = int_to_byte8 sock_fd fd_buffer 0;
	
	val data_len = Word8Array.length data;
	val result_buffer = Word8Array.array (data_len + 4) (Word8.fromInt 0);
	val _ = int_to_byte2 data_len result_buffer 0;
	val _ = int_to_byte2 0 result_buffer 2;  (* offset = 0 *)
	val _ = Word8Array.copy data 0 data_len result_buffer 4;
      in
	#(raw_socket_send) (buffer_to_string fd_buffer) result_buffer;
	if Word8.toInt (Word8Array.sub result_buffer 0) = 0 then
	  Some (byte2_to_int result_buffer 1)
	else
	  None
      end;’
   ;

   val _ = append_prog o process_topdecs $
    ‘(* Send packet to specific interface *)
    fun raw_socket_sendto sock_fd if_index data =
      let
	(* Create buffer with socket descriptor and interface index *)
	val req_buffer = Word8Array.array 16 (Word8.fromInt 0);
	val _ = int_to_byte8 sock_fd req_buffer 0;
	val _ = int_to_byte8 if_index req_buffer 8;
	
	val data_len = Word8Array.length data;
	val result_buffer = Word8Array.array (data_len + 4) (Word8.fromInt 0);
	val _ = int_to_byte2 data_len result_buffer 0;
	val _ = int_to_byte2 0 result_buffer 2;  (* offset = 0 *)
	val _ = Word8Array.copy data 0 data_len result_buffer 4;
      in
	#(raw_socket_sendto) (buffer_to_string req_buffer) result_buffer;
	if Word8.toInt (Word8Array.sub result_buffer 0) = 0 then
	  Some (byte2_to_int result_buffer 1)
	else
	  None
      end;’
   ;

val _ = append_prog o process_topdecs $
 ‘(* Poll multiple file descriptors *)
  fun raw_socket_poll fds timeout =
    let
      (* Create buffer for poll arguments *)
      val nfds = List.length fds;
      val poll_buffer = Word8Array.array (nfds * 10) (Word8.fromInt 0);
      
      (* Fill in the file descriptors and events *)
      fun fill_poll_buffer fds idx =
        case fds of
          [] => ()
        | (fd, events)::rest =>
            let
              val offset = idx * 10;
              val _ = int_to_byte8 fd poll_buffer offset;
              val _ = Word8Array.update poll_buffer (offset + 8) (Word8.fromInt (events div 256));
              val _ = Word8Array.update poll_buffer (offset + 9) (Word8.fromInt (events mod 256));
            in
              fill_poll_buffer rest (idx + 1)
            end;
      
      val _ = fill_poll_buffer fds 0;
      
      (* Result buffer with space for status, number of ready fds, and revents array *)
      val result_buffer = Word8Array.array (8 + (nfds * 2)) (Word8.fromInt 0);
      
      (* Set number of fds and timeout *)
      (* Note: This encodes nfds as a 32-bit number *)
      val _ = Word8Array.update result_buffer 0 (Word8.fromInt ((nfds div 16777216) mod 256));
      val _ = Word8Array.update result_buffer 1 (Word8.fromInt ((nfds div 65536) mod 256));
      val _ = Word8Array.update result_buffer 2 (Word8.fromInt ((nfds div 256) mod 256));
      val _ = Word8Array.update result_buffer 3 (Word8.fromInt (nfds mod 256));

      (* Note: This encodes timeout as a 32-bit number *)      
      val _ = Word8Array.update result_buffer 4 (Word8.fromInt ((timeout div 16777216) mod 256));
      val _ = Word8Array.update result_buffer 5 (Word8.fromInt ((timeout div 65536) mod 256));
      val _ = Word8Array.update result_buffer 6 (Word8.fromInt ((timeout div 256) mod 256));
      val _ = Word8Array.update result_buffer 7 (Word8.fromInt (timeout mod 256));
    in
      #(raw_socket_poll) (buffer_to_string poll_buffer) result_buffer;
      case Word8.toInt (Word8Array.sub result_buffer 0) of
        0 => 
          let
            (* Extract number of ready fds *)
            (* Note: This extracts a 32-bit number *)
            val ready_count = 
              (Word8.toInt (Word8Array.sub result_buffer 1) * 16777216) +
              (Word8.toInt (Word8Array.sub result_buffer 2) * 65536) +
              (Word8.toInt (Word8Array.sub result_buffer 3) * 256) +
              Word8.toInt (Word8Array.sub result_buffer 4);
            
            (* Extract revents for each fd *)
            fun extract_revents idx acc =
              if idx >= nfds then
                List.rev acc
              else
                let
                  val revents = 
                    (Word8.toInt (Word8Array.sub result_buffer (8 + (idx * 2))) * 256) +
                    Word8.toInt (Word8Array.sub result_buffer (8 + (idx * 2) + 1));
                in
                  extract_revents (idx + 1) (revents::acc)
                end;
            
            val revents_list = extract_revents 0 [];
          in
            Some (ready_count, revents_list)
          end
      | 2 => None  (* Timeout *)
      | _ => None  (* Error *)
    end;’
;

   (* Helper functions for packet processing *)
   val _ = append_prog o process_topdecs $
    ‘(* Convert a raw packet buffer to a list of booleans *)
    fun packet_to_bool_list packet =
      let
	val len = Word8Array.length packet;
	fun process_byte byte acc =
	  let
            (* Note: this assumes big-endian order *)
            (* TODO: Unroll this? *)
	    fun process_bit i acc =
	      if i < 0 then acc
	      else
		let
		  val bit_mask = Word8.<< (Word8.fromInt 1) i;
		  val bit = Word8.andb byte bit_mask <> Word8.fromInt 0
		in
		  process_bit (i-1) (bit::acc)
		end
	  in
	    process_bit 7 acc
	  end
	  
	fun process_packet i acc =
	  if i >= len then List.rev acc
	  else process_packet (i+1) (process_byte (Word8Array.sub packet i) acc)
      in
	process_packet 0 []
      end;’
   ;
(*
   (* foldr for Word8Arrays: *)
   val _ = append_prog o process_topdecs $
    ‘fun w8a_foldr_aux f init arr n =
      if n = 0
       then init
      else w8a_foldr_aux f (f (Word8Array.sub arr (n - 1)) init) arr (n - 1)

     fun w8a_foldr f init (arr:byte_array) =
      w8a_foldr_aux f init arr (Word8Array.length arr)’;

   val _ = append_prog o process_topdecs $
    ‘fun array_to_list (arr:byte_array) = w8a_foldr (fn h => (fn res => (h::res))) ([]: (Word8.word list)) arr’;
*)
   (* fromList for Word8Arrays *)
(*
   val _ = append_prog o process_topdecs $
    ‘fun from_w8list (l:Word8.word list) =
     let fun f arr l i =
	case l of
	   [] => arr
	 | (h::t) => (Word8Array.update arr i h; f arr t (i + 1))
     in
       case l of
	 [] => Word8Array.array 0 (Word8.fromInt 0)
       | h::t => f (Word8Array.array (List.length l) h) t 1
     end’;
*)
   val _ = append_prog o process_topdecs $
    ‘(* Convert a list of booleans to a packet buffer *)
    fun bool_list_to_packet bool_list =
      let
	(* Calculate number of bytes needed (round up to nearest byte) *)
	val num_bits = List.length bool_list;
	val num_bytes = (num_bits + 7) div 8;
	
	(* Create buffer for the packet *)
	val packet = Word8Array.array num_bytes (Word8.fromInt 0);
	
	(* Set each bit in the buffer *)
        (* TODO: Unroll this? *)
	fun set_bit byte_idx bit_idx value =
	  let
	    val byte = Word8Array.sub packet byte_idx;
	    val mask = Word8.<< (Word8.fromInt 1) bit_idx;
	    val new_byte = if value then Word8.orb byte mask else byte
	  in
	    Word8Array.update packet byte_idx new_byte
	  end
	  
	fun process_bits bits idx =
	  case bits of
	    [] => ()
	  | b::bs =>
	      let
		val byte_idx = idx div 8;
		val bit_idx = 7 - (idx mod 8);  (* MSB first *)
	      in
		set_bit byte_idx bit_idx b;
		process_bits bs (idx + 1)
	      end
      in
	process_bits bool_list 0;
	packet
      end;’
   ;

   (* Parse port@interface argument *)
   val _ = append_prog o process_topdecs $ 
    ‘fun parse_port_interface arg =
      let
        val parts = String.tokens (fn c => c = #"@") arg;
      in
        if List.length parts = 2 then
          let
            val port_str = List.nth parts 0;
            val if_name = List.nth parts 1;
            val port_opt = Int.fromString port_str;
          in
            case port_opt of
              Some port => Some (port, if_name)
            | None => None
          end
        else None
      end;’
   ;

   val res = append_prog o process_topdecs $ 
    ‘(* Get the nth argument, returning a default if not available *)
    fun get_arg n default =
      let
	val args = CommandLine.arguments ()
      in
	if n < List.length args then
	  List.nth args n
	else
	  default
      end’;

   val _ = append_prog o process_topdecs $
       ‘(* Map between port numbers, interface indices, and socket descriptors *)
       type port_map = (int * (int * int)) list;  (* (port_number, if_index, sock_fd) triplets *)’;

   val _ = append_prog o process_topdecs $
    ‘fun main () =
     let
       (* Extract arguments - 9000 is default buffer size *)
       (* TODO: Best default buffer size? *)
       val buffer_size = 
	 case Int.fromString (get_arg 0 "9000") of
	   Some size =>
           if size >= 65535
           then raise InputError "Buffer size exceeding 65535 bytes: lower or generalise the source code (raw_socket_recv, raw_socket_send, raw_socket_sendto)"
           else size
          (* Unparseable arguments currently yield 9000 instead of InputError *)
	 | None => 9000;

       (* Process interface arguments *)
       val args = CommandLine.arguments ();

       (* Find all -i arguments and extract port@interface pairs *)
       fun find_interfaces args idx acc =
	 if idx >= List.length args then acc
	 else
	   let
	     val arg = List.nth args idx;
	   in
	     if arg = "-i" andalso idx + 1 < List.length args then
	       let
		 val port_if = parse_port_interface (List.nth args (idx + 1));
	       in
		 case port_if of
		   Some pair => find_interfaces args (idx + 2) (pair::acc)
		 | None => find_interfaces args (idx + 2) acc
	       end
	     else
	       find_interfaces args (idx + 1) acc
	   end

       val interfaces = find_interfaces args 0 [];

       (* Print startup message *)
       val _ = print "HOL4P4 Software Switch starting...\n";
       val _ = print ("Buffer size: " ^ Int.toString buffer_size ^ " bytes\n");
       val _ = print ("Number of interfaces: " ^ Int.toString (List.length interfaces) ^ "\n");

       val _ = print "Creating raw sockets...\n";

       val port_map = Ref ([]: port_map);

       fun find_if_index_and_sock port port_map_local =
	 case port_map_local of
	   [] => (None, None)
	 | (p, idx, sock)::rest =>
          if p = port then (Some idx, Some sock) else find_if_index_and_sock port rest
(*
	  let
	    val _ = print ("Searching for index and sock, current: " ^ Int.toString idx ^ " socket " ^ Int.toString sock ^ ")\n");
	  in
	    if p = port then (Some idx, Some sock) else find_if_index_and_sock port rest
	  end *);

       (* For each interface *)
       val _ = List.foldl (fn (port, if_name) => (fn idx =>
	 let
           (* Note: Send and receive buffers are set to 8 MB and 4 MB, respectively *)
	   val sock_fd_opt = raw_socket_create (Some 8388608) (Some 4194304);
	   val _ = print ("Creating socket for interface " ^ if_name ^ " (port " ^ Int.toString port ^ ")\n")
	 in
	   case sock_fd_opt of
	     None => 
	       let
		 val _ = print ("Failed to create socket for interface " ^ if_name ^ "\n")
	       in
		 idx
	       end
	   | Some sock_fd => 
	       let
		 val _ = print ("Socket created with descriptor: " ^ Int.toString sock_fd ^ "\n");

		 (* Get interface index *)
		 val if_idx_opt = get_interface_index sock_fd if_name;
	       in
		 case if_idx_opt of
		   None => 
		     let
		       val _ = print ("Error: Could not get index for interface " ^ if_name ^ "\n")
		     in
		       idx + 1
		     end
		 | Some if_idx =>
		     let
		       val _ = print ("Interface " ^ if_name ^ " has index " ^ Int.toString if_idx ^ " (port " ^ Int.toString port ^ ")\n");

		       (* Bind socket to this interface *)
		       val binding_result = raw_socket_bind sock_fd if_idx;
		       val _ = if binding_result then
				print ("Successfully bound to interface " ^ if_name ^ "\n")
			       else
				print ("Failed to bind to interface " ^ if_name ^ "\n");

		       (* Add port mapping *)
		       val _ = port_map := (port, if_idx, sock_fd)::(!port_map);
		     in
		       idx + 1
		     end
	       end
	 end)) 0 interfaces;

	 (* Main packet processing loop using poll *)
	 fun process_packets () =
	   let
	     (* Create a poll structure with all the sockets *)
	     val poll_fds = List.map (fn (port, idx, sock) => (sock, 1)) (!port_map);

	     val poll_result = raw_socket_poll poll_fds (~1); (* -1 means wait indefinitely *)
	   in
	     case poll_result of
	       None => 
		 let
		   val _ = print "Poll error or timeout\n";
		 in
		   process_packets ()
		 end
	     | Some (ready_count, revents_list) =>
		 let
		   (* Function to check each interface for activity *)
		   fun check_interfaces port_map_list revents_list poll_idx =
		     case (port_map_list, revents_list) of
		       ([], _) => ()
		     | (_, []) => ()
		     | ((port, if_idx, sock)::ports_rest, revents::revents_rest) =>
			 if (revents mod 2) <> 0 then
			   let
(*
			     val _ = print ("Activity detected on port " ^ Int.toString port ^ " (socket: " ^ Int.toString sock ^ ")\n");
*)
			     (* Try to receive a packet on this socket *)
			     val packet_opt = raw_socket_recv sock buffer_size;
			   in
			     case packet_opt of
			       None => 
				 check_interfaces ports_rest revents_rest (poll_idx + 1)
			     | Some packet =>
				 let

				   (* Convert packet to boolean list *)
				   val packet_bl = packet_to_bool_list packet;

(*
				   val _ = print ("Received packet on port " ^ Int.toString port ^ ": " ^ (array_to_hex_string packet) ^ "\n");
*)
(*
				   val _ = print ("Packet converted to " ^ Int.toString (List.length packet_bl) ^ " bits\n");
*)
                                   

				   (* Execute P4 program *)
(*
				   val result = cake_top_exec (array_to_list packet, port);
*)
				   val result = cake_top_exec (packet_bl, port);
				 in
				   case result of
				     None => 
				       (* Error in packet processing *)
				       print ("Error processing packet from port " ^ Int.toString port ^ "\n")
				     | Some out_packets =>
				       (* Process each output packet *)
				       List.app (fn (out_packet_bits, out_port) =>
					 let
					   (* val _ = print ("Forwarding packet to port " ^ Int.toString out_port ^ "\n"); *)

					   (* Find the socket for the output port *)
					   val (out_if_idx_opt, out_sock_opt) = find_if_index_and_sock out_port (!port_map);
(*
					   val _ = print ("Finished search for socket for the output port\n")
*)
					 in
					   case (out_if_idx_opt, out_sock_opt) of
					     (Some out_if_idx, Some out_sock) =>
					       let
						 (* Convert the bits back to a packet buffer *)
						 val out_buffer = bool_list_to_packet out_packet_bits;

						 (* Send the packet *)
						 val send_result = raw_socket_sendto out_sock out_if_idx out_buffer;
(*
				                 val _ = print ("Sending packet on port " ^ Int.toString out_port ^ ": " ^ (array_to_hex_string (from_w8list out_buffer)) ^ "\n");
*)
(*
						 (* Send the packet *)
						 val send_result = raw_socket_sendto out_sock out_if_idx (from_w8list out_buffer);
*)
						 val _ = 
						   case send_result of
						     None => print ("Failed to send packet to port " ^ Int.toString out_port ^ "\n")
						   | Some bytes => () (* print ("Sent " ^ Int.toString bytes ^ " bytes to port " ^ Int.toString out_port ^ "\n") *)
					       in
						 ()
					       end
					   | _ => print ("Unknown output port: " ^ Int.toString out_port ^ "\n")
					 end) out_packets;
				   (* Rest of packet processing... *)
				   check_interfaces ports_rest revents_rest (poll_idx + 1)
				 end
			   end
			 else
			   check_interfaces ports_rest revents_rest (poll_idx + 1);
		 in
		   check_interfaces (!port_map) revents_list 0;
		   process_packets ()
		 end
	   end;
     in
       process_packets ()
     end
     handle InputError parse_err_msg => TextIO.print_err parse_err_msg
(* TODO: Factor out a function just for parsing input, then put this exception handler on that function
     handle _ => TextIO.print_err ("Usage: " ^ CommandLine.name() ^ " [buffer_size] -i <port@interface1> [-i <port@interface2> ...]\n")
*);’
   ;

 in
  (* TODO: Can this be replaced with something more short-handish? *)
  “SNOC
    (Dlet unknown_loc (Pcon NONE [])
     (App Opapp [Var (Short "main"); Con NONE []]))
     ^(get_ml_prog_state() |> get_prog)”
   |> EVAL |> concl |> rhs
 end
;

(* This function takes a program name as a string (e.g. "test_program", without suffix),
 * an actx and astate (HOL4 terms which can be obtained from the HOL4P4 import tool)
 * a maximum number of reduction steps (e.g. 140) and then constructs a CakeML sexp that
 * can be compiled to a command-line program that concretely executes the P4 program in
 * actx from the initial state astate, then prints the resulting outgoing packets.
 *
 * With the inlogic flag set to false, you get a CakeML .sexp file that you can compile
 * in a separate step. With the inlogic flag set to true, you get a .S that you can link
 * with a binary containing the foreign function implementations *)
fun translate_p4 progname actx astate n_max debug_mode inlogic =
 let
  val _ =
    let
     (* TODO: Fix option type? *)
     val cake_top_exec_def =
      Define
       ‘cake_top_exec input = SOME $ p4_get_output_list (arch_multi_exec_total ^actx (p4_append_input_list [input] ^astate) ^n_max)’;

     (* TODO: This is the bottleneck... *)
     val _ = translate cake_top_exec_def;
    in
     ()
    end

  val prog = append_prog_p4_wrapper debug_mode ();
 in
  if inlogic
  then
   let
     val progname_tm = stringSyntax.fromMLstring progname
     val prog_def =
      Define ‘^progname_tm = ^prog’;
    val _ = eval_cake_compile_x64 "" prog_def (progname^".S")
   in
    ()
   end
  else astToSexprLib.write_ast_to_file (progname^".sexp") prog
 end
;

end

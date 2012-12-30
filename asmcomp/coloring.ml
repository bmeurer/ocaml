(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                   Benedikt Meurer, os-cillation GmbH                *)
(*                                                                     *)
(*    Copyright 1998 Institut National de Recherche en Informatique    *)
(*    et en Automatique. Copyright 2012 Benedikt Meurer. All rights    *)
(*    reserved.  This file is distributed  under the terms of the Q    *)
(*    Public License version 1.0.                                      *)
(*                                                                     *)
(***********************************************************************)

(* Register allocation using the "Iterated Register Coalescing" scheme
   described in POPL'96, and TOPLAS v18 #3, pp 325-353.
   
   The implementation differs in the following ways:
  
   1. Moves are sorted such that higher rated moves are coalesced first.
   2. The freeze worklist is sorted such that lower rated registers are
      frozen first, where the freeze rating of a register is the sum of
      all move ratings this register is involved into.
 *)

type move_status = Active | Worklist | Removed

type move =
  { ri: Reg.t;
    rj: Reg.t;
    mutable weight: int;
    mutable status: move_status }

open Mach
open Reg

let allocate_registers fd =
  (* List of low-degree non-move related (virtual) registers *)
  let simplify_worklist = ref Reg.Set.empty in
  (* Low-degree move-related (virtual) registers *)
  let freeze_worklist = ref Reg.Set.empty in
  (* High-degree (virtual) registers *)
  let spill_worklist = ref Reg.Set.empty in

  (* Registers that have been coalesced *)
  let coalesced = ref Reg.Set.empty in
  (* Stack containing temporaries removed from the graph *)
  let select_stack = ref [] in

  (* Number of moves enabled for possible coalescing *)
  let worklist_moves = ref 0 in
  (* The actual moves, sorted by weight (decreasing) *)
  let moves = ref [] in

  (* Mapping from register stamp to the list of moves of this register *)
  let move_list = Array.make (Reg.num_registers()) [] in
  (* Mapping from register stamp to the move count of this register *)
  let move_count = Array.make (Reg.num_registers()) 0 in

  (* Mapping from register stamp to the coalesced register *)
  let alias = Array.make (Reg.num_registers()) Reg.dummy in

  (* Returns the adjacent nodes of the register. *)
  let adjacent reg =
    let cl = Proc.register_class reg in
    let excluded =
      List.fold_left
        (fun s r -> Reg.Set.add r s)
        !coalesced
        !select_stack in
    List.filter
      (fun r -> Proc.register_class r = cl && not(Reg.Set.mem r excluded))
      reg.interf in

  (* Return the aliased registers (if any). *)
  let rec chase reg =
    if Reg.Set.mem reg !coalesced then chase alias.(reg.stamp) else reg in

  (* Enable all moves of the register. *)
  let enable_moves reg =
    List.iter
      (fun mv ->
         if mv.status = Active then begin
           incr worklist_moves;
           mv.status <- Worklist
         end)
      move_list.(reg.stamp) in

  (* Decrement the degree of the register. *)
  let decrement_degree reg =
    let olddeg = reg.degree in
    reg.degree <- olddeg - 1;
    let cl = Proc.register_class reg in
    if olddeg = Proc.num_available_registers.(cl) then begin
      enable_moves reg;
      List.iter enable_moves (adjacent reg);
      spill_worklist := Reg.Set.remove reg !spill_worklist;
      if move_count.(reg.stamp) <> 0 then
        freeze_worklist := Reg.Set.add reg !freeze_worklist
      else
        simplify_worklist := Reg.Set.add reg !simplify_worklist
    end in

  (* Simplify an abitrary register on the simplify worklist. *)
  let simplify() =
    let reg = Reg.Set.choose !simplify_worklist in
    simplify_worklist := Reg.Set.remove reg !simplify_worklist;
    select_stack := reg :: !select_stack;
    List.iter decrement_degree (adjacent reg) in

  (* Add the register to the simplify worklist if unfrozen. *)
  let add_worklist reg =
    let cl = Proc.register_class reg in
    if reg.loc = Unknown
    && move_count.(reg.stamp) = 0
    && reg.degree < Proc.num_available_registers.(cl) then begin
      freeze_worklist := Reg.Set.remove reg !freeze_worklist;
      simplify_worklist := Reg.Set.add reg !simplify_worklist
    end
  in

  (* Combine the registers ru and rv. *)
  let combine ru rv =
    let rec merge_moves ul vl =
      begin match ul, vl with
          [], l
        | l, [] ->
            l
        | { status = Removed } :: ul, vl
        | ul, { status = Removed } :: vl ->
            merge_moves ul vl
        | (mu :: remu as ul), (mv :: remv as vl) ->
            let n = mu.ri.stamp - mv.ri.stamp in
            let n = if n <> 0 then n else mu.rj.stamp - mv.rj.stamp in
            if n < 0 then mu :: merge_moves remu vl
            else if n = 0 then mu :: merge_moves remu remv
            else mv :: merge_moves ul remv
      end in
    if Reg.Set.mem rv !freeze_worklist then
      freeze_worklist := Reg.Set.remove rv !freeze_worklist
    else
      spill_worklist := Reg.Set.remove rv !spill_worklist;
    coalesced := Reg.Set.add rv !coalesced;
    let v = rv.stamp and u = ru.stamp in
    alias.(v) <- ru;
    move_list.(u) <- merge_moves move_list.(u) move_list.(v);
    move_count.(u) <- List.length move_list.(u);
    List.iter
      (fun rt ->
         Interf.add_edge rt ru;
         decrement_degree rt)
      (adjacent rv);
    let cl = Proc.register_class ru in
    if ru.degree >= Proc.num_available_registers.(cl)
    && Reg.Set.mem ru !freeze_worklist then begin
      freeze_worklist := Reg.Set.remove ru !freeze_worklist;
      spill_worklist := Reg.Set.add ru !spill_worklist
    end in

  (* Coalesce an abitrary move from the move worklist. *)
  let coalesce() =
    let conservative ru rv =
      let cl = Proc.register_class ru in
      assert (cl = Proc.register_class rv);
      let avail_regs = Proc.num_available_registers.(cl) in
      let k = ref 0 in
      let count r = if r.degree >= avail_regs then incr k in
      List.iter count (adjacent ru);
      List.iter count (adjacent rv);
      !k < avail_regs in
    let ok ru rv =
      let cl = Proc.register_class rv in
      let avail_regs = Proc.num_available_registers.(cl) in
      List.for_all
        (fun rt ->
           rt.degree < avail_regs
           || rt.loc <> Unknown
           || Interf.has_edge rt ru)
        (adjacent rv) in
    let rec cleanup = function
        { status = Removed } :: l -> cleanup l
      | l -> l in
    let rec next = function
        { status = Worklist } as mv :: _ -> mv
      | _ :: l -> next l
      | _ -> assert false in
    moves := cleanup !moves;
    let mov = next !moves in
    decr worklist_moves;
    mov.status <- Removed;
    let rx = chase mov.ri and ry = chase mov.rj in
    let (ru, rv) = if ry.loc = Unknown then (rx, ry) else (ry, rx) in
    if ru.stamp = rv.stamp then
      add_worklist ru
    else if rv.loc <> Unknown || Interf.has_edge ru rv then begin
      add_worklist ru;
      add_worklist rv
    end else if (ru.loc <> Unknown && ok ru rv)
             || (ru.loc = Unknown && conservative ru rv) then begin
      combine ru rv;
      add_worklist ru
    end else begin
      mov.status <- Active
    end in

  (* Freeze all moves with the given register. *)
  let freeze_moves reg =
    let n = reg.stamp in
    List.iter
      (function
           { status = Removed } -> ()
         | mov ->
             if mov.status = Worklist then decr worklist_moves;
             mov.status <- Removed;
             let ru = chase mov.ri in
             let rv = if ru.stamp = n then chase mov.rj else ru in
             let cnt = move_count.(rv.stamp) - 1 in
             move_count.(rv.stamp) <- cnt;
             if cnt = 0 then begin
               let cl = Proc.register_class rv in
               if rv.degree < Proc.num_available_registers.(cl) then begin
                 freeze_worklist := Reg.Set.remove rv !freeze_worklist;
                 simplify_worklist := Reg.Set.add rv !simplify_worklist
               end
             end)
      move_list.(n);
    move_count.(n) <- 0;
    move_list.(n) <- [] in

  (* Freeze a register from the freeze worklist. *)
  let freeze() =
    let cost reg =
      let rec cost res = function
          [] -> res
        | { status = Removed } :: rem -> cost res rem
        | { weight = weight } :: rem -> cost (res + weight) rem in
      cost 0 move_list.(reg.stamp) in
    let reg =
      Reg.Set.fold
        (fun r1 r2 -> if cost r1 < cost r2 then r1 else r2)
        !freeze_worklist
        (Reg.Set.choose !freeze_worklist) in
    freeze_worklist := Reg.Set.remove reg !freeze_worklist;
    simplify_worklist := Reg.Set.add reg !simplify_worklist;
    freeze_moves reg in

  (* Spill a register from spill worklist. *)
  let select_spill() =
    let reg =
      Reg.Set.fold
        (fun r1 r2 ->
           let c1 = r1.spill_cost and d1 = r1.degree in
           let c2 = r2.spill_cost and d2 = r2.degree in
           let n = c1 * d2 - c2 * d1 in
           let n = if n <> 0 then n else c1 - c2 in
           let n = if n <> 0 then n else d2 - d1 in
           if n < 0 then r1 else r2)
        !spill_worklist
        (Reg.Set.choose !spill_worklist) in
    spill_worklist := Reg.Set.remove reg !spill_worklist;
    simplify_worklist := Reg.Set.add reg !simplify_worklist;
    freeze_moves reg in

  (* Where to start the search for a suitable register.
     Used to introduce some "randomness" in the choice between registers
     with equal scores. This offers more opportunities for scheduling. *)
  let start_register = Array.make Proc.num_register_classes 0 in

  (* Assign stack slot to the register. *)
  let assign_stack_slot reg =
    let cl = Proc.register_class reg in
    let nslots = Proc.num_stack_slots.(cl) in
    let conflict = Array.create nslots false in
    List.iter
      (fun r ->
         begin match chase r with
             { loc = Stack(Local n) } as r ->
               if Proc.register_class r = cl then conflict.(n) <- true
           | _ -> ()
         end)
      reg.interf;
    let slot = ref 0 in
    while !slot < nslots && conflict.(!slot) do incr slot done;
    reg.loc <- Stack(Local !slot);
    if !slot >= nslots then Proc.num_stack_slots.(cl) <- !slot + 1 in

  (* Assign location to the register, the best we can. *)
  let assign_location reg =
    let cl = Proc.register_class reg in
    let first_reg = Proc.first_available_register.(cl) in
    let num_regs = Proc.num_available_registers.(cl) in
    let conflict = Array.create num_regs false in
    let start = start_register.(cl) in
    if num_regs > 0 then begin
      List.iter
        (fun r ->
           begin match chase r with
               { loc = Reg n } ->
                 let n = n - first_reg in
                 if n >= 0 && n < num_regs then
                   conflict.(n) <- true
             | _ -> ()
           end)
        reg.interf;
      let i = ref 0 in
      while !i < num_regs && reg.loc = Unknown do
        let n = start + !i in
        let n = if n < num_regs then n else n - num_regs in
        if not(conflict.(n)) then begin
          reg.loc <- Reg(first_reg + n);
          if Proc.rotate_registers then
            let start = start + 1 in
            start_register.(cl) <- if start >= num_regs then 0 else start
        end else
          incr i
      done
    end;
    if reg.loc = Unknown then begin
      (* We need to use a stack slot *)
      reg.spill <- true;
      assign_stack_slot reg
    end in

  (* Collect the moves *)
  let movetbl = Hashtbl.create 31 in
  let rec collect weight i =
    let rec insert_sorted mov = function
        [] -> [mov]
      | m :: rem as l ->
          let n = mov.ri.stamp - m.ri.stamp in
          let n = if n <> 0 then n else mov.rj.stamp - m.rj.stamp in
          assert (n <> 0);
          if n < 0 then mov :: l
          else m :: insert_sorted mov rem in
    begin match i.desc with
        Iend | Ireturn | Iexit _ | Iraise
      | Iop(Itailcall_ind | Itailcall_imm _) -> ()
      | Iop(Imove) ->
          let ri = i.res.(0) and rj = i.arg.(0) in
          if not(ri.spill) && not(rj.spill) then begin
            let i = ri.stamp and j = rj.stamp in
            if i <> j then begin
              let (ri, rj) as p = if i < j then (ri, rj) else (rj, ri) in
              let mov =
                (try Hashtbl.find movetbl p
                 with Not_found ->
                   let mov = { ri; rj; weight = 0; status = Worklist } in
                   Hashtbl.add movetbl p mov;
                   incr worklist_moves;
                   moves := mov :: !moves;
                   move_count.(i) <- move_count.(i) + 1;
                   move_list.(i) <- insert_sorted mov move_list.(i);
                   move_count.(j) <- move_count.(j) + 1;
                   move_list.(j) <- insert_sorted mov move_list.(j);
                   mov) in
              mov.weight <- mov.weight + weight
            end
          end;
          collect weight i.next
      | Iop _ ->
          collect weight i.next
      | Iifthenelse(_, ifso, ifnot) ->
          collect (weight / 2) ifso;
          collect (weight / 2) ifnot;
          collect weight i.next
      | Iswitch(_, cases) ->
          for i = 0 to Array.length cases - 1 do
            collect (weight / 2) cases.(i)
          done;
          collect weight i.next
      | Iloop(body) ->
          (* Avoid overflow of weight and spill_cost *)
          collect (if weight < 1000 then 8 * weight else weight) body;
          collect weight i.next
      | Icatch(_, body, handler) ->
          collect weight body;
          collect weight handler;
          collect weight i.next
      | Itrywith(body, handler) ->
          collect weight body;
          collect weight handler;
          collect weight i.next
    end in
  collect 8 fd.fun_body;
  moves := List.fast_sort (fun mov1 mov2 -> mov2.weight - mov1.weight) !moves;

  (* Reset the stack slot counts *)
  for i = 0 to Proc.num_register_classes - 1 do
    Proc.num_stack_slots.(i) <- 0;
  done;

  (* Assign (virtual) registers to worklists.
     Pre-allocate spilled registers in the stack. *)
  List.iter
    (fun reg ->
       let cl = Proc.register_class reg in
       if reg.spill then begin
         (* Preallocate the registers in the stack *)
         assign_stack_slot reg
       end else if reg.degree >= Proc.num_available_registers.(cl) then
         spill_worklist := Reg.Set.add reg !spill_worklist
       else if move_list.(reg.stamp) <> [] then
         freeze_worklist := Reg.Set.add reg !freeze_worklist
       else
         simplify_worklist := Reg.Set.add reg !simplify_worklist)
    (Reg.all_registers());

  (* Main loop *)
  let rec loop() =
    if not(Reg.Set.is_empty !simplify_worklist) then begin
      simplify(); loop()
    end else if !worklist_moves <> 0 then begin
      coalesce(); loop()
    end else if not(Reg.Set.is_empty !freeze_worklist) then begin
      freeze(); loop()
    end else if not(Reg.Set.is_empty !spill_worklist) then begin
      select_spill(); loop()
    end else () in
  loop();

  (* Assign locations *)
  List.iter assign_location !select_stack;
  Reg.Set.iter (fun reg -> reg.loc <- (chase reg).loc) !coalesced

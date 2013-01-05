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

(* Register allocation using the "Optimistic Register Coalescing" scheme
   described in TOPLAS v26 #4, pp 735-765. *)

open Mach
open Reg

let allocate_registers fd =
  (* List of low-degree (virtual) registers *)
  let simplify_worklist = ref Reg.Set.empty in
  (* High-degree (virtual) registers *)
  let spill_worklist = ref Reg.Set.empty in

  (* Registers that have been coalesced *)
  let coalesced = ref Reg.Set.empty in
  (* Stack containing temporaries removed from the graph *)
  let select_stack = ref [] in

  (* Mapping from register stamp to the coalesced register *)
  let alias = Array.make (Reg.num_registers()) Reg.dummy in

  (* Saved interference lists *)
  let saved_interf = Array.make (Reg.num_registers()) [] in
  (* Saved spill costs *)
  let saved_spill_cost = Array.make (Reg.num_registers()) 0 in

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

  (* Decrement the degree of the register. *)
  let decrement_degree reg =
    let olddeg = reg.degree in
    reg.degree <- olddeg - 1;
    let cl = Proc.register_class reg in
    if olddeg = Proc.num_available_registers.(cl) then begin
      spill_worklist := Reg.Set.remove reg !spill_worklist;
      simplify_worklist := Reg.Set.add reg !simplify_worklist
    end in

  (* Simplify an abitrary register on the simplify worklist. *)
  let simplify() =
    let reg = Reg.Set.choose !simplify_worklist in
    simplify_worklist := Reg.Set.remove reg !simplify_worklist;
    select_stack := reg :: !select_stack;
    List.iter decrement_degree (adjacent reg) in

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
    simplify_worklist := Reg.Set.add reg !simplify_worklist in

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

  (* Fixes the interference graph for a given primitive register. *)
  let fix_adj rn =
    let saved_interf = saved_interf.(rn.stamp) in
    let rec cleanup = function
        interf when interf == saved_interf -> interf
      | [] -> assert false
      | rv :: interf ->
          if rv.loc = Unknown then
            rv.interf <- List.filter (fun r -> r.stamp <> rn.stamp) rv.interf;
          Interf.remove_edge rn rv;
          cleanup interf in
    rn.interf <- cleanup rn.interf;
    List.iter (fun rv -> Interf.add_edge (chase rv) rn) rn.interf in

  (* Undoes the coalescing of the given register. *)
  let undo_coalescing reg =
    let primitive_regs =
      List.filter
        (fun r -> (chase r).stamp = reg.stamp)
        (Reg.all_registers()) in
    List.iter
      (fun r -> 
         fix_adj r;
         let n = r.stamp in
         alias.(n) <- r;
         r.spill_cost <- saved_spill_cost.(n);
         coalesced := Reg.Set.remove r !coalesced)
      primitive_regs;
    primitive_regs
  in

  (* Compute the set (bit mask) of possible registers *)
  let compute_register_mask reg =
    let cl = Proc.register_class reg in
    let first_reg = Proc.first_available_register.(cl) in
    let num_regs = Proc.num_available_registers.(cl) in
    if num_regs = 0 then 0L else begin
      assert (num_regs <= 64);
      List.fold_left
        (fun mask r ->
           begin match chase r with
               { loc = Reg n } ->
                 let n = n - first_reg in
                 if n >= 0 && n < num_regs then
                   Int64.logand (Int64.lognot (Int64.shift_left 1L n)) mask
                 else
                   mask
             | _ -> mask
           end)
        (let n = 64 - num_regs in
         Int64.shift_right (Int64.shift_left (-1L) n) n)
        reg.interf
    end in

  (* Where to start the search for a suitable register.
     Used to introduce some "randomness" in the choice between registers
     with equal scores. This offers more opportunities for scheduling. *)
  let start_register = Array.make Proc.num_register_classes 0 in

  (* TODO *)
  let choose_location reg mask =
    if mask = 0L then Unknown else begin
      let cl = Proc.register_class reg in
      let num_regs = Proc.num_available_registers.(cl) in
      let start = start_register.(cl) in
      let rec choose i =
        if i >= num_regs then Unknown else begin
          let n = start + i in
          let n = if n < num_regs then n else n - num_regs in
          if Int64.logand mask (Int64.shift_left 1L n) = 0L then
            choose (i + 1)
          else begin
            if Proc.rotate_registers then begin
              let start = start + 1 in
              start_register.(cl) <- if start >= num_regs then 0 else start
            end;
            let first_reg = Proc.first_available_register.(cl) in
            Reg(first_reg + n)
          end
        end in
      choose 0
    end in

  (* Combine two registers ru and rv *)
  let combine ru rv =
    coalesced := Reg.Set.add rv !coalesced;
    alias.(rv.stamp) <- ru;
    List.iter
      (fun rt ->
         Interf.add_edge rt ru;
         if rt.loc = Unknown then rt.degree <- rt.degree - 1)
      (adjacent rv) in

  (* XXX: Als potentielle Optimierung die unter den Stack zu schiebenden
          primitives wieder durch combine vereinigen und nur einen Knoten
          unter den Stack packen. Der wird bei Bedarf erneut gesplitted *)

  (* TODO *)
  let try_primitives reg stack =
    let primitives = undo_coalescing reg in
    assert (primitives <> []);
    (* Compute the colorable splits *)
    let splits =
      List.fold_left
        (fun splits reg -> 
           let regmask = compute_register_mask reg in
           if regmask = 0L then splits else begin
             List.rev_append
               splits
               (List.map
                  (fun ((cost, mask, regl) as split) ->
                     assert (mask <> 0L);
                     let mask = Int64.logand mask regmask in
                     if mask = 0L then split
                     else (cost + reg.spill_cost, mask, reg :: regl))
                  splits)
           end)
        [(0, (-1L), [])]
        primitives in
    (* Choose the split with the highest spill cost *)
    let (_, mask, colorable) =
      List.fold_left
        (fun ((cost1, _, regl1) as split1) ((cost2, _, regl2) as split2) ->
           let n = cost2 - cost1 in
           let n =
             if n = 0 then n
             else List.length regl2 - List.length regl1 in
           if n < 0 then split1 else split2)
        (0, 0L, [])
        splits in
    (* Try to assign location to the colorable registers *)
    let loc = choose_location reg mask in
    List.iter (fun reg -> reg.loc <- loc) colorable;
    (* Recombine the remaining (uncolored) registers again *)
    let rec recombine = function
        [] -> assert false
      | reg :: rem when reg.loc <> Unknown -> recombine rem
      | reg :: rem -> List.fold_left
                        (fun ru rv ->
                           if rv.loc = Unknown then combine ru rv; ru)
                        reg rem in
    let reg = recombine primitives in
    if loc <> Unknown then begin
      (* Place the uncolored register at the bottom of the select stack *)
      reg :: stack
    end else begin
      (* We have to actually spill the register *)
      assign_stack_slot reg;
      stack
    end in

  (* Assign location to the register, the best we can. *)
  let rec select stack rescheduled =
    begin match stack, rescheduled with
        [], [] -> ()
      | [], rescheduled -> select (List.rev rescheduled) []
      | reg :: stack, rescheduled ->
          let mask = compute_register_mask reg in
          let loc = choose_location reg mask in
          if loc <> Unknown then begin
            reg.loc <- loc;
            select stack rescheduled
          end else
            select stack (try_primitives reg rescheduled)
    end in

  (* Reset the stack slot counts *)
  for i = 0 to Proc.num_register_classes - 1 do
    Proc.num_stack_slots.(i) <- 0;
  done;

  (* Save interf lists/spill costs and initialize alias *)
  List.iter
    (fun r ->
       let n = r.stamp in
       alias.(n) <- r;
       saved_interf.(n) <- r.interf;
       saved_spill_cost.(n) <- r.spill_cost)
    (Reg.all_registers());

  (* Coalesce all moves *)
  instr_iter
    (fun i ->
       begin match i.desc with
           Iop(Imove) -> (* XXX: Ispill? Ireload? *)
             let rx = chase i.res.(0) and ry = chase i.arg.(0) in
             let (ru, rv) = if ry.loc = Unknown then (rx, ry) else (ry, rx) in
             if rv.loc = Unknown 
             && ru.stamp <> rv.stamp
             && not(Interf.has_edge ru rv) then begin
               if ru.loc <> Unknown then begin
                 (* Section 7.2: Precoloring with Optimistic Coalescing *)
                 () (*FIXME*)
               end else begin
                 (* Combine ru and rv *)
                 combine ru rv
               end
             end
         | _ -> ()
       end)
    fd.fun_body;

  (* Assign (virtual) registers to worklists. *)
  List.iter
    (fun reg ->
       let cl = Proc.register_class reg in
       if reg.degree >= Proc.num_available_registers.(cl) then
         spill_worklist := Reg.Set.add reg !spill_worklist
       else
         simplify_worklist := Reg.Set.add reg !simplify_worklist)
    (Reg.all_registers());

  (* Main loop *)
  let rec loop() =
    if not(Reg.Set.is_empty !simplify_worklist) then begin
      simplify(); loop()
    end else if not(Reg.Set.is_empty !spill_worklist) then begin
      select_spill(); loop()
    end else () in
  loop();

  (* Assign locations *)
  select !select_stack [];
  Reg.Set.iter (fun reg -> reg.loc <- (chase reg).loc) !coalesced

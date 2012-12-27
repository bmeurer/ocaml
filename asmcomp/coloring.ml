(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Register allocation by coloring of the interference graph *)

module OrderedRegSet =
  Set.Make(struct
    type t = Reg.t
    let compare r1 r2 =
      let open Reg in
      let c1 = r1.spill_cost and d1 = r1.degree in
      let c2 = r2.spill_cost and d2 = r2.degree in
      let n = c2 * d1 - c1 * d2 in
      if n <> 0 then n else
        let n = c2 - c1 in
        if n <> 0 then n else
          let n = d1 - d2 in
          if n <> 0 then n else r1.stamp - r2.stamp
  end)

open Reg

let allocate_registers() =

  (* Iterate over all registers preferred by the given register (transitive) *)
  let rec iter_preferred f reg =
    let p = reg.prefer in
    if p <> [] then begin
      reg.visited <- true;
      List.iter (fun (r, w) ->
                   if not r.visited then begin
                     f r w;
                     iter_preferred f r
                   end) p;
      reg.visited <- false
    end in

  (* Assign a stack slot to a register, the best we can. *)
  let assign_stack_slot reg =
    let num_slots = !Proc.num_stack_slots in
    let score = Array.create num_slots 0 in
    let record f = function
        { loc = Stack(Local n) } as r ->
          let cl = Proc.register_class r in
          for i = 0 to Proc.stack_slot_span.(cl) - 1 do
            let n = n + i in score.(n) <- f score.(n)
          done
      | _ -> () in
    iter_preferred
      (fun r w ->
         record (fun s -> s + w) r;
         if r.loc = Unknown then List.iter (record (fun s -> s - w)) r.interf)
      reg;
    List.iter
      (fun neighbour ->
         record (fun _ -> (-1000000)) neighbour;
         iter_preferred (fun r w -> record (fun s -> s - w) r) reg)
      reg.interf;
    (* Pick the location with the best score *)
    let cl = Proc.register_class reg in
    let span = Proc.stack_slot_span.(cl) in
    let best_score = ref (-1000000) and best_slot = ref num_slots in
    let n = ref num_slots and k = ref 0 in
    while !n > 0 do
      let slot = !n - 1 in
      if score.(slot) > !best_score then begin
        let s = !k + 1 in
        if s == span then begin
          best_score := score.(slot);
          best_slot := slot;
          k := 0
        end else
          k := s
      end else
        k := 0;
      n := slot
    done;
    reg.loc <- Stack(Local !best_slot);
    let max_slots = !best_slot + span in
    if max_slots > num_slots then begin
      Proc.num_stack_slots := max_slots
    end in

  (* Constrained regs with degree >= number of available registers,
     sorted by spill cost (highest first).
     The spill cost measure is [r.spill_cost / r.degree].
     [r.spill_cost] estimates the number of accesses to [r]. *)
  let constrained = ref OrderedRegSet.empty in

  (* Unconstrained regs with degree < number of available registers *)
  let unconstrained = ref [] in

  (* Preallocate the spilled registers in the stack.
     Split the remaining registers into constrained and unconstrained. *)
  let remove_reg reg =
    let cl = Proc.register_class reg in
    if reg.spill then begin
      (* Preallocate the registers in the stack *)
      assign_stack_slot reg
    end else if reg.degree < Proc.num_available_registers.(cl) then
      unconstrained := reg :: !unconstrained
    else begin
      constrained := OrderedRegSet.add reg !constrained
    end in

  (* Where to start the search for a suitable register.
     Used to introduce some "randomness" in the choice between registers
     with equal scores. This offers more opportunities for scheduling. *)
  let start_register = Array.create Proc.num_register_classes 0 in

  (* Assign a location to a register, the best we can. *)
  let assign_location reg =
    let cl = Proc.register_class reg in
    let first_reg = Proc.first_available_register.(cl) in
    let num_regs = Proc.num_available_registers.(cl) in
    let last_reg = first_reg + num_regs in
    let score = Array.create num_regs 0 in
    let best_score = ref (-1000000) and best_reg = ref (-1) in
    let start = start_register.(cl) in
    if num_regs > 0 then begin
      (* Favor the registers that have been assigned to pseudoregs for which
         we have a preference. If these pseudoregs have not been assigned
         already, avoid the registers with which they conflict. *)
      iter_preferred
        (fun r w ->
          match r.loc with
            Reg n -> if n >= first_reg && n < last_reg then
                       score.(n - first_reg) <- score.(n - first_reg) + w
          | Unknown ->
              List.iter
                (fun neighbour ->
                  match neighbour.loc with
                    Reg n -> if n >= first_reg && n < last_reg then
                             score.(n - first_reg) <- score.(n - first_reg) - w
                  | _ -> ())
                r.interf
          | _ -> ())
        reg;
      List.iter
        (fun neighbour ->
          (* Prohibit the registers that have been assigned
             to our neighbours *)
          begin match neighbour.loc with
            Reg n -> if n >= first_reg && n < last_reg then
                       score.(n - first_reg) <- (-1000000)
          | _ -> ()
          end;
          (* Avoid the registers that have been assigned to pseudoregs
             for which our neighbours have a preference *)
          iter_preferred
            (fun r w ->
              match r.loc with
                Reg n -> if n >= first_reg && n < last_reg then
                           score.(n - first_reg) <- score.(n - first_reg) - (w - 1)
                         (* w-1 to break the symmetry when two conflicting regs
                            have the same preference for a third reg. *)
              | _ -> ())
            neighbour)
        reg.interf;
      (* Pick the register with the best score *)
      for n = start to num_regs - 1 do
        if score.(n) > !best_score then begin
          best_score := score.(n);
          best_reg := n
        end
      done;
      for n = 0 to start - 1 do
        if score.(n) > !best_score then begin
          best_score := score.(n);
          best_reg := n
        end
      done
    end;
    (* Found a register? *)
    if !best_reg >= 0 then begin
      reg.loc <- Reg(first_reg + !best_reg);
      if Proc.rotate_registers then
        start_register.(cl) <- (if start+1 >= num_regs then 0 else start+1)
    end else begin
      (* Sorry, we must put the pseudoreg in a stack location *)
      assign_stack_slot reg
    end;
    (* Cancel the preferences of this register so that they don't influence
       transitively the allocation of registers that prefer this reg. *)
    reg.prefer <- [] in

  (* Reset the stack slot count *)
  Proc.num_stack_slots := 0;

  (* First pass: preallocate spill registers and split remaining regs
     Second pass: assign locations to constrained regs
     Third pass: assign locations to unconstrained regs *)
  List.iter remove_reg (Reg.all_registers());
  OrderedRegSet.iter assign_location !constrained;
  List.iter assign_location !unconstrained

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

(* Construction of the interference graph.
   Annotate pseudoregs with interference lists and preference lists. *)

val add_edge: Reg.t -> Reg.t -> unit
val remove_edge: Reg.t -> Reg.t -> unit
val has_edge: Reg.t -> Reg.t -> bool
val build_graph: Mach.fundecl -> unit

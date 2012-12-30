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

(* Register allocation by "Iterated Register Coalescing" *)

val allocate_registers: Mach.fundecl -> unit

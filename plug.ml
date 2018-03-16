(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2018 stephane.duprat81@gmail.com                        *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)




open Cil_types

module Pcg =
  Plugin.Register
    (struct
       let name = "Project Graph Explorer"
       let shortname = "pcg"
       let help = "generated call graph functions and call graph module"
     end)

(** Register the new Frama-C option "-hello". *)
module FunctionCg =
  Pcg.Empty_string
    (struct
       let option_name = "-pcg-f"
       let help = "generate function call graph" 
       let kind= `Tuning 
       let arg_name = "fcg-name"
       let default ="fcg.dot"
     end)

module ModuleCg =
  Pcg.Empty_string
    (struct
       let option_name = "-pcg-m"
       let help = "generate module call graph" 
       let kind= `Tuning 
       let arg_name = "mcg-name"
       let default ="mcg.dot"
     end)

module CgHead =
  Pcg.False
    (struct
       let option_name = "-pcg-head"
       let help = "include headers"
       let kind = `Correctness
     end)

module CgAll =
  Pcg.False
    (struct
       let option_name = "-pcg-all"
       let help = "one cg for each module"
       let kind = `Correctness
     end)


let logdeb3 msg =
  Pcg.debug ~level:3 msg

type function_node = {
  fname: string;
  fid : int;
  is_def:bool;
  fmod:string;
}

type module_node = {
  mname: string;
  mid: int;
  is_header:bool;
}

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)
module PairOrd     = struct type t = int * int let compare = compare end
module PairString = struct type t = string * string let compare = compare end
module PairStringSet = Set.Make(PairString)

type prj_desc = (function_node StringMap.t * module_node StringMap.t * PairStringSet.t * PairStringSet.t)

let cPT=ref 0

let new_id () =
  cPT := !cPT+1;
  !cPT

let is_header n = 
  try
    (String.sub n ((String.length n)-2) 2)=".h"
  with Invalid_argument(_) ->
    false

let string_map_filter f m =
  StringMap.fold (fun k e cur_map -> if (f k e) then (StringMap.add k e cur_map) else cur_map) m StringMap.empty

let string_map_exists e m =
  try
    ignore (StringMap.find e m);
    true
  with
      Not_found -> false

class c_get_called =
object (self) 
  inherit Visitor.frama_c_inplace as super

  val mutable called_list = [] 

  method get_called_list() = called_list;
  method add_func_called f =
    called_list<-if (List.exists ((=) f) called_list) then called_list else f::called_list;

  method vinst (i:instr) =
    match i with
        Call(_,{enode=Lval(Var({vname=n}),_)},_,_)      ->
          self#add_func_called n;
          Cil.DoChildren
      | _   -> Cil.DoChildren

end

let get_called_functions kf =
  match kf.fundec with
      Definition(f,_)   ->
        let v=new c_get_called
        in
          ignore (Visitor.visitFramacFunction (v :>Visitor.frama_c_visitor) f);
          v#get_called_list();
    | _       -> []


let add_edge_to_prj a ((mf,mm,gf,gm):prj_desc) b =
  let new_gf = 
    logdeb3 "add func %s -> %s" a b;
    PairStringSet.add (a,b)  gf
  and new_gm =
    let ma = (StringMap.find a mf).fmod
    and mb = (StringMap.find b mf).fmod
    in
      logdeb3 "add mod %s -> %s" ma mb;
      PairStringSet.add (ma,mb)  gm
  in
    (mf,mm,new_gf,new_gm)

let add_func_to_prj ((mf,mm,gf,gm) as prj:prj_desc) fname =
  if not (string_map_exists fname mf) 
  then
    let kf=  Globals.Functions.find_by_name fname in
    let owner= let {Lexing.pos_fname=n},_=Kernel_function.get_location kf in n in
    let new_mf=
      let fdesc={
        fname=fname;
        fid=new_id();
        is_def=Kernel_function.is_definition kf;
        fmod=owner;}
      in
        StringMap.add fname fdesc mf
    and new_mm =
      if not (string_map_exists owner mm)
      then
        let mod_desc={
          mname=owner;
          mid=new_id();
          is_header=is_header owner;
        } in
          StringMap.add  owner mod_desc mm
          else
            mm
    in
      (new_mf, new_mm, gf, gm)
      else
        prj

let compute_prj ()=
  let ffold kf ((mf,mm,gf,gm) as prj:prj_desc) =
    let name=Kernel_function.get_name kf 
    and called_functions = get_called_functions kf in
    let new_prj = add_func_to_prj prj name  in
    let new_prj =  List.fold_left add_func_to_prj new_prj called_functions in
      logdeb3 "computing %s function\n" name;
      List.fold_left (add_edge_to_prj name) new_prj called_functions
  in
  let init_prj = (StringMap.empty, StringMap.empty, PairStringSet.empty,  PairStringSet.empty) in
    Globals.Functions.fold ffold init_prj

let filter_header ((mf,mm,gf,gm) as prj:prj_desc)=
  let new_mm = string_map_filter (fun _ e -> not e.is_header) mm in
  let new_mf = string_map_filter (fun _ e -> string_map_exists e.fmod new_mm) mf in
  let new_gm = PairStringSet.filter (fun (a,b) -> (string_map_exists a new_mm) && (string_map_exists b new_mm)) gm in
  let new_gf = PairStringSet.filter (fun (a,b) -> (string_map_exists a new_mf) && (string_map_exists b new_mf)) gf 
  in
    (new_mf,new_mm,new_gf,new_gm)

let print_graph_func fd ((mf,mm,gf,gm) as prj:prj_desc)=
  let print_called()=
    let fiter (a,b)=
      Printf.fprintf fd "\t%s->%s\n" a b
    in
      PairStringSet.iter fiter gf

  and print_cluster_part ()=
    let print_cluster n mdesc=
      let filtered_mf= string_map_filter (fun k {fmod=p}->p=n) mf
      in
        Printf.fprintf fd "subgraph cluster_%d {\n" mdesc.mid;
        StringMap.iter (fun n d ->Printf.fprintf fd "\t%s;\n" n) filtered_mf;
        Printf.fprintf fd "\tlabel = \"%s\";\n\t}\n" (Filename.chop_extension (Filename.basename n))
    in
      StringMap.iter print_cluster mm
  in
    Printf.fprintf fd "digraph G {\n";
    Printf.fprintf fd "size=\"60,40\"; ratio = fill;\n";
    print_called();
    print_cluster_part();
    Printf.fprintf fd "}\n"

let center_prj_to_mod  m ((mf,mm,gf,gm) as prj:prj_desc)=

  let new_gf = 
    let ffilter (a,b) =
      let ma = (StringMap.find a mf).fmod
      and mb = (StringMap.find b mf).fmod
      in 
        (0 = (compare m ma)) || (0 = (compare m mb))
    in
      PairStringSet.filter ffilter gf
  in
  let new_mm = 
    let ffilter m _ =
	(* m is a module of a function of the function map
	   it exists in the function map an orig function whose module is m
	   or an dest functions whose module is m *)
      let ffind (a,b) =
	let ma = (StringMap.find a mf).fmod
	and mb = (StringMap.find b mf).fmod
	in 
        (0 = (compare m ma)) || (0 = (compare m mb))
      in
      PairStringSet.exists ffind new_gf
    in
    StringMap.filter ffilter mm
  in 
  let new_mf =
    (* only function that are orig or dest of graph *)
    let ffilter n f =
      PairStringSet.exists (fun (a,b) -> (0 = compare a n) || (0 = compare b n) ) new_gf
    in
    StringMap.filter ffilter mf


  in (new_mf,new_mm,new_gf,gm)


let print_graph_func_mod  m ((mf,mm,gf,gm) as prj:prj_desc)=
  logdeb3 "print_graph_func_mod %s" m;
  let print_called fd=
    let fiter (a,b)=
      Printf.fprintf fd "\t%s->%s\n" a b
    and ffilter (a,b) =
      let ma = (StringMap.find a mf).fmod
      and mb = (StringMap.find b mf).fmod
      in 
        (0 = (compare m ma)) || (0 = (compare m mb))
    in
      PairStringSet.iter fiter (PairStringSet.filter ffilter gf)
      
  and print_cluster_part fd =
    let print_cluster  n mdesc=
      let filtered_mf= string_map_filter (fun k {fmod=p}->p=n) mf
      in
        Printf.fprintf fd "subgraph cluster_%d {\n" mdesc.mid;
        StringMap.iter (fun n d ->Printf.fprintf fd "\t%s;\n" n) filtered_mf;
        Printf.fprintf fd "\tlabel = \"%s\";\n\t}\n" (Filename.chop_extension (Filename.basename n))
    in
(*      StringMap.iter print_cluster mm*)
        print_cluster m (StringMap.find m mm);
  in
    let fd = open_out ((Filename.chop_extension (Filename.basename m)) ^".dot");
    in
    Printf.fprintf fd "digraph G {\n";
    Printf.fprintf fd "//size=\"60,40\"; ratio = fill;\n";
    print_called fd;
    print_cluster_part fd;
    Printf.fprintf fd "}\n";
    close_out fd

let print_graph_mod fd ((mf,mm,gf,gm) as prj:prj_desc)=

  let print_called()=
    let fiter (a,b)=
      let desc_a=StringMap.find a mm
      and desc_b=StringMap.find b mm
      in
        Printf.fprintf fd "%d->%d\n" desc_a.mid desc_b.mid
    in
      PairStringSet.iter fiter gm

  and print_mod ()=
    let print_one_mod k mod_elt =
      Printf.fprintf fd "\t\"%d\" [shape=diamond, label=\"%s\", style=bold];\n"  mod_elt.mid (Filename.chop_extension (Filename.basename k))
    in
      StringMap.iter print_one_mod mm

  in
    Printf.fprintf fd "digraph G {\n";
    (* Printf.fprintf fd "size=\"60,40\"; ratio = fill;\n"; *)
    print_mod ();
    print_called();
    Printf.fprintf fd "}\n"


let print_graph_mod2 fd ((mf,mm,gf,gm) as prj:prj_desc)=

  let print_called()=
    let fiter (a,b)=
      let desc_a=StringMap.find a mm
      and desc_b=StringMap.find b mm
      in
        Printf.fprintf fd "%s->%s\n" 
	  (Filename.chop_extension (Filename.basename desc_a.mname))
	  (Filename.chop_extension (Filename.basename desc_b.mname))
    in
      PairStringSet.iter fiter gm
  in
    Printf.fprintf fd "digraph G {\n";
    Printf.fprintf fd "size=\"6,4\"; ratio = fill;\n";
    print_called();
    Printf.fprintf fd "}\n"



let run () =  

  let fcg_filename = FunctionCg.get()
  and mcg_filename = ModuleCg.get()
  in

    if (((String.length fcg_filename) >0) || ((String.length mcg_filename) >0) || (CgAll.get ()))
    then
      begin
        ignore (Ast.get());
        let prj = 
          let prj=compute_prj ()
          in
            if (CgHead.get ())
            then
              prj
            else
              filter_header prj
        in
	if (CgAll.get ())
        then
	  begin
            let (mf,mm,gf,gm) = prj;
	    in 
	    logdeb3 "print all" ;
	    (* StringMap.iter (fun m d -> print_graph_func_mod m prj) mm; *)
	    let print_graph_func_mod2 m prj =
	      let fd = open_out ((Filename.chop_extension (Filename.basename m)) ^".dot")
	      in
	      print_graph_func fd prj;
	      close_out fd
	    in
	    StringMap.iter (fun m d -> print_graph_func_mod2 m (center_prj_to_mod m prj)) mm;
	    
	  end;
        if ((String.length fcg_filename)>0)
          then
            begin
              try
                let o = open_out fcg_filename in
                  print_graph_func o prj;
                  close_out o
              with e ->
                Pcg.error
                  "error during output of function callgraph: %s"
                  (Printexc.to_string e)
            end;
          if ((String.length mcg_filename)>0)
          then
            begin
              try
                let o = open_out mcg_filename in
                  print_graph_mod2 o prj;
                  close_out o
              with e ->
                Pcg.error
                  "error during output of module callgraph: %s >%s<"
                  (Printexc.to_string e) mcg_filename
            end;

      end

let () = Db.Main.extend run

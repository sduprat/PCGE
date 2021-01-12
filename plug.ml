(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2020 stephane.duprat81@gmail.com                        *)
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
open Cabs

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

module CgComments_filename =
  Pcg.Empty_string
    (struct
       let option_name = "-pcg-comments"
       let help = "count comments per functions"
       let kind= `Tuning
       let arg_name = "comments_file"
       let default ="comments_count.txt"
     end)

module CommentOut =
  Pcg.False
    (struct
       let option_name = "-pcg-comment"
       let help = "comment metrics"
       let kind = `Correctness
     end)

module CgStack_filename =
  Pcg.Empty_string
    (struct
       let option_name = "-pcg-stack"
       let help = "stack computation" 
       let kind= `Tuning 
       let arg_name = "stack_file"
       let default ="stack.txt"
     end)

module CgStack_calls_filename =
  Pcg.Empty_string
    (struct
       let option_name = "-pcg-stack-calls"
       let help = "add additional calls (resulting from callback trough function pointers" 
       let kind= `Tuning 
       let arg_name = "stack_calls_file"
       let default ="stack_calls.txt"
     end)

module CgStack_caller =
  Pcg.True
    (struct
       let option_name = "-pcg-stack-caller"
       let help = "compute only for uncalled function"
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

module StringMap  = Map.Make(String)
module StringSet  = Set.Make(String)
module PairOrd    = struct type t = int * int let compare = compare end
module PairString = struct type t = string * string let compare = compare end
module PairStringSet = Set.Make(PairString)
module PairStringMap = Map.Make(PairString)

type prj_desc = (function_node StringMap.t * module_node StringMap.t * PairStringSet.t * PairStringSet.t)

let rec max_list l =
  match l with
    [] -> 0
   |t::q -> max t (max_list q) ;;

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

(*
 * counting comments
 *)

let m_function_comment_nb = ref PairStringMap.empty

let lines_of_string_list sl =
  let ffold (n:int) (s:string)  =
    n + (List.length (String.split_on_char '\n' s))
  in
  List.fold_left ffold 0 sl

let r_lines = ref []

let compute_comment_function (fname:string) (filepath:Filepath.position) lstart lend=
  let ffold ((pos1,pos2):cabsloc) str prev_n =
    if (((Filepath.Normalized.to_pretty_string filepath.pos_path)
         = (Filepath.Normalized.to_pretty_string pos1.pos_path))
        && pos1.pos_lnum>=lstart && pos1.pos_lnum<=lend)
    then
      prev_n + (lines_of_string_list [str])
    else
      prev_n
  in
  Cabshelper.Comments.fold ffold 0


let rec init_empty_list n =
  if n=0
  then
    []
  else
    "" :: (init_empty_list (n-1))

let compute_empty_lines_per_function (filename:string) =
  r_lines := [""];
  let in_channel = open_in filename in
  try
    let r_last_marker = ref 0 in
    while true do
      let line = input_line in_channel in
      let r = Str.regexp "^# \\([0-9]+\\)" in
      if Str.string_match r line 0
      then
        begin
          r_last_marker :=  (int_of_string (Str.matched_group 1 line));
          r_lines := init_empty_list !r_last_marker;
        end
      else
        r_lines := List.append !r_lines [line]
    done;
  with End_of_file ->
    close_in in_channel


class c_globals_function =
object (self)
  inherit Visitor.frama_c_inplace as super

  method vglob (g:global) =
    begin
      match g with
        GFun(({svar=vi}),(l1,l2)) ->
        begin
          let filename = Filename.basename (Format.asprintf "%a" Filepath.Normalized.pp_abs l1.pos_path) in
          if (Str.string_match (Str.regexp ".*\\.c$") filename 0)
          then
            (* only for function in .c file *)
            begin
              compute_empty_lines_per_function (Filepath.Normalized.to_pretty_string l1.pos_path) ;

              Pcg.debug ~level:3 "Gfun %s ===========>\n" vi.vname;
              List.iter (fun s -> Pcg.debug ~level:4  "%d %s \n" (List.length (String.split_on_char '\n' s)) s) (Globals.get_comments_global g);

              let nb_comment_header =
                let function_comments_list = Globals.get_comments_global g
                in
                if (List.length function_comments_list) > 0
                then
                  (* lines_of_string_list [ List.hd (List.rev (Globals.get_comments_global g))] *)
                  lines_of_string_list (Globals.get_comments_global g)
                else
                  0

              and nb_lines_function =
                let subarray =
                  try
                    Array.sub (Array.of_list !r_lines) l1.pos_lnum (l2.pos_lnum - l1.pos_lnum +1)
                  with Invalid_argument(_) ->
                    Printf.printf "ERROR : %d, %d, %d\n" (List.length !r_lines) l1.pos_lnum (l2.pos_lnum - l1.pos_lnum +1);
                    Array.sub (Array.of_list !r_lines) l1.pos_lnum (l2.pos_lnum - l1.pos_lnum +1)
                and ffold n s =
                  if (Str.string_match (Str.regexp "[a-zA-Z0-9 ;{}]+") s 0) then n+1 else n
                in
                Array.fold_left ffold 0 subarray

              and nb_comments_function =
                compute_comment_function vi.vname l1 l1.pos_lnum l2.pos_lnum
              in
              let nb_total_function = nb_comment_header + nb_lines_function
              and nb_total_comments_function = nb_comment_header + nb_comments_function
              in
              Pcg.debug ~level:3  "%s %d %d total %d (%dc) - %d\n"
                vi.vname l1.pos_lnum l2.pos_lnum nb_total_function nb_total_comments_function (nb_total_comments_function*100/nb_total_function);

              let module_name = (Filename.basename filename) in
              let m_f = (module_name,vi.vname) in
              m_function_comment_nb := PairStringMap.add m_f (nb_total_function,nb_total_comments_function) !m_function_comment_nb ;

              Cil.DoChildren
            end
          else
            Cil.SkipChildren
        end

      | _ -> Cil.SkipChildren

    end ;

  (* method vstmt (s:stmt) =
   *   try
   *     Pcg.debug ~level:3  "Gstmt===========>\n";
   *     let comment_list = (Globals.get_comments_stmt s) in
   *     List.iter (Pcg.debug ~level:4 "comment stmt = %s\n") comment_list;
   *     let prev_n = PairStringMap.find (current_module,current_function) !m_function_comment_nb
   *     and supp_n = if List.length comment_list > 0 then 1 else 0 
   *       (\* buggy behaviour of get_comments_stmt -> +1 per comment issue *\)
   *       (\*lines_of_string_list (Globals.get_comments_stmt s)*\)
   *     in m_function_comment_nb := PairStringMap.add (current_module,current_function) (prev_n+supp_n) !m_function_comment_nb; Pcg.debug ~level:3 "%d " prev_n;
   *     Cil.DoChildren
   *   with Not_found -> Cil.DoChildren *)


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
    let owner= let {Filepath.pos_path=n},_=Kernel_function.get_location kf in Filepath.Normalized.to_pretty_string n in
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
    (* Printf.fprintf fd "size=\"60,40\"; ratio = fill;\n"; *)
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
    (* Printf.fprintf fd "//size=\"60,40\"; ratio = fill;\n"; *)
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
    (* Printf.fprintf fd "size=\"6,4\"; ratio = fill;\n"; *)
    print_called();
    Printf.fprintf fd "}\n"

let computingmap = ref StringMap.empty 


let parse_stack_size_file prj =
  let parse_line line_str map =
    let reg = Str.regexp "^\\([A-Za-z0-9_]+\\)[ \t]+\\([0-9]+\\)" in
    if (Str.string_match reg line_str 0)
    then
      begin
        let n1 = Str.matched_group 1 line_str
        and n2 = Str.matched_group 2 line_str in
        Pcg.debug ~level:2 "function %s : %s" n1 n2 ;
        StringMap.add n1 (int_of_string n2) map
      end
    else
      begin
        Pcg.warning  "nothing to parse at this line %s" line_str ;
        map
      end
  in
  try
    let filename = CgStack_filename.get () in
    try
      let ref_file = open_in filename
      in
      try
        Pcg.debug ~level:2 "Parsing stack conf file %s\n" filename ;
        while true do
          computingmap := parse_line (input_line ref_file) !computingmap;
        done;      
      with End_of_file -> close_in ref_file
    with 
      Sys_error(str)    -> 
      Pcg.warning "Error opening file %s (%s)\n" filename str 
  with 
    (* no stack file  *)
    Not_found           ->
     Pcg.debug ~level:2 "No stack file set"

let computingset = ref PairStringSet.empty 

let parse_stack_call_file prj =
  let parse_line line_str set =
    let reg = Str.regexp "^\\([A-Za-z0-9_]+\\)[ \t]+\\([A-Za-z0-9_]+\\)" in
    if (Str.string_match reg line_str 0)
    then
      begin
        let f1 = Str.matched_group 1 line_str
        and f2 = Str.matched_group 2 line_str in
        Pcg.debug ~level:2 "add call %s -> %s" f1 f2 ;
        PairStringSet.add (f1,f2) set
      end
    else
      begin
        Pcg.warning  "nothing to parse at this line %s" line_str ;
        set
      end
  in
  try
    let filename = CgStack_calls_filename.get () in
    try
      let ref_file = open_in filename
      in
      try
        Pcg.debug ~level:2 "Parsing stack calls conf file %s\n" filename ;
        while true do
          computingset := parse_line (input_line ref_file) !computingset;
        done;      
      with End_of_file -> close_in ref_file
    with 
      Sys_error(str)    -> 
      Pcg.warning "Error opening file %s (%s)\n" filename str 
  with 
    (* no stack file  *)
    Not_found           ->
     Pcg.debug ~level:2 "No stack file set"

let compute_stack ((mf,mm,gf,gm) as prj) =
  parse_stack_size_file();
  parse_stack_call_file();
  let stack_size_of_fn (fn:string) =
    try
      StringMap.find fn !computingmap
    with
      Not_found ->
      Pcg.warning "Stack of %s unknown\n" fn;
      0
  in
  let rec max_stack_function str fn=
    let list_of_called_fn = 
      let subset = PairStringSet.filter (fun (x,_) -> 0 = String.compare x fn) (PairStringSet.union gf !computingset)
      in
      let ffold (a,b) p = 
        b :: p
      in
      PairStringSet.fold ffold subset []
    in
    let new_str = Printf.sprintf "%s -> %s (%d) " str fn (stack_size_of_fn fn) in
    Pcg.log "%s\n" new_str;
    (stack_size_of_fn fn) + (max_list (List.map (max_stack_function new_str) list_of_called_fn))
  in
  let fiter k f_elt =
    Pcg.debug "starting: %s\n" k ;
    Pcg.log "COMPUTED STACK FROM: %s : %d\n" k (max_stack_function "" k)
  in
  let func_to_analyse =
    if (CgStack_caller.get())
    then
      StringMap.filter (fun m _ -> not (PairStringSet.exists (fun (_,b) -> m=b) gf)) mf
    else
      mf;
  in
  StringMap.iter fiter func_to_analyse





let run () =

  let fcg_filename = FunctionCg.get()
  and mcg_filename = ModuleCg.get()
  and stack_filename = CgStack_filename.get()
  and comments_filename = CgComments_filename.get()
  in

    if (   ((String.length fcg_filename) >0)
        || ((String.length mcg_filename) >0)
        || ((String.length stack_filename) >0)
        || ((String.length comments_filename) >0)
        || (CgAll.get ())
        || (CommentOut.get ()))
    then
      begin
        let cil_type_file = Ast.get() in
        let prj =
          let prj=compute_prj ()
          in
            if (CgHead.get ())
            then
              prj
            else
              filter_header prj
        in
        if (CommentOut.get ())
        then
          (
            ignore (Visitor.visitFramacFile ((new c_globals_function):> Visitor.frama_c_visitor) (Ast.get ()));
            PairStringMap.iter (fun (m,f) (l,c) -> Printf.printf "%s;%s;%d;%d;%d\n" m f l c (c*100/l)) !m_function_comment_nb;
          );
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

          if ((String.length comments_filename)>0)
          then
            begin
              try
                let o = open_out comments_filename in
                  ignore (Visitor.visitFramacFile ((new c_globals_function):> Visitor.frama_c_visitor) (Ast.get ()));
                  Printf.fprintf o  "module;function;code+comments;comments; /100 of comments\n";
                  PairStringMap.iter (fun (m,f) (l,c) -> Printf.fprintf o "%s;%s;%d;%d;%d\n" m f l c (c*100/l)) !m_function_comment_nb;
                  close_out o
              with e ->
                Pcg.error
                  "error during output of comments count: %s >%s<"
                  (Printexc.to_string e) comments_filename
            end;

        if ((String.length stack_filename)>0)
        then
          compute_stack prj;

      end

let () = Db.Main.extend run

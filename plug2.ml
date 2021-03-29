open Cabs

let r_lines = ref []

class metricsCabsVisitor = object(self)
  inherit Cabsvisit.nopCabsVisitor

  method! vdef def =
    match def with
      | FUNDEF (_, sname, _, (l1,_), (l2,_)) ->
        begin
          let subarray = Array.sub (Array.of_list !r_lines) l1.pos_lnum (l2.pos_lnum - l1.pos_lnum +1)
          in
          let ffold n s =
            if (Str.string_match (Str.regexp "[a-zA-Z0-9 ;{}]+") s 0) then n+1 else n
          in
          let nb_nonempty_line = Array.fold_left ffold 0 subarray in
          Format.printf "%a %d, %a %d, total %d, diff %d\n" Filepath.Normalized.pp_abs l1.pos_path l1.pos_lnum Filepath.Normalized.pp_abs l2.pos_path l2.pos_lnum nb_nonempty_line (l2.pos_lnum - l1.pos_lnum -nb_nonempty_line +1);

          Cil.DoChildren
        end
      | _ -> Cil.DoChildren;


end
;;

let rec strech_list l n =
  if n=0
  then
    l
  else
    strech_list (List.tl l) (n-1)

let rec init_empty_list n =
  if n=0
  then
    []
  else
    "" :: (init_empty_list (n-1))

let run () =

    let cabs_files = Ast.UntypedFiles.get () in
    let cabs_visitor = new metricsCabsVisitor in
    List.iter (fun file ->
        (* 1- compute all lines *)
        begin
          let in_channel = open_in (Filepath.Normalized.to_pretty_string (fst file)) in
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
            (*r_lines := strech_list !r_lines !r_last_marker*)
          with End_of_file ->
            close_in in_channel;
        end;

        ignore
	(Cabsvisit.visitCabsFile (cabs_visitor:>Cabsvisit.cabsVisitor) file);

    ) cabs_files


let () = Db.Main.extend run

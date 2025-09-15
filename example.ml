(* Instructions to use example.ml: Run the two commands below. *)
(* ocamlfind ocamlc -package sexplib,ppx_sexp_conv -linkpkg -o example example.ml *)
(* ./example *)

open Sexplib.Std

(* user-defined type *)
type person = {
  name : string;
  age : int;
  hobbies : string list;
} [@@deriving sexp]

let () =
  (* Create a value of type person *)
  let p = { name = "Alice"; age = 30; hobbies = ["reading"; "cycling"] } in

  (* Convert the person to an S-expression *)
  let sexp = sexp_of_person p in
  Printf.printf "S-expression: %s\n" (Sexplib.Sexp.to_string_hum sexp);

  (* Convert the S-expression back to a person *)
  let p' = person_of_sexp sexp in
  Printf.printf "Name: %s, Age: %d\n" p'.name p'.age;
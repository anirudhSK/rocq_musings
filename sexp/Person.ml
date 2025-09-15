open Sexplib.Std
(* user-defined type *)
type person = {
  name : string;
  age : int;
  hobbies : string list;
} [@@deriving sexp]
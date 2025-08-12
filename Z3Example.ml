open Z3

let ctx = mk_context []

let example_1 () =
  (* Create integer variables x and y *)
  let int_sort = Arithmetic.Integer.mk_sort ctx in
  let x = Expr.mk_const_s ctx "x" int_sort in
  let y = Expr.mk_const_s ctx "y" int_sort in
  
  (* Create constants *)
  let zero = Arithmetic.Integer.mk_numeral_i ctx 0 in (* zero *)
  let eleven = Arithmetic.Integer.mk_numeral_i ctx 11 in (* eleven *)
  
  let x_gt_0 = Arithmetic.mk_gt ctx x zero in (* x > 0 *)
  let y_gt_0 = Arithmetic.mk_gt ctx y zero in (* y > 0 *)
  let sum = Arithmetic.mk_add ctx [x; y] in   (* sum = x + y *)
  let x_plus_y_eq_11 = Boolean.mk_eq ctx sum eleven in (* sum = 11 *)
  
  (* Create solver and add constraints *)
  let solver = Solver.mk_solver ctx None in
  Solver.add solver [x_gt_0; y_gt_0; x_plus_y_eq_11];
  
  (* Print the constraints *)
  Printf.printf "Constraints:\n";
  Printf.printf "x > 0: %s\n" (Expr.to_string x_gt_0);
  Printf.printf "y > 0: %s\n" (Expr.to_string y_gt_0);
  Printf.printf "x + y = 11: %s\n" (Expr.to_string x_plus_y_eq_11);

  (* Check satisfiability *)
  match Solver.check solver [] with
  | SATISFIABLE ->
    let model = Solver.get_model solver in
    (match model with
     | Some m ->
       Printf.printf "SAT\n";
       Printf.printf "x = %s\n" (Model.eval m x true |> Option.get |> Expr.to_string);
       Printf.printf "y = %s\n" (Model.eval m y true |> Option.get |> Expr.to_string)
     | None -> Printf.printf "No model\n")
  | UNSATISFIABLE ->
    Printf.printf "UNSAT\n"
  | UNKNOWN ->
    Printf.printf "UNKNOWN\n"

let () = example_1 ()
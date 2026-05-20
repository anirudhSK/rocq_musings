let () =
  let eq_test_stats = Stdlib.List.fold_left
    (fun (acc : int * int) (name, test) -> (
      let p, t = acc in
      Printf.printf "Running Test (%s)\n" name;
      let passed = test () in (
      Printf.printf "\027[1m%s\027[0m\n\n" (if passed = 1 then "\027[32mPASSED" else "\027[31mFAILED");
      (p + passed, t + 1)))) (0, 0) (Stdlib.List.rev !TestEquality.eq_tests) in

  let semantics_test_stats = Stdlib.List.fold_left
    (fun (acc : int * int) (name, test) -> (
      let p, t = acc in
      Printf.printf "Running Test (%s)\n" name;
      let passed = test () in (
      Printf.printf "\027[1m%s\027[0m\n\n" (if passed = 1 then "\027[32mPASSED" else "\027[31mFAILED");
      (p + passed, t + 1)))) (0, 0) (Stdlib.List.rev !TestSemantics.semantics_tests) in

  Printf.printf "┌ \027[1mTest Summary\027[0m -----------\n";

  Printf.printf "| Equality: %d/%d\n" (fst eq_test_stats) (snd eq_test_stats);
  Printf.printf "| Semantics: %d/%d\n" (fst semantics_test_stats) (snd semantics_test_stats);

  let n_pass = (fst eq_test_stats) + (fst semantics_test_stats) in
  let n = (snd eq_test_stats) + (snd semantics_test_stats) in
  let color_string = if n_pass <> n then "\027[31m" else "\027[32m" in
  Printf.printf "| Overall: \027[1m%s%d/%d\027[0m\n"
    color_string n_pass n;

  Printf.printf "└-------------------------\n";

  if (n_pass <> n) then exit 1 else exit 0

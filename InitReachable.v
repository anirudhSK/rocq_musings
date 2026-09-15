(* Which concrete initial states the equivalence results are about.

   [SmtModuleQuery]'s network lemmas are stated over
   [concretize_sym_modnet_state (init_general_symbolic_state pf p) f] -- the
   concretization of the initial symbolic state under a valuation.  That raises
   the obvious question: is that a thin slice of the concrete initial states, or
   all of the sensible ones?  This file answers it, by BUILDING the concrete
   initial states rather than describing them.

   The shape matters, and the obvious shape does not work.  A predicate listing
   sanity facts about a concrete state ("regions hold bytes, nothing has run
   yet") and a conclusion of [ci = concretize ... f] cannot be proved, because
   such a predicate can only speak POINTWISE about the maps in the state and
   [PMap] is not extensional: [PMap.set k v m] and [m] have the same [!!]
   everywhere when [v] is what [k] already read, and different trees.  Every
   concretization of an initial state has the EMPTY tree in [sh_mem_extent]
   (the seed is [PMap.init] and [PMap.map] is [PTree.map1], which preserves
   [Empty]), so a valid state with any other tree there is outside the image
   whatever the predicate says.

   So: parameterise the concrete initializer by the same free inputs the
   symbolic one has ([InitInputs]), prove the two agree on the nose
   ([init_concretize_eq]), and prove every choice of inputs is realized by some
   valuation ([inputs_realizable]).  Validity is then defined, not guessed:
   a valid initial state IS one the builder produces.

   The equality survives because concretization commutes with every fold shape
   the initializer uses -- [pmap_map_set] and friends below, which is where
   [PTree.extensionality] earns its keep.  That is worth more than it looks:
   the result is an equation, so it rewrites straight into
   [modnet_equivalence_checker_sound] without needing a congruence lemma for
   [eval_general_program_concrete]. *)

From MyProject Require Import CrVarLike CrIdentifiers CrModule CrDsl
     CrGeneralProgramState CrProgramState CrSymbolicSemanticsModule
     CrSymbolicSemanticsParser CrSymbolicSemanticsTransformer
     SmtExpr SmtTypes CrVal Maps MyInts Integers Coqlib.
From Stdlib Require Import List ZArith micromega.Lia.
From Stdlib.Strings Require Import String Ascii.
Import ListNotations.

Local Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* Strings: a literal prefix, and a binary numeral.                     *)

Fixpoint strip_prefix (pre s : string) : option string :=
  match pre, s with
  | EmptyString, _ => Some s
  | String c pre', String d s' =>
      if Ascii.eqb c d then strip_prefix pre' s' else None
  | String _ _, EmptyString => None
  end.

Lemma strip_prefix_app : forall pre s, strip_prefix pre (pre ++ s) = Some s.
Proof.
  induction pre as [| c pre IH]; intros s; cbn; [reflexivity |].
  rewrite Ascii.eqb_refl. apply IH.
Qed.

Lemma string_app_nil : forall s, (s ++ "")%string = s.
Proof. induction s as [| c s IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma string_app_assoc : forall a b c,
  ((a ++ b) ++ c)%string = (a ++ (b ++ c))%string.
Proof. induction a as [| x a IH]; cbn; intros; [reflexivity | rewrite IH; reflexivity]. Qed.

(* Parse a MAXIMAL binary numeral off the front and return what is left.  The
   accumulator is [None] until a digit is seen, which is what lets
   [pos_to_string]'s leading [1] -- always present, since the recursion bottoms
   out at [xH] -- seed it rather than shift into it. *)
Fixpoint parse_num (s : string) (acc : option positive) {struct s}
  : option (positive * string) :=
  match s with
  | EmptyString => match acc with Some a => Some (a, EmptyString) | None => None end
  | String c rest =>
      if Ascii.eqb c "0"%char then
        match acc with Some a => parse_num rest (Some (xO a)) | None => None end
      else if Ascii.eqb c "1"%char then
        match acc with
        | Some a => parse_num rest (Some (xI a))
        | None => parse_num rest (Some xH)
        end
      else match acc with Some a => Some (a, String c rest) | None => None end
  end.

Definition parse_num_at (s : string) : option (positive * string) := parse_num s None.

Definition digit_head (s : string) : bool :=
  match s with
  | String c _ => orb (Ascii.eqb c "0"%char) (Ascii.eqb c "1"%char)
  | EmptyString => false
  end.

(* [pos_to_string] appends on the RIGHT, so the induction threads the rest of
   the string through the accumulator. *)
Lemma parse_num_pos : forall p s,
  parse_num (pos_to_string p ++ s) None = parse_num s (Some p).
Proof.
  induction p as [q IH | q IH |]; intros s; cbn [pos_to_string].
  - rewrite string_app_assoc. cbn [String.append]. rewrite IH. reflexivity.
  - rewrite string_app_assoc. cbn [String.append]. rewrite IH. reflexivity.
  - cbn. reflexivity.
Qed.

Lemma parse_num_stop : forall p s,
  digit_head s = false -> parse_num_at (pos_to_string p ++ s) = Some (p, s).
Proof.
  intros p s Hd. unfold parse_num_at. rewrite parse_num_pos.
  destruct s as [| c rest]; cbn; [reflexivity |].
  cbn in Hd. apply Bool.orb_false_iff in Hd as [H0 H1]. rewrite H0, H1. reflexivity.
Qed.

Lemma parse_num_all : forall p, parse_num_at (pos_to_string p) = Some (p, EmptyString).
Proof.
  intro p. rewrite <- (string_app_nil (pos_to_string p)) at 1.
  apply parse_num_stop. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The inverse of [CrVarLike.seed_name].

   Its existence is the statement that the four families of seeded names are
   pairwise distinct and each injective -- which is what makes the four kinds
   of input independently choosable, and hence [inputs_realizable] true.  An
   input name never starts with [mod_mark], so the shared and module-local
   namespaces separate by computation, for EVERY program prefix. *)
Definition seed_parse (pf : string) (s : string) : option SeedVar :=
  match strip_prefix "hdr_" s with
  | Some r =>
      match parse_num_at r with
      | Some (h, EmptyString) => Some (SVHdr h)
      | _ => None
      end
  | None =>
  match strip_prefix "pkt_" s with
  | Some r =>
      match parse_num_at r with
      | Some (i, EmptyString) => Some (SVPkt i)
      | _ => None
      end
  | None =>
  match strip_prefix (mod_mark ++ pf ++ "_m") s with
  | Some r0 =>
      match parse_num_at r0 with
      | Some (m, r1) =>
          match strip_prefix "_" r1 with
          | Some r2 =>
              match strip_prefix "ctrl_" r2 with
              | Some r3 =>
                  match parse_num_at r3 with
                  | Some (v, EmptyString) => Some (SVCtrl m v)
                  | _ => None
                  end
              | None =>
                  match strip_prefix "state_" r2 with
                  | Some r3 =>
                      match parse_num_at r3 with
                      | Some (v, EmptyString) => Some (SVState m v)
                      | _ => None
                      end
                  | None => None
                  end
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end end end.

Lemma seed_name_mod_shape : forall pf m tag v,
  (get_mod_prefix pf (ModuleNameCtr m) ++ tag ++ pos_to_string v)
  = (mod_mark ++ pf ++ "_m") ++ (pos_to_string m ++ ("_" ++ (tag ++ pos_to_string v))).
Proof.
  intros pf m tag v. unfold get_mod_prefix. cbn [unwrap Posesque_ModuleName].
  rewrite !string_app_assoc. reflexivity.
Qed.

(* The branches that must MISS, each by computation on the leading character. *)
Lemma strip_hdr_pkt : forall s, strip_prefix "hdr_" ("pkt_" ++ s) = None.
Proof. reflexivity. Qed.

Lemma strip_hdr_modname : forall pf mid s,
  strip_prefix "hdr_" (get_mod_prefix pf mid ++ s) = None.
Proof. reflexivity. Qed.

Lemma strip_pkt_modname : forall pf mid s,
  strip_prefix "pkt_" (get_mod_prefix pf mid ++ s) = None.
Proof. reflexivity. Qed.

Lemma strip_ctrl_state : forall s, strip_prefix "ctrl_" ("state_" ++ s) = None.
Proof. reflexivity. Qed.

Lemma seed_parse_name : forall pf x, seed_parse pf (seed_name pf x) = Some x.
Proof.
  intros pf [h | i | m v | m v]; unfold seed_parse, seed_name.
  - rewrite (strip_prefix_app "hdr_"), parse_num_all. reflexivity.
  - rewrite strip_hdr_pkt, (strip_prefix_app "pkt_"), parse_num_all. reflexivity.
  - rewrite strip_hdr_modname, strip_pkt_modname, seed_name_mod_shape.
    rewrite (strip_prefix_app (mod_mark ++ pf ++ "_m")).
    rewrite (parse_num_stop m) by reflexivity.
    rewrite (strip_prefix_app "_"), (strip_prefix_app "ctrl_"), parse_num_all.
    reflexivity.
  - rewrite strip_hdr_modname, strip_pkt_modname, seed_name_mod_shape.
    rewrite (strip_prefix_app (mod_mark ++ pf ++ "_m")).
    rewrite (parse_num_stop m) by reflexivity.
    rewrite (strip_prefix_app "_"), strip_ctrl_state.
    rewrite (strip_prefix_app "state_"), parse_num_all.
    reflexivity.
Qed.

(* [region_name] lives in [sv_arrs], a namespace of its own, so it needs only
   to be injective in itself. *)
Definition region_parse (s : string) : option positive :=
  match strip_prefix "mem_" s with
  | Some r => match parse_num_at r with
              | Some (k, EmptyString) => Some k
              | _ => None
              end
  | None => None
  end.

Lemma region_parse_name : forall k, region_parse (region_name k) = Some k.
Proof.
  intro k. unfold region_parse, region_name.
  rewrite strip_prefix_app, parse_num_all. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Concretization commutes with the folds the initializer is built from.

   This is what keeps the conclusion an EQUATION rather than a pointwise
   agreement, and it is the one place [PTree.extensionality] is doing real
   work: [PTree.map1] and [PTree.set] commute because the two sides agree at
   every index, which for the canonical tree is enough to make them the same
   tree. *)

Lemma ptree_map1_set : forall (A B : Type) (g : A -> B) k v (m : PTree.t A),
  PTree.map1 g (PTree.set k v m) = PTree.set k (g v) (PTree.map1 g m).
Proof.
  intros A B g k v m. apply PTree.extensionality. intros i.
  rewrite PTree.gmap1, !PTree.gsspec, PTree.gmap1.
  destruct (Coqlib.peq i k); reflexivity.
Qed.

Lemma pmap_map_set : forall (A B : Type) (g : A -> B) k v (m : PMap.t A),
  PMap.map g (PMap.set k v m) = PMap.set k (g v) (PMap.map g m).
Proof.
  intros A B g k v m. unfold PMap.map, PMap.set. cbn.
  rewrite ptree_map1_set. reflexivity.
Qed.

Lemma pmap_map_fold : forall (A B C : Type) (g : A -> B)
    (key : C -> positive) (val : C -> A) (l : list C) (m : PMap.t A),
  PMap.map g (List.fold_left (fun acc c => PMap.set (key c) (val c) acc) l m)
  = List.fold_left (fun acc c => PMap.set (key c) (g (val c)) acc) l (PMap.map g m).
Proof.
  intros A B C g key val l. induction l as [| c r IH]; intros m; [reflexivity |].
  cbn [List.fold_left]. rewrite IH, pmap_map_set. reflexivity.
Qed.

Lemma pmap_fold_ext : forall (A C : Type) (key : C -> positive) (v1 v2 : C -> A)
    (l : list C) (m : PMap.t A),
  (forall c, v1 c = v2 c) ->
  List.fold_left (fun acc c => PMap.set (key c) (v1 c) acc) l m
  = List.fold_left (fun acc c => PMap.set (key c) (v2 c) acc) l m.
Proof.
  intros A C key v1 v2 l. induction l as [| c r IH]; intros m Hv; [reflexivity |].
  cbn [List.fold_left]. rewrite Hv. apply IH. exact Hv.
Qed.

(* [force_keys] re-reads its accumulator, so this needs [PMap.gmap] as well. *)
Lemma pmap_map_force : forall (A B : Type) (g : A -> B) (ks : list positive) (m : PMap.t A),
  PMap.map g (force_keys ks m) = force_keys ks (PMap.map g m).
Proof.
  intros A B g ks. unfold force_keys. induction ks as [| k r IH]; intros m; [reflexivity |].
  cbn [List.fold_left]. rewrite IH, pmap_map_set, PMap.gmap. reflexivity.
Qed.

Lemma ptree_map1_fold : forall (A B : Type) (g : A -> B) (l : list (positive * A)) m,
  PTree.map1 g (List.fold_left (fun acc kv => PTree.set (fst kv) (snd kv) acc) l m)
  = List.fold_left (fun acc kv => PTree.set (fst kv) (snd kv) acc)
      (List.map (fun kv => (fst kv, g (snd kv))) l) (PTree.map1 g m).
Proof.
  intros A B g l. induction l as [| kv r IH]; intros m; [reflexivity |].
  cbn [List.fold_left List.map fst snd]. rewrite IH, ptree_map1_set. reflexivity.
Qed.

Lemma ptree_map1_of_list : forall (A B : Type) (g : A -> B) (l : list (positive * A)),
  PTree.map1 g (PTree_Properties.of_list l)
  = PTree_Properties.of_list (List.map (fun kv => (fst kv, g (snd kv))) l).
Proof.
  intros A B g l. unfold PTree_Properties.of_list. apply ptree_map1_fold.
Qed.

(* A [PMap] built as (default, of_list), which is how a transformer's ctrl and
   state maps are seeded. *)
Lemma pmap_map_of_list : forall (A B : Type) (g : A -> B) (d : A) (l : list (positive * A)),
  PMap.map g (d, PTree_Properties.of_list l)
  = (g d, PTree_Properties.of_list (List.map (fun kv => (fst kv, g (snd kv))) l)).
Proof.
  intros A B g d l. unfold PMap.map. cbn. rewrite ptree_map1_of_list. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The free inputs of an initial state.

   Five families, matching [SeedVar] plus the regions.  A run of the network
   is a function of the program and these; everything else about an initial
   state is fixed. *)
Record InitInputs : Type := {
  ii_hdr   : positive -> CrVal;               (* an extracted header's entry value *)
  ii_pkt   : positive -> CrVal;               (* one input packet bit *)
  ii_mem   : positive -> @Array CrVal;        (* a region's contents on entry *)
  ii_ctrl  : positive -> positive -> CrVal;   (* module -> ctrl config entry *)
  ii_state : positive -> positive -> CrVal;   (* module -> state variable *)
}.

(* Each input is RAW -- whatever the solver's constant holds -- and the builder
   applies the normalizer, which is the same one the symbolic side applies.
   That is what makes the two halves below exact rather than approximate: the
   set of values an input can actually take is not a constraint anyone has to
   state, it is a consequence of the normalizer.

   [as_int]: [eval_smt_arith]'s [SmtArithVar] arm folds every non-integer into
   [ErrorVal], so [UninitVal] is NOT reachable at a seeded variable.
   [as_bit]: a symbolic packet bit is an integer read as nonzero/zero.
   A header goes through [val_of] then [mk_int ty], so a header register holds
   exactly the values [mk_int ty z]; a region through [region_of_bytes], so it
   has the declared length and holds bytes. *)
Definition as_int (v : CrVal) : CrVal :=
  match v with IntVal a t => IntVal a t | _ => ErrorVal end.

Definition as_bit (v : CrVal) : bool :=
  match v with IntVal a _ => negb (Integers.eq a Integers.zero) | _ => false end.

Definition seed_header_conc (hts : list (Header * CrIntType)) (hs : list Header)
    (ii : InitInputs) : PMap.t CrVal :=
  List.fold_left
    (fun acc h =>
       PMap.set (unwrap h)
         (match lookup_header_type hts h with
          | Some ty => mk_int ty (val_of (ii_hdr ii (unwrap h)))
          | None => UninitVal
          end) acc)
    hs (PMap.init UninitVal).

(* [region_of_bytes] is the normalizer here: it forces the declared length and
   sends every cell through [CrVal.to_byte].  So the input is an arbitrary
   array and the builder makes it a region of bytes -- which is exactly what a
   free [SmtArrVar] denotes. *)
Definition init_conc_mem (rs : list MemRegionDecl) (ii : InitInputs)
    : PMap.t (@Array CrVal) :=
  List.fold_left
    (fun acc d =>
       PMap.set (unwrap (mr_id d))
         (region_of_bytes (repr (Z.of_nat (mr_len d))) (ii_mem ii (unwrap (mr_id d)))) acc)
    rs (PMap.init (@Unallocated CrVal)).

Definition empty_concrete_parser_state : ConcreteParserState :=
  {| p_header_map := PMap.init UninitVal;
     p_packet := @nil bool;
     p_cursor := 0 |}.

Definition empty_concrete_mod : ConcreteModuleState :=
  TransformerMod {| t_ctrl_map := PMap.init UninitVal;
                    t_header_map := PMap.init UninitVal;
                    t_state_map := PMap.init UninitVal |}.

Definition init_conc_mod_state (ii : InitInputs) (m : CrModule) : ConcreteModuleState :=
  match m with
  | ParserModule _ _ => ParserMod empty_concrete_parser_state
  | DeparserModule _ _ => DeparserMod empty_concrete_parser_state
  | TransformerModule _ s c _ =>
      TransformerMod {|
        t_ctrl_map := (UninitVal, PTree_Properties.of_list
          (List.map (fun x => let x' := unwrap x in
                              (x', as_int (ii_ctrl ii (unwrap (get_mod_name m)) x'))) c));
        t_header_map := PMap.init UninitVal;
        t_state_map := force_keys
          (List.map unwrap (collect_module_state_targets m))
          (UninitVal, PTree_Properties.of_list
            (List.map (fun x => let x' := unwrap x in
                                (x', as_int (ii_state ii (unwrap (get_mod_name m)) x'))) s));
      |}
  end.

(* The concrete initial state determined by a program and a choice of inputs.
   [CrVarLike.init_general_concrete_state] is the all-zero case of this. *)
Definition init_general_concrete_state_with
    (p : GeneralCaracaraProgram) (ii : InitInputs) : GeneralConcreteState :=
  {| sh_hdr_map :=
       let mods := net_modules (get_network_from_general p) in
       seed_header_conc (collect_header_types mods) (collect_write_headers mods) ii;
     sh_read_tape := List.map (fun i => as_bit (ii_pkt ii (Pos.of_succ_nat i)))
                              (List.seq 0 (get_inp_len_from_general p));
     sh_bits_read := mk_int u64 0;
     sh_write_tape := @nil bool;
     sh_mem := init_conc_mem (get_mem_regions_from_general p) ii;
     sh_mem_extent := PMap.init (mk_int u64 0);
     mod_states := List.fold_left
       (fun acc m => PMap.set (unwrap (get_mod_name m)) (init_conc_mod_state ii m) acc)
       (net_modules (get_network_from_general p))
       (PMap.init empty_concrete_mod);
     gps_valid := true |}.

(* What a valuation says about each input. *)
Definition inputs_of (pf : string) (f : SmtValuation) : InitInputs :=
  {| ii_hdr   := fun h => sv_ints f (seed_name "" (SVHdr h));
     ii_pkt   := fun i => sv_ints f (seed_name "" (SVPkt i));
     ii_mem   := fun k => sv_arrs f (region_name k);
     ii_ctrl  := fun m v => sv_ints f (seed_name pf (SVCtrl m v));
     ii_state := fun m v => sv_ints f (seed_name pf (SVState m v)) |}.

(* ------------------------------------------------------------------ *)
(* Adequacy: every concretization of the initial symbolic state IS a builder
   state, on the nose.                                                   *)

Lemma seed_header_adequate : forall hts hs pf f,
  PMap.map (fun e => eval_smt_arith e f) (seed_header_syms hts hs)
  = seed_header_conc hts hs (inputs_of pf f).
Proof.
  intros hts hs pf f. unfold seed_header_syms, seed_header_conc.
  rewrite pmap_map_fold. apply pmap_fold_ext. intros h.
  destruct (lookup_header_type hts h) as [ty |]; [| reflexivity].
  cbn [eval_smt_arith]. apply cast_u64_mk_int.
Qed.

Lemma init_mem_adequate : forall rs pf f,
  PMap.map (fun a => eval_smt_mem a f) (init_symbolic_mem rs)
  = init_conc_mem rs (inputs_of pf f).
Proof.
  intros rs pf f. unfold init_symbolic_mem, init_conc_mem. cbv zeta.
  rewrite pmap_map_fold. apply pmap_fold_ext. intros d. reflexivity.
Qed.

Lemma present_bits_all : forall l f,
  (forall b, In b l -> eval_smt_bool (cvc b) f = true) ->
  present_bits l f = List.map (fun b => eval_smt_bool (cvv b) f) l.
Proof.
  intros l f H. unfold present_bits. f_equal.
  induction l as [| b r IH]; cbn [List.filter]; [reflexivity |].
  rewrite (H b) by (left; reflexivity).
  rewrite IH by (intros x Hx; apply H; right; exact Hx). reflexivity.
Qed.

Lemma read_tape_adequate : forall n pf f,
  present_bits (symbolic_input_bits n) f
  = List.map (fun i => as_bit (ii_pkt (inputs_of pf f) (Pos.of_succ_nat i)))
             (List.seq 0 n).
Proof.
  intros n pf f. unfold symbolic_input_bits.
  rewrite present_bits_all
    by (intros b Hb; apply in_map_iff in Hb as [i [Hi _]]; subst b; reflexivity).
  rewrite map_map. reflexivity.
Qed.

(* [program_state_mapper] is [Global Opaque], so its defining equation has to be
   named rather than unfolded. *)
Lemma program_state_mapper_eq : forall (T1 T2 : Type) (fc fh fs : T1 -> T2) s,
  program_state_mapper fc fh fs s =
  {| t_ctrl_map := PMap.map fc (t_ctrl_map s);
     t_header_map := PMap.map fh (t_header_map s);
     t_state_map := PMap.map fs (t_state_map s) |}.
Proof. reflexivity. Qed.

Lemma mod_state_adequate : forall pf f m,
  concretize_sym_module_state (init_sym_mod_state pf m) f
  = init_conc_mod_state (inputs_of pf f) m.
Proof.
  intros pf f m. destruct m as [mid ps | mid ps | mid s c t];
    unfold init_sym_mod_state, init_conc_mod_state; cbv zeta.
  - reflexivity.
  - reflexivity.
  - cbn [concretize_sym_module_state].
    unfold eval_sym_state. cbv zeta. rewrite program_state_mapper_eq.
    cbn [t_ctrl_map t_header_map t_state_map].
    rewrite pmap_map_force, !pmap_map_of_list, !map_map. reflexivity.
Qed.

Lemma mod_states_adequate : forall pf f mods,
  PMap.map (fun sym_st => concretize_sym_module_state sym_st f)
    (List.fold_left
       (fun acc m => PMap.set (unwrap (get_mod_name m)) (init_sym_mod_state pf m) acc)
       mods (PMap.init empty_transformer_mod))
  = List.fold_left
      (fun acc m => PMap.set (unwrap (get_mod_name m)) (init_conc_mod_state (inputs_of pf f) m) acc)
      mods (PMap.init empty_concrete_mod).
Proof.
  intros pf f mods. rewrite pmap_map_fold. apply pmap_fold_ext.
  intros m. apply mod_state_adequate.
Qed.

Theorem init_concretize_eq : forall p pf f,
  concretize_sym_modnet_state (init_general_symbolic_state pf p) f
  = init_general_concrete_state_with p (inputs_of pf f).
Proof.
  intros p pf f.
  unfold concretize_sym_modnet_state, init_general_concrete_state_with,
         init_general_symbolic_state.
  cbn [sh_hdr_map sh_read_tape sh_bits_read sh_write_tape sh_mem sh_mem_extent
       mod_states gps_valid cvv].
  cbv zeta. f_equal.
  - apply seed_header_adequate.
  - apply read_tape_adequate.
  - apply init_mem_adequate.
  - apply mod_states_adequate.
Qed.

(* ------------------------------------------------------------------ *)
(* Realizability: every choice of inputs is realized by some valuation.

   This is where [seed_parse_name] earns its place.  Building the valuation
   means answering for EVERY name at once, and answering correctly at a header
   name without disturbing a packet bit or a module's ctrl entry is exactly the
   claim that the four families of names are distinct. *)

Definition seed_valuation (pf : string) (ii : InitInputs) : SmtValuation :=
  {| sv_ints := fun s =>
       match seed_parse pf s with
       | Some (SVHdr h)    => ii_hdr ii h
       | Some (SVPkt i)    => ii_pkt ii i
       | Some (SVCtrl m v) => ii_ctrl ii m v
       | Some (SVState m v) => ii_state ii m v
       | None => ErrorVal
       end;
     sv_arrs := fun s =>
       match region_parse s with
       | Some k => ii_mem ii k
       | None => @Unallocated CrVal
       end |}.

Definition ii_agree (i1 i2 : InitInputs) : Prop :=
  (forall h, ii_hdr i1 h = ii_hdr i2 h)
  /\ (forall i, ii_pkt i1 i = ii_pkt i2 i)
  /\ (forall k, ii_mem i1 k = ii_mem i2 k)
  /\ (forall m v, ii_ctrl i1 m v = ii_ctrl i2 m v)
  /\ (forall m v, ii_state i1 m v = ii_state i2 m v).

(* The builder reads each input at finitely many keys, so it cannot tell apart
   two input assignments that agree pointwise.  Stating realizability this way
   is what keeps functional extensionality out of the development. *)
Lemma init_with_ext : forall p i1 i2,
  ii_agree i1 i2 ->
  init_general_concrete_state_with p i1 = init_general_concrete_state_with p i2.
Proof.
  intros p i1 i2 [Hh [Hp [Hm [Hc Hs]]]].
  unfold init_general_concrete_state_with. cbv zeta. f_equal.
  - unfold seed_header_conc. apply pmap_fold_ext. intros h.
    destruct (lookup_header_type _ h); [rewrite Hh |]; reflexivity.
  - apply map_ext. intros i. rewrite Hp. reflexivity.
  - unfold init_conc_mem. apply pmap_fold_ext. intros d. rewrite Hm. reflexivity.
  - apply pmap_fold_ext. intros m. unfold init_conc_mod_state.
    destruct m as [mid ps | mid ps | mid st c t]; try reflexivity.
    f_equal. f_equal.
    + f_equal. f_equal. apply map_ext. intros x. rewrite Hc. reflexivity.
    + f_equal. f_equal. f_equal. apply map_ext. intros x. rewrite Hs. reflexivity.
Qed.

(* A header register and a packet bit are shared inputs: their names carry no
   program prefix, so reading them does not depend on which program's prefix
   the parser was given. *)
Lemma seed_name_hdr_pf : forall pf h, seed_name "" (SVHdr h) = seed_name pf (SVHdr h).
Proof. reflexivity. Qed.

Lemma seed_name_pkt_pf : forall pf i, seed_name "" (SVPkt i) = seed_name pf (SVPkt i).
Proof. reflexivity. Qed.

Lemma seed_valuation_inputs : forall pf ii,
  ii_agree (inputs_of pf (seed_valuation pf ii)) ii.
Proof.
  intros pf ii. unfold ii_agree, inputs_of, seed_valuation.
  cbn [ii_hdr ii_pkt ii_mem ii_ctrl ii_state sv_ints sv_arrs].
  refine (conj _ (conj _ (conj _ (conj _ _)))); intros.
  - rewrite (seed_name_hdr_pf pf), seed_parse_name. reflexivity.
  - rewrite (seed_name_pkt_pf pf), seed_parse_name. reflexivity.
  - rewrite region_parse_name. reflexivity.
  - rewrite seed_parse_name. reflexivity.
  - rewrite seed_parse_name. reflexivity.
Qed.

Theorem inputs_realizable : forall p pf ii,
  init_general_concrete_state_with p ii
  = concretize_sym_modnet_state (init_general_symbolic_state pf p) (seed_valuation pf ii).
Proof.
  intros p pf ii. rewrite init_concretize_eq. symmetry.
  apply init_with_ext, seed_valuation_inputs.
Qed.

(* ------------------------------------------------------------------ *)
(* What the file exists for.                                            *)

(* A concrete initial state is VALID when it is one the initializer produces
   for some choice of inputs.  Defined rather than guessed -- see the header
   comment for why a predicate listing sanity facts cannot do this job. *)
Definition concrete_gp_state_valid
    (p : GeneralCaracaraProgram) (ci : GeneralConcreteState) : Prop :=
  exists ii, ci = init_general_concrete_state_with p ii.

Theorem valid_is_reachable : forall p pf ci,
  concrete_gp_state_valid p ci ->
  exists f, ci = concretize_sym_modnet_state (init_general_symbolic_state pf p) f.
Proof.
  intros p pf ci [ii ->]. exists (seed_valuation pf ii). apply inputs_realizable.
Qed.

(* And the converse, which is [init_concretize_eq] read the other way: the
   states the network lemmas quantify over are exactly the valid ones, no more
   and no fewer. *)
Theorem reachable_is_valid : forall p pf f,
  concrete_gp_state_valid p (concretize_sym_modnet_state (init_general_symbolic_state pf p) f).
Proof.
  intros p pf f. exists (inputs_of pf f). apply init_concretize_eq.
Qed.

Theorem valid_iff_reachable : forall p pf ci,
  concrete_gp_state_valid p ci
  <-> exists f, ci = concretize_sym_modnet_state (init_general_symbolic_state pf p) f.
Proof.
  intros p pf ci. split.
  - apply valid_is_reachable.
  - intros [f ->]. apply reachable_is_valid.
Qed.

(* ------------------------------------------------------------------ *)
(* Two programs at once.

   [modnet_equivalence_checker_sound] quantifies over ONE valuation and both
   programs' initial states, which is the formal content of "the two programs
   are compared on the same input".  So the usable form of reachability is a
   pair: given inputs for each, one valuation realizing both.  It needs the two
   halves to agree on the SHARED inputs -- a header register, a packet bit, a
   region -- which is not a technicality but the statement itself, and it needs
   the two prefixes to name different module-local variables. *)

Definition seed_valuation2 (pf1 pf2 : string) (ii1 ii2 : InitInputs) : SmtValuation :=
  {| sv_ints := fun s =>
       match seed_parse pf1 s with
       | Some (SVHdr h)    => ii_hdr ii1 h
       | Some (SVPkt i)    => ii_pkt ii1 i
       | Some (SVCtrl m v) => ii_ctrl ii1 m v
       | Some (SVState m v) => ii_state ii1 m v
       | None =>
           match seed_parse pf2 s with
           | Some (SVCtrl m v) => ii_ctrl ii2 m v
           | Some (SVState m v) => ii_state ii2 m v
           | _ => ErrorVal
           end
       end;
     sv_arrs := fun s =>
       match region_parse s with
       | Some k => ii_mem ii1 k
       | None => @Unallocated CrVal
       end |}.

(* One prefix's module-local names are not the other's.  This is a property of
   the two prefixes, and for the ones the checker uses it holds by computation:
   [seed_parse] fails inside the literal part of the name, before it reaches
   anything variable. *)
Definition prefixes_disjoint (pf1 pf2 : string) : Prop :=
  (forall m v, seed_parse pf1 (seed_name pf2 (SVCtrl m v)) = None)
  /\ (forall m v, seed_parse pf1 (seed_name pf2 (SVState m v)) = None).

Lemma prefixes_disjoint_p1_p2 : prefixes_disjoint "p1" "p2".
Proof. split; intros m v; reflexivity. Qed.

Theorem valid_is_reachable_pair : forall p1 p2 pf1 pf2 ii1 ii2,
  prefixes_disjoint pf1 pf2 ->
  (forall h, ii_hdr ii1 h = ii_hdr ii2 h) ->
  (forall i, ii_pkt ii1 i = ii_pkt ii2 i) ->
  (forall k, ii_mem ii1 k = ii_mem ii2 k) ->
  exists f,
    init_general_concrete_state_with p1 ii1
      = concretize_sym_modnet_state (init_general_symbolic_state pf1 p1) f
    /\ init_general_concrete_state_with p2 ii2
      = concretize_sym_modnet_state (init_general_symbolic_state pf2 p2) f.
Proof.
  intros p1 p2 pf1 pf2 ii1 ii2 [Hc2 Hs2] Hh Hp Hm.
  exists (seed_valuation2 pf1 pf2 ii1 ii2). split.
  - rewrite init_concretize_eq. symmetry. apply init_with_ext.
    unfold ii_agree, inputs_of, seed_valuation2.
    cbn [ii_hdr ii_pkt ii_mem ii_ctrl ii_state sv_ints sv_arrs].
    refine (conj _ (conj _ (conj _ (conj _ _)))); intros.
    + rewrite (seed_name_hdr_pf pf1), seed_parse_name. reflexivity.
    + rewrite (seed_name_pkt_pf pf1), seed_parse_name. reflexivity.
    + rewrite region_parse_name. reflexivity.
    + rewrite seed_parse_name. reflexivity.
    + rewrite seed_parse_name. reflexivity.
  - rewrite init_concretize_eq. symmetry. apply init_with_ext.
    unfold ii_agree, inputs_of, seed_valuation2.
    cbn [ii_hdr ii_pkt ii_mem ii_ctrl ii_state sv_ints sv_arrs].
    refine (conj _ (conj _ (conj _ (conj _ _)))); intros.
    + rewrite (seed_name_hdr_pf pf1), seed_parse_name. apply Hh.
    + rewrite (seed_name_pkt_pf pf1), seed_parse_name. apply Hp.
    + rewrite region_parse_name. apply Hm.
    + rewrite Hc2, seed_parse_name. reflexivity.
    + rewrite Hs2, seed_parse_name. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* What the old sanity predicate asserted, now derived.

   [SmtModuleQuery.concrete_gp_state_is_valid] used to be a list of facts about
   a concrete state -- nothing emitted, nothing consumed, regions holding
   bytes -- asserted as a hypothesis.  Each is now a property of every state
   the builder produces, which is the point of defining validity by
   construction: the facts come out rather than going in. *)

Lemma valid_gps_valid : forall p ii,
  gps_valid (init_general_concrete_state_with p ii) = true.
Proof. reflexivity. Qed.

Lemma valid_write_tape : forall p ii,
  sh_write_tape (init_general_concrete_state_with p ii) = @nil bool.
Proof. reflexivity. Qed.

Lemma valid_bits_read : forall p ii,
  sh_bits_read (init_general_concrete_state_with p ii) = mk_int u64 0.
Proof. reflexivity. Qed.

Lemma valid_extent_zero : forall p ii k,
  (sh_mem_extent (init_general_concrete_state_with p ii)) !! k = mk_int u64 0.
Proof. reflexivity. Qed.

Lemma valid_read_tape_len : forall p ii,
  List.length (sh_read_tape (init_general_concrete_state_with p ii))
  = get_inp_len_from_general p.
Proof.
  intros p ii. cbn [sh_read_tape init_general_concrete_state_with].
  rewrite map_length, seq_length. reflexivity.
Qed.

(* A region's contents on entry are BYTES.  This was the clause that mattered
   most and the one hardest to state honestly: [region_of_bytes] puts every
   cell through [CrVal.to_byte], so it holds of the raw input whatever it is. *)
Lemma to_byte_is_byte : forall c, exists z, to_byte c = Init (mk_int u8 z).
Proof.
  intros [[b [w] | | ] | ].
  - destruct w; [exists (unsigned b) | exists 0%Z | exists 0%Z | exists 0%Z]; reflexivity.
  - exists 0%Z. reflexivity.
  - exists 0%Z. reflexivity.
  - exists 0%Z. reflexivity.
Qed.

Lemma region_of_bytes_byte : forall len a i v,
  ld_arr (region_of_bytes len a) i = Legal v -> exists z, v = mk_int u8 z.
Proof.
  intros len a i v H. unfold region_of_bytes, ld_arr in H.
  destruct i as [idx ity | | ]; try discriminate.
  cbn [arr_len arr_bytes] in H.
  destruct (Integers.ltu idx len); [| discriminate].
  rewrite PMap.gmap in H.
  destruct (to_byte_is_byte ((region_bytes a) !! (offset_to_key idx))) as [z Hz].
  rewrite Hz in H. inversion H. exists z. reflexivity.
Qed.

(* Every entry of the region map is either undeclared or a region of bytes;
   there is no third possibility, whatever the inputs are. *)
Lemma init_conc_mem_entries : forall rs ii k m,
  (m !! k = Unallocated \/ exists len a, m !! k = region_of_bytes len a) ->
  ((List.fold_left
      (fun acc d =>
         PMap.set (unwrap (mr_id d))
           (region_of_bytes (repr (Z.of_nat (mr_len d))) (ii_mem ii (unwrap (mr_id d)))) acc)
      rs m) !! k = Unallocated)
  \/ exists len a,
      (List.fold_left
        (fun acc d =>
           PMap.set (unwrap (mr_id d))
             (region_of_bytes (repr (Z.of_nat (mr_len d))) (ii_mem ii (unwrap (mr_id d)))) acc)
        rs m) !! k = region_of_bytes len a.
Proof.
  intros rs ii k. induction rs as [| d r IH]; intros m Hm; cbn [List.fold_left];
    [exact Hm |].
  apply IH. rewrite PMap.gsspec. destruct (Coqlib.peq k (unwrap (mr_id d))).
  - right. eexists. eexists. reflexivity.
  - exact Hm.
Qed.

Lemma valid_regions_hold_bytes : forall p ii k i v,
  ld_arr ((sh_mem (init_general_concrete_state_with p ii)) !! k) i = Legal v ->
  exists z, v = mk_int u8 z.
Proof.
  intros p ii k i v H.
  cbn [sh_mem init_general_concrete_state_with] in H.
  unfold init_conc_mem in H.
  destruct (init_conc_mem_entries (get_mem_regions_from_general p) ii k
              (PMap.init (@Unallocated CrVal)) (or_introl (PMap.gi _ _)))
    as [Hu | [len [a Ha]]].
  - rewrite Hu in H. cbn in H. discriminate.
  - rewrite Ha in H. exact (region_of_bytes_byte _ _ _ _ H).
Qed.

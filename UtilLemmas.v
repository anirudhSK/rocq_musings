Lemma not_none_is_some : forall {A : Type} (y : option A),
  y <> None -> exists x, y = Some x.
Proof.
  intros A y H.
  destruct y as [x|].
  - exists x. reflexivity.
  - exfalso. apply H. reflexivity.
Qed.

(* This is what I am going to call the Joe subtlety in honor of
   https://gist.github.com/jtassarotti/57f65712869af462a01b46b660e0d92d 
   This is the buggy lemma here:
   Lemma some_is_not_none : forall {A : Type} (y : option A),
       exists x, y = Some x -> y <> None.
   Btw, as of Aug 4, 2025, Copilot points this out *)
Lemma some_is_not_none : forall {A : Type} (y : option A) (x: A),
  y = Some x -> y <> None.
Proof.
  intros A y x H.
  rewrite H.
  discriminate.
Qed.
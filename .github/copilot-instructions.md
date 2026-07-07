All Rocq/Coq files have been cleanly compiled before being pushed, so they are known to typecheck and close all goals.

Do NOT comment on proof bodies (the tactic scripts between Proof. and Qed./Defined.). Specifically, do not speculate about whether a proof is complete, whether a tactic will succeed, whether a goal remains open, or suggest alternative tactics for _correctness_ reasons.

Of course, although the proof body is known to be correct, it is possible for a) the proof to be inefficient, b) the proof statement to have a hole in it. But for the most part, focus your review on all the code changes made outside of the proof body itself.
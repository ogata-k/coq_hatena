(* この中はコメント。 file: hello_world.v
  The Coq Proof Assistant, version 8.11.0 (January 2020)
  compiled on Jan 24 2020 22:35:23 with OCaml 4.07.1
*)

Theorem AA: forall A: Prop, A -> A.
Proof.
  intros A a.
  exact a.
Qed.

(* AAがどういうのか見てみる *)
Print AA.
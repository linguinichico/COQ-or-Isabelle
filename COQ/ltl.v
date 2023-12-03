Section LTL.

Set Implicit Arguments.
Unset Strict Implicit.

(* =================== INTERPRETATIONS ================= *)

  Variables (state: Set) (initial_state : state -> Prop).

  CoInductive stream : Set :=
    occ : state -> stream -> stream.

  Definition head_str (s : stream) : state :=
    match s with
    | occ a _ => a
    end.
  
  Definition tl_str (s: stream) : stream :=
    match s with
    | occ _ s0 => s0
    end.

  Definition stream_formula := stream -> Prop.

  Definition and_ltl (P1 P2 : stream_formula) : stream_formula :=
  fun s => P1 s /\ P2 s.

  Definition or_ltl (P1 P2: stream_formula) : stream_formula :=  
  fun s => P1 s \/ P2 s.

  Definition not_ltl (P: stream_formula) : stream_formula :=
  fun s => ~ (P s).

  Definition true_ltl (s:stream) : Prop := True.

  Definition false_ltl (s:stream) : Prop := False.

(*  Inductive true_ltl (s:stream) : Prop :=
    | true_intro : forall (P:stream_formula), P s \/ ~P s -> true_ltl s.
  
  Definition false_ltl (s: stream) : Prop := ~ (true_ltl s). *)

  Notation " 't' " := (true_ltl) (at level 99).
  Notation "P1 '/l\' P2" := (and_ltl P1 P2) (at level 100).
  Notation "P1 '\l/' P2" := (or_ltl P1 P2) (at level 100).
  Notation " '!' P" := (not_ltl P) (at level 99).
  Notation " 'f' " := (false_ltl) (at level 99).

(* ===================================================== *)

(* ======================= OPERATORS =================== *)

  Inductive next (P: stream_formula) : stream_formula :=
    | next_intro : forall (a: state)(s: stream), P s -> next P (occ a s).

  Inductive until (P1 P2: stream_formula) : stream_formula :=
    | until_intro : forall (s: stream), P2 s -> until P1 P2 s
    | until_occ : forall (a: state)(s: stream), P1 (occ a s) -> until P1 P2 s -> until P1 P2 (occ a s).

  Inductive sometime (P: stream_formula) : stream_formula :=
    | sometime_intro : forall (s: stream), P s -> sometime P s
    | sometime_occ : forall (a: state)(s: stream), sometime P s -> sometime P (occ a s).

  CoInductive always (P: stream_formula) : stream_formula :=
    | always_occ : forall (a: state)(s: stream), P (occ a s) -> always P s -> always P (occ a s).

  Inductive previous (P: stream_formula) : stream_formula :=
    | previous_occ : forall (a: state)(s: stream), P (occ a s) -> previous P s.

  Inductive back (P1 P2: stream_formula) : stream_formula :=
    | back_intro : forall (s: stream), P2 s -> back P1 P2 s
    | back_occ : forall (a: state)(s: stream), P1 s -> back P1 P2 (occ a s) -> back P1 P2 s.

  Notation "'X' P" := (next P) (at level 100).
  Notation "P1 'U' P2" := (until P1 P2) (at level 100).
  Notation "'F' P" := (sometime P) (at level 100).
  Notation "'G' P" := (always P) (at level 100).
  Notation "'Y' P" := (previous P) (at level 100).
  Notation "P1 'S' P2" := (back P1 P2) (at level 100).

(* ===================================================== *)

(* ========= GETTING CLASSICAL LOGIC RESULTS =========== *)

Definition peirce := forall P Q:Prop, ((P->Q)->P)->P.
Definition classic := forall P:Prop, ~~P -> P.
Definition excluded_middle := forall P:Prop, P\/~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P/\~Q)->P\/Q.
Definition implies_to_or := forall P Q:Prop, (P->Q)->(~P\/Q).

Lemma excluded_middle_to_classic : excluded_middle -> classic.
Proof.
  unfold excluded_middle, classic.
  intros.
  elim H with (P:=P).
  intro; assumption.
  intro; apply False_ind.
  apply H0; assumption.
Qed.

Lemma classic_to_peirce : classic -> peirce.
Proof.
  unfold classic, peirce.
  intros.
  apply H.
  intro.
  apply H1.
  apply H0.
  intro.
  apply False_ind.
  apply H1.
  apply H2.
Qed.

Lemma de_morgan_not_and_not_to_excluded_middle : de_morgan_not_and_not -> excluded_middle.
Proof.
  unfold de_morgan_not_and_not, excluded_middle.
  intros.
  apply H.
  intro.
  destruct H0.
  apply H1.
  assumption.
Qed.

Lemma peirce_to_de_morgan_not_and_not : peirce -> de_morgan_not_and_not.
Proof.
  unfold peirce,de_morgan_not_and_not.
  intros.
  apply H with (Q:=False).
  intro.
  apply False_ind.
  apply H0.
  split.
  intro.
  apply H1.
  left.
  assumption.
  intro.
  apply H1.
  right.
  assumption.
Qed.

Lemma de_morgan_not_and_not_to_implies_to_or : de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold implies_to_or, de_morgan_not_and_not.
  intros.
  induction H with (P:=~P) (Q:=Q).
  left.
  assumption.
  right.
  assumption.
  intro.
  elim H1.
  intros.
  apply H3.
  apply H0.
  induction H with (P:=P) (Q:=~P).
  assumption.
  apply False_ind.
  apply H2.
  assumption.
  intro.
  apply H2.
  destruct H4.
  assumption.
Qed.

Lemma implies_to_or_to_excluded_middle : implies_to_or -> excluded_middle.
Proof.
  unfold excluded_middle, implies_to_or.
intros H P.
  induction (H P P).
  auto.
  auto.
  auto.
Qed.

Axiom classic_2 : forall P : Prop, ~~P -> P.

Lemma classic_1 : forall P Q:Prop, ((P->Q)->P)->P.
Proof.
  apply classic_to_peirce.
  unfold classic.
  intros.
  apply classic_2.
  assumption.
Qed.

Lemma classic_3 : forall P:Prop, P\/~P.
Proof.
  apply de_morgan_not_and_not_to_excluded_middle.
  apply peirce_to_de_morgan_not_and_not.
  apply classic_to_peirce.
  unfold classic.
  intros.
  apply classic_2.
  assumption.
Qed.

Lemma classic_4 : forall P Q:Prop, ~(~P/\~Q)->P\/Q.
Proof.
  apply peirce_to_de_morgan_not_and_not.
  apply classic_to_peirce.
  unfold classic.
  intros.
  apply classic_2.
  assumption.
Qed.

Lemma classic_5 : forall P Q:Prop, (P->Q)->(~P\/Q).
Proof.
  apply de_morgan_not_and_not_to_implies_to_or.
  apply peirce_to_de_morgan_not_and_not.
  apply classic_to_peirce.
  unfold classic.
  intros.
  apply classic_2.
  assumption.
Qed.

(* ===================================================== *)

(* ===================== PRE REQUISITES ================ *)

Lemma always_assumption : forall P Q : stream_formula, (forall s : stream, (G Q) s -> P s) -> forall s : stream, (G Q) s -> (G P) s.
Proof.
  intros P Q.
  cofix H.
  intros H_Q_P s.
  destruct s.
  intros.
  split.
  apply H_Q_P with (s:= occ s s0).
  assumption.
  apply H.
  assumption.
  inversion H0.
  assumption.
Qed.

Lemma always_assumption_1 : forall P Q T: stream_formula, (forall s : stream, (G Q) s -> (G T) s  -> P s) -> forall s : stream, (G Q) s -> (G T) s -> (G P) s.
Proof.
Proof.
  intros P Q T.
  cofix H.
  intros H_Q_P s.
  destruct s.
  intros.
  split.
  apply H_Q_P with (s:= occ s s0).
  assumption.
  assumption.
  apply H.
  assumption.
  inversion H0.
  assumption.
  inversion H1.
  assumption.
Qed.

Lemma not_f : forall (P:stream_formula) (s:stream), (! (F P)) s -> (F (! P)) s.
Proof.
  intros.
  destruct s.
  left.
  intro.
  apply H.
  left.
  assumption.
Qed.

(* ===================================================== *)

(* ================= EQUIVALENT FORMULAS =============== *)


(******************)
(* DISTRIBUTIVITY *) (* 7/7 work *)
(******************)

(* NEXT OPERATOR *)

(* (X (P1 /l\ P2)) s <-> ((X P1) /l\ (X P2)) s *)

Lemma next_and : forall (P1 P2: stream_formula) (s:stream), (X (P1 /l\ P2)) s <-> ((X P1) /l\ (X P2)) s.
Proof.
  firstorder.
  inversion H.
  inversion H0.
  split.
  assumption.
  inversion H.
  inversion H0.
  split.
  assumption.
  destruct s.
  split.
  split.
  inversion H.
  assumption.
  inversion H0.
  assumption.
Qed.

(* (X (P1 \l/ P2)) s <-> ((X P1) \l/ (X P2)) s *)

Lemma next_or : forall (P1 P2: stream_formula) (s:stream), (X (P1 \l/ P2)) s <-> ((X P1) \l/ (X P2)) s.
Proof.
  firstorder.
  inversion H.
  induction H0.
  left.
  split.
  assumption.
  right.
  split.
  assumption.
  inversion H.
  split.
  left.
  assumption.
  inversion H.
  split.
  right.
  assumption.
Qed.

(* (X (P1 U P2)) s <-> ((X P1) U (X P2)) s *)

Lemma next_until : forall (P1 P2: stream_formula) (s:stream), (X (P1 U P2)) s <-> ((X P1) U (X P2)) s.
Proof.
  firstorder.
  destruct s.
  induction H.
  induction H.
  left.
  split.
  assumption.
  right.
  split.
  assumption.
  inversion IHuntil.
  left.
  inversion H1.
  split.
  assumption.
  right.
  inversion H3.
  split.
  assumption.
  assumption.
  induction H.
  destruct s.
  split.
  inversion H.
  left.
  assumption.
  destruct s.
  split.
  right.
  inversion H.
  assumption.
  inversion IHuntil.
  assumption.
Qed.

(* UNTIL OPERATOR *)

(* (P1 U (P2 \l/ P3)) s <-> ((P1 U P2) \l/ (P1 U P3)) s *)

Lemma until_or : forall (P1 P2 P3: stream_formula) (s:stream), (P1 U (P2 \l/ P3)) s <-> ((P1 U P2) \l/ (P1 U P3)) s.
Proof.
  firstorder.
  induction H.
  inversion H.
  left.
  left.
  assumption.
  right.
  left.
  assumption.
  inversion IHuntil.
  left.
  right; assumption.
  right; right; assumption.
  induction H.
  left; left; assumption.
  right; assumption.
  induction H.
  left; right; assumption.
  right; assumption.
Qed.

(* ( (P1 /l\ P2) U P3 ) s <-> ((P1 U P3) /l\ (P2 U P3)) s *)

Lemma until_and : forall (P1 P2 P3: stream_formula) (s:stream), ((P1 /l\ P2) U P3) s <-> ((P1 U P3) /l\ (P2 U P3)) s.
Proof.
  firstorder.
  induction H.
  left; assumption.
  right.
  inversion H.
  assumption.
  assumption.
  induction H.
  left.
  assumption.
  right.
  inversion H.
  assumption.
  assumption.
  induction H0.
  left.
  assumption.
  inversion H.
  left.
  assumption.
  right.
  split.
  assumption.
  assumption.
  apply IHuntil.
  assumption.
Qed.

(* ALWAYS OPERATOR *)

(* (G (P /l\ Q)) s <-> ((G P) /l\ (G Q)) s *)

Lemma and_always : forall (P Q: stream_formula) (s: stream), (G (P /l\ Q)) s <-> ((G P) /l\ (G Q)) s.
Proof.
  firstorder.
  apply always_assumption with (Q:=(P/l\Q))(P:=P).
 intros.
     destruct s0.
     inversion H0.
     inversion H3.
     assumption.
assumption.
apply always_assumption with (Q:=(P/l\Q))(P:=Q).
intros.
     destruct s0.
     inversion H0.
     inversion H3.
     assumption.
  assumption.
  destruct s.
   inversion H.
  apply always_assumption_1 with (Q:=P)(T:=Q)(P:=(P /l\ Q)).
  intros.
    destruct s1.
    split.
  inversion H5.
     assumption.
  inversion H6.
     assumption.
  assumption.
  assumption.
Qed.

(* EVENTUALLY OPERATOR *)

(* (F (P1\l/P2)) s <-> ((F P1) \l/ (F P2)) s*)

Lemma or_eventually : forall (P1 P2: stream_formula) (s:stream), (F (P1\l/P2)) s <-> ((F P1) \l/ (F P2)) s.
Proof.
  firstorder.
  induction H.
  induction H.
  left.
  left.
  assumption.
  right.
  left.
  assumption.
  induction IHsometime.
  left.
  right.
  assumption.
  right.
  right.
  assumption.
  induction H.
  left.
  left.
  assumption.
  right.
  assumption.
  induction H.
  left.
  right.
  assumption.
  right.
  assumption.
Qed.


(*********************************)
(* OPERATORS ITERATIVE BEHAVIOUR *) (* 4/4 work *)
(*********************************)

(* BACK OPERATOR *)

(* (P1 S P2) s <-> (P2 \l/ (P1 /l\ (Y (P1 S P2)))) s*)

Lemma back_unmask : forall (P1 P2:stream_formula)(s:stream), (P1 S P2) s <-> (P2 \l/ (P1 /l\ (Y (P1 S P2)))) s.
Proof.
  firstorder.
  induction H.
  left.
  assumption.
  right.
  split.
  assumption.
  split with (a:=a).
  assumption.
  left.
  assumption.
  destruct s.
  inversion H0.
  right with (a:=a).
  assumption.
  assumption.
Qed.

(* UNTIL OPERATOR *)

(* (P1 U P2) s <-> (P2 \l/ (P1 /l\ (X (P1 U P2)))) s*)

Lemma until_unmask : forall (P1 P2:stream_formula)(s:stream), (P1 U P2) s <-> (P2 \l/ (P1 /l\ (X (P1 U P2)))) s.
Proof.
  firstorder.
  induction H.
  left.
  assumption.
  right.
  split.
  assumption.
  split.
  assumption.
  left.
  assumption.
  destruct s.
  induction H0.
  right.
  assumption.
  assumption.
Qed.

(* EVENTUALLY OPERATOR *)

(* (F P) s <-> (P \l/ (X (F P))) s *)

Lemma eventually_unmask : forall (P: stream_formula)(s: stream),  (F P) s <-> (P \l/ (X (F P))) s.
Proof.
  firstorder.
  induction H.
  left.
  assumption.
  right.
  split.
  assumption.
  left.
  assumption.
  destruct s.
  induction H.
  right.
  assumption.
Qed.

(* ALWAYS OPERATOR *)

(* (G P) s <-> (P /l\ (X (G P))) s *)

Lemma always_unmask : forall (P: stream_formula)(s: stream),  (G P) s <-> (P /l\ (X (G P))) s.
Proof.
  firstorder.
  inversion H.
  assumption.
  inversion H.
  split.
  assumption.
  destruct s.
  split.
  assumption.
  inversion H0.
  assumption.
Qed.


(******************)
(*    NEGATION    *) (* 1/3 work *)
(******************)

(*  NEXT OPERATOR *)

(* (! (X P)) s <-> (X (! P)) s *)

Lemma next_negation : forall (P: stream_formula)(s: stream),  (! (X P)) s <-> (X (! P)) s.
Proof.
  firstorder.
  destruct s.
  split.
  intro.
  apply H.
  split.
  assumption.
  destruct s.
  intro.
  induction H.
  apply H.
  inversion H0.
  assumption.
Qed.

(* ALWAYS OPERATOR *)

(* (! (G P)) s <-> (F (! P)) s *) (*-------- PROBLEMS IN ONE DIRECTION ----------*)

Axiom not_G_1 : forall (P: stream_formula) (s: stream), (! (G P)) s -> (F (! P)) s.

Lemma not_G_2 : forall (P: stream_formula) (s: stream), (F (! P)) s -> (! (G P)) s.
Proof.
  intros.
  induction H.
  intro.
  apply H.
  inversion H0.
  assumption.
  intro.
  apply IHsometime.
  inversion H0.
  assumption.
Qed.

Lemma not_G_11 : forall (P: stream_formula) (s: stream), (! (G P)) s -> (F (! P)) s.
Proof.
  intros.
  apply eventually_unmask.
  apply classic_4 with (P:=(!P) s)(Q:=(X(F ! P)) s).
  intro.
  inversion H0.
  apply classic_2 in H1.
  destruct s.
  apply H.
  split.
  assumption.
Abort.

(* EVENTUALLY OPERATOR *)

(* (! (F P)) s <-> (G (! P)) s *) (*-------- PROBLEMS IN ONE DIRECTION ----------*)

Axiom not_F_1 : forall (P: stream_formula) (s: stream), (! (F P)) s -> (G (! P)) s.
Lemma not_F_11 : forall (P: stream_formula) (s: stream), (! (F P)) s -> (G (! P)) s.
Proof. 
  intros.
  destruct s.
  split.
  intro.
  apply H.
  left.
  assumption.
  induction H.
Abort.

Lemma not_F_2 : forall (P: stream_formula) (s: stream), (G (! P)) s -> (! (F P)) s.
Proof.
  intros.
  intro.
  generalize H.
  apply not_G_2.
  induction H0.
  left.
  intro.
  apply H1.
  assumption.
  right.
  apply IHsometime.
  inversion H.
  assumption.
Qed.


(*****************)
(* ABBREVIATIONS *) (* 1/3 work *)
(*****************)

(* NEXT OPERATOR *)

(* (X P) s <-> (f U P) s *) (*------------------PROBLEMS--------------*)

Lemma next_unmask : forall (P: stream_formula)(s: stream), (f U P) s <-> (X P) s.
Proof.
  firstorder.
  destruct s.
  split.
  inversion H.
  apply False_ind.
  inversion H.
  generalize H2.
Abort.

(* EVENTUALLY OPERATOR *)

(* (F P) s <-> (t U P) s *)

Lemma until_eventually : forall (P: stream_formula)(s: stream), (t U P) s <-> (F P) s.
Proof.
  firstorder.
  -elim H.
  --intros.
    left.
    assumption.
  --intros.
    right.
    assumption.
  -elim H.
  --intros.
    left.
    assumption.
  --intros.
    right. 
    unfold true_ltl.
    tauto.
    assumption.
Qed.

(* ALWAYS OPERATOR *)

(*(G P) s <-> (! (F (! P))) s*)

Lemma G_to_F_1 : forall (P: stream_formula) (s: stream), (G P) s -> (! (F (! P))) s.
Proof.
  intros.
  apply not_F_2.
  apply always_assumption with (P:=(! (! P)))(Q:=P).
  intros.
  intro.
  apply H1.
  destruct s0.
  inversion H0.
  assumption.
  assumption.
Qed.

Lemma G_to_F_2 : forall (P: stream_formula) (s: stream), (! (F (! P))) s -> (G P) s.
Proof.
  intros.
  apply not_F_1 in H.
  apply always_assumption with (Q:=(! (! P))).
  intros.
  destruct s0.
  inversion H0.
  (* The only way is the adding of the "double negation" axiom? *)
Abort.


(************************)
(* SPECIAL EQUIVELANCES *) (* 5/5 work *)
(************************)

(* (G (G P)) s <-> (G P) s *)

Lemma always_always : forall (P: stream_formula) (s: stream), (G (G P)) s <-> (G P) s.
Proof.
  firstorder.
  -destruct s.
   inversion H.
   assumption.
  -apply always_assumption with (P:=(G P))(Q:=P).
   intros.
   assumption.
   assumption.
Qed.

(* (F (F P)) s <-> (F P) s *)

Lemma eventually_eventually : forall (P: stream_formula) (s: stream), (F (F P)) s <-> (F P) s.
Proof.
  firstorder.
  -intros.
   induction H.
  --assumption.
  --right.
    assumption.
  -intros.
   destruct s.
  --left.
    assumption.
Qed.

(* (G (F (G P))) s <-> (F (G P)) s *)

Lemma g_f_g : forall (P: stream_formula)(s: stream),  (G (F (G P))) s <-> (F (G P)) s.
Proof.
  firstorder.
  inversion H.
  assumption.
  induction H.
  destruct s.
  split.
  left.
  assumption.
  inversion H.
  apply always_assumption with (P:=(F (G P)))(Q:=P).
  intros.
  left.
  assumption.
  assumption.
  split.  
  right.
  assumption.
  assumption.
Qed.

(* (F (G (F P))) s <-> (G (F P)) s *)

Lemma f_g_f : forall (P: stream_formula)(s: stream),  (F (G (F P))) s <-> (G (F P)) s.
Proof.
  firstorder.
  induction H.
  assumption.
  split.
  right.
  inversion IHsometime.
  assumption.
  assumption.
  left.
  assumption.
Qed.

(* (P1 U (P1 U P2)) s <-> (P1 U P2) s *)

Lemma until_until : forall (P1 P2: stream_formula) (s:stream), (P1 U P2) s <-> (P1 U (P1 U P2)) s.
Proof.
  firstorder.
  left.
  assumption.
  induction H.
  assumption.
  right.
  assumption.
  assumption.
Qed.

(* ===================================================== *)

End LTL.
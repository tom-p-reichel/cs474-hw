Inductive Propo {T:Type} := varo : T -> @Propo T | negvaro : T -> @Propo T  | oro : (@Propo T -> @Propo T -> @Propo T)  | ando : (@Propo T -> @Propo T -> @Propo T) .

Notation "a 'ando' b" := (ando a b) (at level 80, right associativity).

Notation "a 'oro' b" := (oro a b) (at level 85, right associativity).


(* utility defs *)

Fixpoint evaluate {T:Type} (p:Propo) (model : T -> bool) : bool :=
  match p with
  | varo n => model n
  | negvaro n => negb (model n)
  | a oro b => orb (evaluate a model) (evaluate b model)
  | a ando b => andb (evaluate a model) (evaluate b model)
  end.

Definition satisfiable {T:Type} (p:Propo) : Prop := exists (model : T -> bool), evaluate p model = true.

(* for example *)

Theorem example : satisfiable (negvaro 0).
Proof.
exists (fun x => false).
reflexivity.
Qed.

(* Tseitin extends the set of propositions of its input. *)

Inductive TseitinVar {T:Type} := canonical_proposition : T -> @TseitinVar T | formula_proposition : (@Propo T) -> @TseitinVar T.

(* for simplicity *)
Definition fvaro {T:Type} (a : @Propo T) := varo (formula_proposition a).
Definition fnegvaro {T:Type} (a : @Propo T) := negvaro (formula_proposition a).
Definition cvaro {T:Type} (a : T) := varo (canonical_proposition a).
Definition cnegvaro {T:Type} (a : T) := negvaro (canonical_proposition a).

(* Tseitin construction, as described to us. *)



Fixpoint tseitin' {T:Type} (p:@Propo T) : @Propo (@TseitinVar T) :=
  match p with
  | varo n => ((fvaro p) oro (cnegvaro n)) ando ((fnegvaro p) oro (cvaro n))
  | negvaro n => ((fvaro p) oro (cvaro n)) ando ((fnegvaro p) oro (cnegvaro n))
  | r ando s => ((fnegvaro p) oro (fvaro r)) ando ((fnegvaro p) oro (fvaro s)) ando ((fnegvaro r) oro (fnegvaro s) oro (fvaro p)) ando (tseitin' r) ando (tseitin' s)
  | r oro s => ((fnegvaro p) oro (fvaro r) oro (fvaro s)) ando ((fnegvaro r) oro (fvaro p)) ando ((fnegvaro s) oro (fvaro p)) ando (tseitin' r) ando (tseitin' s)
  end.

Definition tseitin {T:Type} (p:@Propo T) : @Propo (@TseitinVar T) := (fvaro p) ando (tseitin' p).

Ltac isbool := fun t => match type of t with
  | bool => idtac
  | _ => fail
  end.

Ltac hit :=
  fun t => multimatch type of t with
  | context [ ?A ] => isbool A; assert_fails unify A true; assert_fails unify A false; tryif match A with context [ ?B ] => isbool B; assert_fails unify A B end then fail else destruct_with_eqn @A
  end.

Ltac pummel := fun t => repeat hit t; try discriminate t; try reflexivity.

Ltac simpl_all := simpl; repeat multimatch goal with
  | H : _ |- _ => simpl in H
  end.

Ltac hit_goal :=
  multimatch goal with
  | _ : _ |- context [ ?A ] => isbool A; assert_fails unify A true; assert_fails unify A false; tryif match A with context [ ?B ] => isbool B; assert_fails unify A B end then fail else destruct_with_eqn @A
  end.

Ltac pummel_goal := repeat hit_goal; try reflexivity.

Lemma tseitin_internals : forall (T:Type), forall (p:@Propo T), forall (m:T -> bool), evaluate (tseitin' p) (fun p => match p with
    | canonical_proposition n => m n
    | formula_proposition f => evaluate f m
    end) = true.
Proof.
  intros.
  induction p; simpl; pummel_goal; try discriminate IHp1; try discriminate IHp2.
Qed.

Lemma tseitin_internals_2 : forall (T:Type), forall (p:@Propo T), forall (m: @TseitinVar T -> bool), evaluate (tseitin p) m = true -> evaluate p (fun p => m (canonical_proposition p)) = true.
Proof.
  intros.
  induction p; simpl_all; pummel_goal; pummel H; simpl_all; try apply IHp1; try apply IHp2; reflexivity.
Qed.
  

Theorem tseitin_works : forall (T:Type), forall (p:@Propo T), satisfiable p <-> satisfiable (tseitin p).
Proof.
  intros.
  unfold satisfiable.
  constructor; intros; destruct H.
  exists (fun p => match p with
    | canonical_proposition n => x n
    | formula_proposition f => evaluate f x
    end).
  simpl.
  rewrite H.
  rewrite tseitin_internals.
  reflexivity.
  exists (fun p => x (canonical_proposition p)).
  apply tseitin_internals_2.
  apply H.
Qed.
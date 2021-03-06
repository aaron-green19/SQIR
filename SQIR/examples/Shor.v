(*From Interval Require Import Tactic.*)
Require Import Reals Psatz ZArith Znumtheory.
Require Export VectorStates QPE.

Local Close Scope R_scope.

Local Coercion INR : nat >-> R.
Local Coercion Z.of_nat : nat >-> BinNums.Z.

(* r is the order of a modulo p *)
Definition Order (a r N : nat) :=
  0 < r /\
  a^r mod N = 1 /\
  (forall r' : nat, (0 < r' /\ a^r' mod N = 1) -> r' >= r).

Lemma Order_N_lb :
  forall a r N,
    Order a r N ->
    1 < N.
Proof.
  intros. 
  destruct (0 <? N)%nat eqn:E.
  - destruct (1 <? N)%nat eqn:S.
    + apply Nat.ltb_lt in S; easy.
    + apply Nat.ltb_ge in S. destruct H as [_ [? _]].
      apply Nat.ltb_lt in E. replace N with 1%nat in H by omega. simpl in H. discriminate H.
  - apply Nat.ltb_ge in E. assert (N=0) by omega. destruct H as [_ [? _]]. rewrite H0 in H. simpl in H. omega.
Qed.

Lemma Order_a_nonzero :
  forall a r N,
    Order a r N ->
    0 < a.
Proof.
  intros. assert (HN := H). apply Order_N_lb in HN.
  destruct (0 <? a)%nat eqn:E.
  - apply Nat.ltb_lt in E; easy.
  - apply Nat.ltb_ge in E. assert (a=0) by omega. destruct H as [? [? _]]. rewrite H0 in H1. rewrite Nat.pow_0_l in H1. rewrite Nat.mod_0_l in H1 by omega. omega. omega.
Qed.  

Lemma Order_a_inv_ex :
  forall a r N,
    Order a r N ->
    exists a_inv,
      (a * a_inv) mod N = 1.
Proof.
  intros. exists (a^(pred r))%nat. destruct H as [? [? _]].
  assert (a * a ^ Init.Nat.pred r = a^1 * a^(Init.Nat.pred r))%nat. rewrite Nat.pow_1_r; easy. rewrite H1.
  rewrite <- Nat.pow_add_r. rewrite Nat.succ_pred; omega.
Qed.

Lemma inv_pow :
  forall a r N a_inv x,
    Order a r N ->
    (a * a_inv) mod N = 1 ->
    (a^x * a_inv^x) mod N = 1.
Proof.
  intros. assert (HN := H). apply Order_N_lb in HN. induction x.
  - simpl. apply Nat.mod_1_l. easy.
  - simpl. rewrite Nat.mul_assoc. rewrite (Nat.mul_shuffle0 a (a^x)%nat a_inv).
    rewrite mult_assoc_reverse with (n:=(a * a_inv)%nat). rewrite <- Nat.mul_mod_idemp_l with (a:=(a * a_inv)%nat); try omega. rewrite H0. rewrite Nat.mul_1_l. apply IHx.
Qed.

Lemma Pow_minus_aux :
  forall a r N a_inv x d,
    Order a r N ->
    (a * a_inv) mod N = 1 ->
    a^d mod N = (a^(x + d) * a_inv^x) mod N.
Proof.
  intros. replace (x + d)%nat with (d + x)%nat by omega. rewrite Nat.pow_add_r.
  assert (HN := H). apply Order_N_lb in HN.
  rewrite <- Nat.mul_assoc. rewrite <- Nat.mul_mod_idemp_r; try omega. rewrite inv_pow with (r:=r); auto. rewrite Nat.mul_1_r. easy.
Qed.

Lemma Pow_minus :
  forall a r N a_inv x1 x2,
    Order a r N ->
    x1 <= x2 ->
    (a * a_inv) mod N = 1 ->
    a^(x2-x1) mod N = (a^x2 * a_inv^x1) mod N.
Proof.
  intros. rewrite Pow_minus_aux with (r:=r) (a:=a) (x:=x1) (a_inv:=a_inv); try easy. replace (x1 + (x2 - x1))%nat with (x2 - x1 + x1)%nat by omega. rewrite Nat.sub_add; easy.
Qed.

Lemma Pow_diff :
  forall a r N x1 x2,
    Order a r N ->
    0 <= x1 < r ->
    0 <= x2 < r ->
    x1 < x2 ->
    a^x1 mod N <> a^x2 mod N.
Proof.
  intros. intro.
  assert (Ha_inv := H). apply Order_a_inv_ex in Ha_inv. destruct Ha_inv as [a_inv Ha_inv].
  assert (HN := H). apply Order_N_lb in HN.
  assert (a^(x2-x1) mod N = 1).
  rewrite Pow_minus with (r:=r) (a_inv:=a_inv); try omega; try easy.
  rewrite <- Nat.mul_mod_idemp_l; try omega.
  rewrite <- H3. rewrite Nat.mul_mod_idemp_l; try omega.
  rewrite <- Pow_minus with (r:=r); try omega; try easy.
  rewrite Nat.sub_diag. simpl. apply Nat.mod_1_l; easy.
  destruct H as [_ [_ Hminimal]].
  pose (Hminimal (x2 - x1)%nat) as Hcounter.
  assert (0 < x2 - x1 /\ a ^ (x2 - x1) mod N = 1)%nat by omega.
  apply Hcounter in H. omega.
Qed.

(* Parameter assumptions of the Shor's algorithm *)
Definition BasicSetting (a r N m n : nat) :=
  0 < a < N /\
  Order a r N /\
  N^2 < 2^m <= 2 * N^2 /\
  N <= 2^n < 2 * N.

Definition basisPowerA (a r N n : nat) := basis_vector (2^n) (a^r mod N).

Local Open Scope R_scope.

Definition ω_neg (r : nat) := Cexp (-2 * PI / r).

(* The ψ states are the eigenstates of the target circuit. Described in https://cs.uwaterloo.ca/~watrous/LectureNotes/CPSC519.Winter2006/10.pdf. *)
Definition ψ (a r N j n : nat) :=
  (1 / √r) .* vsum r (fun x => (ω_neg r)^(j * x) .* (basisPowerA a x N n)).

Lemma ω_neg_sum_zero : forall r, Csum (fun i =>  (ω_neg r ^ (i * 0))%C) r = r.
Proof.
  intros.
  apply Csum_1.
  intros.
  unfold ω_neg.
  rewrite Cexp_pow.
  rewrite Nat.mul_0_r.
  autorewrite with R_db.
  apply Cexp_0.
Qed. 

(* Proved in a slightly different form in Csum_Cexp_nonzero in QPE.v. We should 
   update the two files to use consistent notation. *)
Lemma ω_neg_sum_nonzero :
  forall (r k : nat),
    0 < r ->
    0 < k < r -> 
    Csum (fun i => (ω_neg r ^ (i * k))%C) r = 0.
Proof.
  intros.
  assert (((fun (x : nat) => (ω_neg r)^(x * k)) = (fun (x : nat) => ((ω_neg r) ^ k) ^ x))%C).
  { apply functional_extensionality. intros. unfold ω_neg. do 3 rewrite Cexp_pow.
    rewrite mult_INR. replace (-2 * PI / r * (x * k)) with (-2 * PI / r * k * x) by lra. easy.
  }
  rewrite H1. rewrite Csum_geometric_series. unfold ω_neg. do 2 rewrite Cexp_pow.
  replace (-2 * PI / r * k * r) with (-(2 * PI * k)) by (field; lra). rewrite Cexp_neg.
  rewrite <- Cexp_pow. rewrite Cexp_2PI.
  replace (1 ^ k)%C with C1 by (rewrite RtoC_pow; rewrite pow1; auto).
  replace (1 - / 1)%C with C0 by lca. lca.
  unfold ω_neg. rewrite Cexp_pow. unfold Cexp. intro. inversion H2. rewrite H4 in H5. rewrite Rplus_0_l in H5.
  assert (0 < / r * k < 1).
  { destruct H0. split. 
    - apply Rinv_0_lt_compat in H. apply Rmult_lt_0_compat; assumption.
    - pose (Rinv_lt_contravar k r (Rmult_lt_0_compat k r H0 H) H3) as H6.
      pose (Rmult_lt_compat_r k (/ r) (/ k) H0 H6) as H7.
      rewrite <- Rinv_l_sym in H7; lra.
  }
  rewrite <- sin_neg in H5. replace (- (-2 * PI / r * k)) with (2 * PI / r * k) in H5 by lra.
  assert (0 < 2 * PI).
  { apply Rmult_lt_0_compat; try lra. apply PI_RGT_0.
  }
  assert (0 < 2 * PI / r * k < 2 * PI).
  { destruct H3. replace (2 * PI / r * k) with ((2 * PI) * (/ r * k)) by lra. split.
    - apply Rmult_lt_0_compat; lra. 
    - pose (Rmult_lt_compat_l (2 * PI) (/ r * k) 1 H6 H7) as H8.
      autorewrite with R_db in H8. assumption.
  }
  destruct H7.
  apply sin_eq_O_2PI_0 in H5; try (apply Rlt_le; assumption).
  destruct H5 as [? |[? | ?]]; try lra.
  replace ((-2 * PI / r * k)) with (- (2 * PI / r * k)) in H4 by lra. rewrite H5 in H4.
  rewrite cos_neg in H4. rewrite cos_PI in H4. lra.
Qed.

Lemma sum_of_ψ_is_one :
  forall a r N m n : nat,
    BasicSetting a r N m n ->
    (1 / √r) .* vsum r (fun j => ψ a r N j n) = basis_vector (2^n) 1.
Proof.
  intros.
  destruct H as [? [[? _] _]]. (* we only need a few parts of H *)
  unfold ψ.
  rewrite <- Mscale_vsum_distr_r.
  rewrite Mscale_assoc.
  rewrite vsum_swap_order.
  erewrite vsum_eq.
  2: { intros. rewrite Mscale_vsum_distr_l. reflexivity. }
  erewrite vsum_unique.
  2: { exists O.
       split. assumption.
       split.
       rewrite ω_neg_sum_zero. reflexivity.
       intros.
       rewrite ω_neg_sum_nonzero.
       lma.
       apply lt_0_INR; assumption. split. apply not_eq_sym in H2. apply neq_0_lt in H2. apply lt_0_INR; assumption. apply lt_INR; assumption.
  }
  unfold basisPowerA.
  rewrite Nat.pow_0_r.
  rewrite Nat.mod_1_l by lia.
  rewrite Mscale_assoc.
  replace (1 / √ r * (1 / √ r) * r)%C with C1.
  lma.
  field_simplify_eq.
  rewrite <- RtoC_mult.
  rewrite sqrt_def. 
  reflexivity.
  apply pos_INR.
  apply RtoC_neq.
  apply sqrt_neq_0_compat.
  apply lt_0_INR. 
  assumption.
Qed.

Lemma mod_pow :
  forall a b N,
    (0 < N)%nat ->
    a^b mod N = (a mod N)^b mod N.
Proof.
  intros. induction b.
  - simpl; auto.
  - simpl. rewrite Nat.mul_mod; try omega. rewrite IHb. apply Nat.mul_mod_idemp_r. omega.
Qed.

Lemma MultiGroup_modulo_N :
  forall a r N x,
    Order a r N ->
    a^x mod N = a^(x mod r) mod N.
Proof.
  intros. assert (HN := H). apply Order_N_lb in HN.
  destruct H as [? [? ?]]. replace (a ^ x mod N)%nat with ((a^(r * (x / r) + x mod r)) mod N)%nat.
  2: { rewrite <- Nat.div_mod; omega. }
  rewrite Nat.pow_add_r. rewrite Nat.mul_mod; try omega.
  rewrite Nat.pow_mul_r. rewrite mod_pow; try omega.
  rewrite H0. rewrite Nat.pow_1_l. rewrite <- Nat.mul_mod; try omega. rewrite Nat.mul_1_l. easy.
Qed.

(* The description of the circuit implementing "multiply a modulo N". *)
Definition MultiplyCircuitProperty (a N n : nat) (c : base_ucom n) :=
  forall x : nat,
    ((0 <= x < N)%nat ->
     (uc_eval c) × (basis_vector (2^n) x) = basis_vector (2^n) (a * x mod N)).

Lemma MC_eigenvalue :
  forall (a r N j m n : nat) (c : base_ucom n),
    BasicSetting a r N m n ->
    MultiplyCircuitProperty a N n c ->
    (uc_eval c) × (ψ a r N j n) = Cexp (2 * PI * j / r) .* (ψ a r N j n).
Proof.
  intros. unfold ψ. 
  unfold BasicSetting in H. destruct H as [Ha [HOrder [HN1 HN2]]]. 
  rewrite Mscale_mult_dist_r. rewrite Mscale_assoc. rewrite Cmult_comm.
  rewrite <- Mscale_assoc. rewrite Mscale_vsum_distr_r. rewrite Mmult_vsum_distr_l.
  unfold MultiplyCircuitProperty in H0. remember (uc_eval c) as U.
  replace (vsum r (fun i : nat => U × (ω_neg r ^ (j * i) .* basisPowerA a i N n))) 
    with (vsum r (fun i : nat => (ω_neg r ^ (j * i) .* basisPowerA a (i+1) N n))).
  2:{
    apply vsum_eq. intros. rewrite Mscale_mult_dist_r.
    unfold basisPowerA. rewrite H0. rewrite Nat.add_1_r. simpl. rewrite Nat.mul_mod_idemp_r. easy.
    (* N <> 0 *)
    destruct Ha. unfold not. intros. rewrite H3 in H2. easy.
    (* 0 <= a^i mod N < N *)
    apply Nat.mod_bound_pos. apply Nat.le_0_l. apply Nat.lt_trans with a. easy. easy. 
  }
  replace (vsum r (fun i : nat => ω_neg r ^ (j * i) .* basisPowerA a (i + 1) N n))
    with (vsum r (fun i : nat => Cexp (2 * PI * j / r) .* (ω_neg r ^ (j * i) .* basisPowerA a i N n))).
  easy.
  destruct r. easy. 
  rewrite <- vsum_extend_l. rewrite <- vsum_extend_r. rewrite Mplus_comm.
  unfold shift.
  assert (forall t (A B C D : Vector t), A = B -> C = D -> A .+ C = B .+ D).
  { intros. rewrite H. rewrite H1. easy. }
  apply H.   
  - apply vsum_eq. intros. rewrite Mscale_assoc. unfold ω_neg. rewrite Cexp_pow. rewrite Cexp_pow.
    rewrite <- Cexp_add. 
    replace (2 * PI * j / S r + -2 * PI / S r * (j * (i + 1))%nat) with (-2 * PI / S r * (j * i)%nat).
    easy. repeat rewrite mult_INR. rewrite plus_INR. simpl. lra.
  - unfold basisPowerA. remember (S r) as r'. unfold ω_neg. simpl. destruct HOrder as [Hr [HO1 HO2]].
    rewrite Nat.add_1_r. rewrite <- Heqr'. rewrite HO1. rewrite Nat.mod_small.
    rewrite Mscale_assoc. repeat rewrite Cexp_pow. rewrite <- Cexp_add.
    rewrite <- (Cmult_1_l (Cexp (-2 * PI / r' * (j * r)%nat))). replace 1 with (1^j). rewrite <- RtoC_pow. 
    rewrite <- Cexp_2PI. rewrite Cexp_pow. rewrite <- Cexp_add. repeat rewrite mult_INR.  simpl.
    replace (2 * PI * j / r' + -2 * PI / r' * (j * 0)) with (2 * PI * j + -2 * PI / r' * (j * r)).
    easy. simpl. rewrite Heqr'. rewrite <- Nat.add_1_r. repeat rewrite plus_INR. repeat rewrite Rdiv_unfold. simpl.
    repeat rewrite Rmult_0_r. rewrite Rplus_0_r. replace (-2 * PI) with (2 * PI * -1) by lra. 
    repeat rewrite Rmult_assoc.
    repeat rewrite <- Rmult_plus_distr_l.
    replace (j + -1 * (/ (r + 1) * (j * r))) with (j * / (r + 1)). easy.
    rewrite <- (Rmult_1_r j) at 2. rewrite <- (Rinv_r (r+1)) at 2.
    rewrite Rmult_comm. lra. 
    + replace (r+1) with (r+1%nat). rewrite <- plus_INR. rewrite Nat.add_1_r. rewrite <- Heqr'.
      apply lt_0_INR in Hr. apply Rlt_dichotomy_converse. right. easy. easy.
    + apply pow1.
    + destruct N. easy. destruct N. easy. lia. 
Qed.

Definition round (x : R) := up (x - /2).

(* The target basis we focus on, when the sampling result locates near k/r *)
Definition s_closest (m k r : nat) :=
  Z.to_nat (round (k / r * 2^m)%R).

(* Copied from QPEGeneral.v *)
Definition probability_of_outcome {n} (ψ o : Vector n) : R := 
  (Cmod ((o† × ψ) 0%nat 0%nat)) ^ 2.

Lemma QPE_MC_partial_correct :
  forall (a r N k m n : nat) (c : base_ucom n),
    BasicSetting a r N m n ->
    MultiplyCircuitProperty a N n c ->
    0 <= k < r ->
    probability_of_outcome ((uc_eval (QPE m n c)) × ((basis_vector (2^m) 0) ⊗ (ψ a r N k n))) ((basis_vector (2^m) (s_closest m k r)) ⊗ (ψ a r N k n)) >= 4 / (PI ^ 2).
Admitted.

Lemma QPE_MC_correct :
  forall (a r N k m n : nat) (c : base_ucom n),
    BasicSetting a r N m n ->
    MultiplyCircuitProperty a N n c ->
    0 <= k < r ->
    probability_of_outcome ((uc_eval (QPE m n c)) × ((basis_vector (2^m) 0) ⊗ (basis_vector (2^n) 1))) ((basis_vector (2^m) (s_closest m k r)) ⊗ (ψ a r N k n)) >= 4 / (PI ^ 2 * r).
Admitted.


(* Finds p/q such that |s/2^m-p/q|<=1/2^(m+1) and q<N. Must make sure 2^m>N^2 to secure the uniqueness. *)
Fixpoint CF_ite (n a b p1 q1 p2 q2 N : nat) : nat * nat :=
  if q1 <? N then
    match n with
    | O => (p1, q1)
    | S n => let c := (b / a)%nat in
            CF_ite n (b mod a)%nat a (c*p1+p2)%nat (c*q1+q2)%nat p1 q1 N
    end
  else (p2, q2).

Compute (CF_ite 3 72 100 0 1 1 0 5).

(* Not sure if this bound is correct. But it seems enough *)
Definition CF_bound (N : nat) := (Nat.log2 N + 1)%nat.

Definition ContinuedFraction (s N m : nat) : nat * nat := CF_ite (CF_bound N) s (2^m) 0 1 1 0 N.

Definition Shor_post (s N m : nat) := snd (ContinuedFraction s N m).

Lemma Rabs_center :
  forall x y z d1 d2,
    Rabs (x - y) < d1 ->
    Rabs (x - z) < d2 ->
    Rabs (y - z) < d1 + d2.
Proof.
  intros. 
  rewrite Rabs_minus_sym in H0.
  apply Rabs_def2 in H. apply Rabs_def2 in H0.
  apply Rabs_def1; lra.
Qed.

Lemma Rabs_Z_lt_1 :
  forall z,
    Rabs (IZR z) < 1 ->
    (z = 0)%Z.
Proof.
  intros. rewrite <- abs_IZR in H. apply lt_IZR in H. lia.
Qed.

Lemma ClosestFracUnique :
  forall (α : R) (p1 q1 p2 q2 N : nat),
    (0 < N)%nat ->
    (0 < q1 <= N)%nat ->
    (0 < q2 <= N)%nat ->
    Rabs (α - p1 / q1) < / (2 * N^2) ->
    Rabs (α - p2 / q2) < / (2 * N^2) ->
    p1 / q1 = p2 / q2.
Proof.
  intros. destruct H0 as [H00 H01]. destruct H1 as [H10 H11].
  apply lt_INR in H. simpl in H. apply lt_INR in H00. simpl in H00. apply lt_INR in H10. simpl in H10.
  apply le_INR in H01. apply le_INR in H11.
  assert (Rabs (p1 / q1 - p2 / q2) < / N^2).
  { replace (/ N^2) with (/ (2 * N^2) + / (2 * N^2)) by (field; lra).
    apply Rabs_center with (x := α); easy.
  }
  replace (p1 / q1 - p2 / q2) with (IZR (p1 * q2 - p2 * q1)%Z / (q1 * q2)) in H0.
  2:{ rewrite minus_IZR. do 2 rewrite mult_IZR. repeat rewrite <- INR_IZR_INZ. field. lra.
  }
  assert (forall a b, b <> 0 -> Rabs (a / b) = Rabs a / Rabs b).
  { intros. replace (a / b) with (a * /b) by lra. rewrite Rabs_mult. rewrite Rabs_Rinv; easy.
  }
  assert (0 < q1 * q2) by (apply Rmult_lt_0_compat; lra).
  rewrite H1 in H0 by lra.
  assert (Rabs (q1 * q2) = q1 * q2).
  { apply Rabs_pos_eq. apply Rmult_le_pos; lra.
  }
  rewrite H5 in H0. unfold Rdiv in H0. apply Rmult_lt_compat_r with (r:=q1*q2) in H0; try assumption.
  rewrite Rmult_assoc in H0. rewrite Rinv_l in H0 by lra. rewrite Rmult_1_r in H0.
  assert (/ N ^ 2 * (q1 * q2) <= 1).
  { apply Rmult_le_reg_l with (r:=N^2). simpl. rewrite Rmult_1_r. apply Rmult_lt_0_compat; easy.
    rewrite <- Rmult_assoc. rewrite Rinv_r. rewrite Rmult_1_r. rewrite Rmult_1_l. simpl. rewrite Rmult_1_r. apply Rmult_le_compat; lra.
    simpl. rewrite Rmult_1_r. apply Rmult_integral_contrapositive_currified; lra.
  }
  pose (Rlt_le_trans _ _ _ H0 H6) as H7.
  apply Rabs_Z_lt_1 in H7.
  assert (p1 * q2 = p2 * q1).
  { repeat rewrite INR_IZR_INZ. repeat rewrite <- mult_IZR. replace (p1 * q2)%Z with (p2 * q1)%Z by lia. easy.
  }
  apply Rmult_eq_reg_r with (r:=q1 * q2); try lra.
  replace (p1 / q1 * (q1 * q2)) with (p1 * q2 * (/ q1 * q1)) by lra. rewrite Rinv_l by lra.
  replace (p2 / q2 * (q1 * q2)) with (p2 * q1 * (/ q2 * q2)) by lra. rewrite Rinv_l by lra.
  rewrite H8. easy.
Qed.

Lemma round_inequality :
  forall x,
    x - /2 < IZR (round x) <= x + /2.
Proof.
  intros. unfold round.
  pose (archimed (x - /2)) as H. destruct H as [H0 H1].
  lra.
Qed.

Lemma round_pos :
  forall x,
    0 <= x ->
    (0 <= round x)%Z.
Proof.
  intros. pose (round_inequality x) as G. destruct G as [G0 G1].
  assert (-1 < IZR (round x)) by lra. apply lt_IZR in H0. lia.
Qed.

Lemma IZR_IZN_INR :
  forall z,
    (0 <= z)%Z ->
    IZR z = Z.to_nat z.
Proof.
  intros. destruct z; try lia. easy.
  simpl. rewrite INR_IPR. easy.
Qed.

Lemma s_closest_is_closest :
  forall a r N m n k,
    BasicSetting a r N m n ->
    (0 < k < r)%nat ->
    Rabs ((s_closest m k r) / (2^m) - k / r) < 1 / (2 * N^2).
Proof.
  intros. destruct H as [Ha [HOrder [[Hm1 Hm2] HN2]]]. unfold s_closest. assert (HN := HOrder). apply Order_N_lb in HN. apply lt_INR in HN. simpl in HN.
  assert (PowM: 0 < 2 ^ m) by (apply pow_lt; lra).
  assert (0 <= round (k / r * 2 ^ m))%Z.
  { apply round_pos. destruct H0 as [Hk Hr]. assert (0 < r)%nat by lia. apply lt_INR in H. simpl in H. apply lt_INR in Hk. simpl in Hk. assert (0 < k / r). apply Rdiv_lt_0_compat; easy. apply Rlt_le. apply Rmult_lt_0_compat; easy.
  } 
  rewrite <- IZR_IZN_INR by easy.
  pose (round_inequality (k / r * 2 ^ m)) as G. destruct G as [G0 G1].
  assert (/2 * /2^m < / (2 * N^2)).
  { assert (0 < N^2).
    { apply Rmult_lt_0_compat; lra.
    }
    rewrite Rinv_mult_distr by lra.
    apply Rmult_lt_compat_l. apply Rinv_0_lt_compat. lra.
    apply Rinv_lt_contravar. apply Rmult_lt_0_compat; easy.
    apply lt_INR in Hm1. do 2 rewrite pow_INR in Hm1. apply Hm1.
  }
  apply Rabs_def1.
  - apply Rmult_le_compat_r with (r:=/2^m) in G1.
    2:{ apply Rinv_0_lt_compat in PowM. lra.
    }
    rewrite Rmult_plus_distr_r in G1.
    replace (k / r * 2 ^ m * / 2 ^ m) with (k / r * (2 ^ m * / 2 ^ m)) in G1 by lra. rewrite Rinv_r in G1 by lra.
    apply Rle_lt_trans with (r2:=/ 2 * / 2 ^ m); lra.
  - apply Rmult_lt_compat_l with (r:=/2^m) in G0.
    2:{ apply Rinv_0_lt_compat. easy.
    }
    rewrite Rmult_minus_distr_l in G0.
    replace (/ 2 ^ m * (k / r * 2 ^ m)) with (/ 2^m * 2^m * (k / r)) in G0 by lra. rewrite Rinv_l in G0 by lra.
    apply Rlt_le_trans with (r2:=- /2 * /2^m); lra.
Qed.

Lemma CF_is_closest :
  forall a r N m n k,
    BasicSetting a r N m n ->
    (0 < k < r)%nat ->
    let (p, q) := ContinuedFraction (s_closest m k r) N m in
    Rabs ((s_closest m k r) / (2^m) - p / q) < 1 / (2 * N^2).
Admitted.

(* "Partial correct" of ContinuedFraction function. "Partial" because it is exactly correct only when k and r are coprime. Otherwise it will output (p, q) such that p/q=k/r. *)
Lemma ContinuedFraction_partial_correct :
  forall (a r N k m n : nat),
    BasicSetting a r N m n ->
    rel_prime k r ->
    ContinuedFraction (s_closest m k r) N m = (k, r).
Admitted.

Definition Rsum (n : nat) (f : nat -> R) : R := sum_f_R0 f (n - 1)%nat.

Definition prob_partial_meas {n} {m} x (ψ : Vector (2^(m + n))) :=
  Rsum (2^n) (fun y => probability_of_outcome ψ (basis_vector (2^m) x ⊗ basis_vector (2^n) y)).

(* The final success probability of Shor's order finding algorithm. It counts the k's coprime to r and their probability of being collaped to. *)
Definition probability_of_success (a r N m n : nat) (c : base_ucom n) :=
  Rsum (2^m) (fun x => if Shor_post x N m =? r then
                      prob_partial_meas x ((uc_eval (QPE m n c)) × ((basis_vector (2^m) 0) ⊗ (basis_vector (2^n) 1)))
                    else 0).

(* Euler's totient function *)
Definition ϕ (n : nat) := Rsum n (fun x => if rel_prime_dec x n then 1 else 0).

(* This might need to be treated as an axiom. [1979 Hardy & Wright, Thm 328] *)
Lemma ϕ_n_over_n_lowerbound :
  exists β, 
    β>0 /\
    forall (n : nat),
      2 < n ->
      (ϕ n) / n >= β / (Nat.log2 (Nat.log2 n)).
Admitted.

(* The correctness specification. It succeed with prob proportional to 1/(log log N), which is asymptotically small, but big enough in practice.
   With better technique (calculate the LCM of multiple outputs), the number of rounds may be reduced to constant. But I don't know how to specify that, and the analysis in Shor's original paper refers the correctness to "personal communication" with Knill. *)
Lemma Shor_correct :
  exists β, 
    β>0 /\
    forall (a r N m n : nat) (c : base_ucom n),
      BasicSetting a r N m n ->
      MultiplyCircuitProperty a N n c ->
      probability_of_success a r N m n c >= β / (Nat.log2 (Nat.log2 N)).
Admitted.

Require Import List.
Require Import Lia.
Require Import Coq.NArith.BinNatDef BinNat.
Require Coq.Program.Wf.

(* Definition of a record with a value and a property bound to it
that ensures that values of this type have less than 32 bits *)
Record uint32_t := {
  value :> N;
  H_uint32_size : N.size_nat value <= 32
}.

Program Definition uint32_t_0 := Build_uint32_t N.zero _.
Next Obligation.
lia.
Qed.
Program Definition uint32_t_1 := Build_uint32_t N.one _.
Next Obligation.
lia.
Qed.
Definition uint32_t_mod := N.shiftl N.one 32.

(* Definition of a record with a list of limbs and a number of limbs.
A property is also bound to each record ensuring that the length of the
list containing the limbs is equal to nlimbs *)
Record BigNum := {
  limbs :> list uint32_t;
  nlimbs :> nat;
  H_nlimbs_equal_to_limbs_length : length limbs = nlimbs
}.

Program Definition uint32_t_add (a b : uint32_t) : uint32_t :=
  let a_b_add := N.modulo (N.add (value a) (value b)) uint32_t_mod in
  Build_uint32_t a_b_add _.
Next Obligation. (* Need to prove that x mod 2^32 < 2^32 *)
admit.
Admitted.

Definition add_32_with_carry (a b : uint32_t)
                             : (uint32_t * uint32_t) :=
  let a_b_add := uint32_t_add a b in
  if (orb (N.ltb a_b_add a) (N.ltb a_b_add b)) then
    (a_b_add, uint32_t_1)
  else
    (a_b_add, uint32_t_0).

Program Fixpoint common_limbs (a_limbs b_limbs : list uint32_t)
                              (previous_loop_carry : uint32_t)
                              (H_len_limbs : length a_limbs = length b_limbs)
                              (H_carry : previous_loop_carry = uint32_t_0 \/ previous_loop_carry = uint32_t_1)
                              : (list uint32_t * uint32_t) :=
  match (a_limbs, b_limbs) with
  | (nil, nil) => (nil, previous_loop_carry)
  | (a_limb::a_l, b_limb::b_l) =>
    let (a_limb_with_carry, first_carry) := add_32_with_carry a_limb previous_loop_carry in
    let (new_limb, second_carry) := add_32_with_carry a_limb_with_carry b_limb in
    let loop_carry := N.lor first_carry second_carry in
    let (new_limbs, final_carry) := common_limbs a_l b_l (Build_uint32_t loop_carry _) _ _ in
    (new_limb::new_limbs, Build_uint32_t final_carry _)
  | (_, _) => False_rect _ _
  end.
Next Obligation. (* Need to prove that first_carry | second_carry < 2^32 *)
admit.
Admitted.
Next Obligation. (* Need to prove that carry = 0 \/ carry = 1 *)
admit.
Admitted.
Next Obligation. (* Need to prove that final_carry < 2^32 *)
admit.
Admitted.
Next Obligation.
case_eq a_limbs; case_eq b_limbs.
intros.
- rewrite H1 in H0.
  rewrite H2 in H0.
  contradict H0.
  reflexivity.
- intros.
  rewrite H2 in H0.
  rewrite H2 in *.
  contradict H_len_limbs.
  rewrite H1.
  simpl.
  trivial.
- intros.
  rewrite H2 in H_len_limbs.
  rewrite H1 in H_len_limbs.
  contradict H_len_limbs.
  simpl.
  congruence.
- intros.
  specialize (H u0 l0 u l).
  rewrite H2 in H.
  rewrite H1 in H.
  contradict H.
  reflexivity.
Qed.

Next Obligation.
split.
- intros.
  injection.
  inversion H.
- injection.
  inversion H.
Qed.

Next Obligation.
split.
- intros.
  injection.
  inversion H.
- injection.
  inversion H.
Qed.

Fixpoint remaining_limbs(rem_a_limbs : list uint32_t) (previous_loop_carry : uint32_t)
                        : (list uint32_t * uint32_t) :=
  match rem_a_limbs with
  | nil => (nil, previous_loop_carry)
  | a_limb::a_l =>
    let (a_limb_with_carry, first_carry) := add_32_with_carry a_limb previous_loop_carry in
    let (new_limbs, final_carry) := remaining_limbs a_l first_carry in
    (a_limb_with_carry::new_limbs, final_carry)
  end.

Program Definition __BigNum_Add__ (a b : BigNum)
                                  (H_a_ge_b_nlimbs : (nlimbs a) >= (nlimbs b))
                                  : BigNum :=
  let previous_loop_carry := uint32_t_0 in
  let a_ls_limbs := List.firstn (nlimbs b) (limbs a) in
  let (ls_limbs, carry) := common_limbs a_ls_limbs (limbs b) previous_loop_carry _ _ in
  let a_ms_limbs := List.skipn (nlimbs b) (limbs a) in
  let (ms_limbs, overflow) := remaining_limbs a_ms_limbs carry in
  if (BinNat.N.eq_dec overflow uint32_t_1) then
    let new_limbs := ls_limbs ++ ms_limbs ++ (cons overflow nil) in
    Build_BigNum new_limbs ((nlimbs a) + 1) _
  else
    let new_limbs := ls_limbs ++ ms_limbs in
    Build_BigNum new_limbs (nlimbs a) _.
Next Obligation.
assert (forall b : BigNum, length (limbs b) = nlimbs b) as H_limbs_len
       by apply H_nlimbs_equal_to_limbs_length.
rewrite (H_limbs_len b).
apply firstn_length_le.
rewrite (H_limbs_len a).
lia.
Qed.

Next Obligation. (* Need to prove that length (ls_limbs ++ ms_limbs ++ overflow) = (nlimbs a) + 1 *)
admit.
Admitted.

Next Obligation. (* Need to prove that length (ls_limbs ++ ms_limbs) = nlimbs a *)
admit.
Admitted.

Program Definition BigNum_Add(a b : BigNum) : BigNum :=
  if (Compare_dec.ge_dec (nlimbs a) (nlimbs b)) then
    __BigNum_Add__ a b _
  else
    __BigNum_Add__ b a _.
Next Obligation.
lia.
Qed.

Program Fixpoint BigNum_cons_aux (n_bin : N)  {measure (N.to_nat n_bin)} : list uint32_t :=
  match n_bin with
  | N0     => nil
  | _ as n =>
    let (div, rem) := N.div_eucl n uint32_t_mod in
    let u32_rem := Build_uint32_t rem _ in
    let uint32_t_list := BigNum_cons_aux div in
    u32_rem::uint32_t_list
  end.
Next Obligation. (* Need to prove again that x mod 2^32 < 2^32 *)
admit.
Admitted.
Next Obligation. (* Need to prove that the recursive call argument is decreasing for Coq *)
admit.
Admitted.

Program Definition BigNum_cons (n : nat) : BigNum :=
  let n_bin := N.of_nat(n) in
  let limbs := BigNum_cons_aux n_bin in
  Build_BigNum limbs (length limbs) _.

Lemma BigNum_Nat_Equiv : forall (a b c : nat), (Nat.add a b) = c <->
                         BigNum_Add (BigNum_cons a) (BigNum_cons b) = (BigNum_cons c).
Proof.
admit.
Admitted.

Lemma uint32_t_add_res_ge_args : forall a b c : nat,
                                 forall a_u32 b_u32 a_b_add : uint32_t,
                                 value a_u32 = N.of_nat a
                              -> value b_u32 = N.of_nat b
                              -> c = a + b
                              -> a_b_add = uint32_t_add a_u32 b_u32
                              -> c < N.to_nat uint32_t_mod
                              -> N.ge (value a_b_add) (value a_u32)
                              /\ N.ge (value a_b_add) (value b_u32).
Proof.
admit.
Admitted.

Lemma uint32_t_add_res_lt_args : forall a b c : nat,
                                 forall a_u32 b_u32 a_b_add : uint32_t,
                                 value a_u32 = N.of_nat a
                              -> value b_u32 = N.of_nat b
                              -> c = a + b
                              -> a_b_add = uint32_t_add a_u32 b_u32
                              -> c >= N.to_nat uint32_t_mod
                              -> N.lt (value a_b_add) (value a_u32)
                              \/ N.lt (value a_b_add) (value b_u32).
Proof.
intros.
unfold uint32_t_add in H2.
admit.
Admitted.

Lemma add_32_with_carry_spec : forall a b c : nat,
                               forall a_u32 b_u32 c_u32 carry : uint32_t,
                               (value a_u32) = N.of_nat a
                            -> (value b_u32) = N.of_nat b
                            -> c = a + b
                            -> c_u32 = uint32_t_add a_u32 b_u32
                            -> add_32_with_carry a_u32 b_u32 = (c_u32, carry)
                            -> (c < N.to_nat uint32_t_mod
                                -> carry = uint32_t_0)
                            /\ (c >= N.to_nat uint32_t_mod
                                -> carry = uint32_t_1).
Proof.
intros a b c a_u32 b_u32 c_u32 carry.
intros H_a_u32 H_b_u32 H_c H_c_u32.
intro H_add_32_with_carry.
split; intros H_cmp;
unfold add_32_with_carry in H_add_32_with_carry;
rewrite H_c_u32 in H_add_32_with_carry;
rewrite <- H_c_u32 in H_add_32_with_carry;
destruct (orb (N.ltb c_u32 a_u32) (N.ltb c_u32 b_u32)) as []eqn:?.
- contradict Heqb0.
  apply Bool.not_true_iff_false.
  apply Bool.orb_false_intro;
  apply N.ltb_ge;
  pose proof uint32_t_add_res_ge_args as H_args_lt_sum;
  destruct (H_args_lt_sum a b c a_u32 b_u32 c_u32) as [H_a_u32_lt_sum H_b_u32_lt_sum];
  try assumption; lia.
- symmetry.
  inversion H_add_32_with_carry.
  reflexivity.
- symmetry.
  inversion H_add_32_with_carry.
  reflexivity.
- contradict Heqb0.
  apply Bool.not_false_iff_true.
  apply Bool.orb_true_intro.
  repeat rewrite N.ltb_lt.
  pose proof uint32_t_add_res_lt_args as H_sum_lt_args.
  apply (H_sum_lt_args a b c a_u32 b_u32 c_u32); assumption.
Qed.

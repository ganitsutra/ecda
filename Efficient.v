Require Export Coq.MSets.MSetInterface.
From Coq Require Import OrderedType.
Require Export OTypes.
Require Export RBT.
Require Export Programs.
Require Export Definitions.
Require Export Properties.
Require Import UniqueMatch.
Require Import Programs.



Require Import Coq.Logic.Eqdep_dec Coq.Arith.Compare_dec Coq.Arith.PeanoNat.

Inductive color := Red | Black.
Module Color.
 Definition t := color.
End Color.


Module TB. Include MakeRaw OrderedB. End TB.
Include Raw2Sets OrderedB TB.


Module TA. Include MakeRaw OrderedA. End TA.
Module T_id. Include MakeRaw Ordered_id. End T_id.

Definition Bt (p: (TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)) := 
match p with (x, y, x_id, y_id, z) => x end.
Definition At (p: (TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)) := 
match p with (x, y, x_id, y_id, z) => y end.
Definition Mt (p: (TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)) := 
match p with (x, y, x_id, y_id, z) => z end.
Definition Bt_id (p: (TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)) := 
match p with (x, y, x_id, y_id, z) => x_id end.
Definition At_id (p: (TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)) := 
match p with (x, y, x_id, y_id, z) => y_id end.

Lemma perm_In2 (l1 l2:list order)(a:order):
perm l1 l2 -> List.In a l1 -> List.In a l2.
Proof. intros. apply perm_elim2 in H.
unfold "[=]" in H. destruct H. eauto. Qed. 

Hint Immediate perm_In2 :ecda.

(*
Lemma len_make (t1: TB.tree):
TB.cardinal (TB.makeBlack t1) = TB.cardinal t1.
Proof. induction t1. simpl. auto. simpl. lia. Qed.

Lemma len_eq (t1 t2: TB.tree):
t1 = t2 -> TB.cardinal t1 = TB.cardinal t2.
Proof. revert t1. induction t2. simpl. intros.
rewrite H. simpl. auto. intros. subst t2.
simpl. auto. Qed.
*)
Lemma min_elt_in_list (B: list order)(b:order):
TB.min_elt (TB.treeify B) = Some b -> InA OTypes.eqcompetitive b B.
Proof. intros. induction B. simpl in H. inversion H.
apply TB.min_elt_spec1 in H. apply TB.treeify_spec in H.
auto. Qed.

Hint Immediate min_elt_in_list :ecda.


Lemma In_elementsB (B:TB.t)(a:TB.elt):
List.In a (TB.elements B) -> TB.InT a B.
Proof. induction B.
  { intros. inversion H. }
  { unfold TB.elements. simpl.
      rewrite TB.elements_app. rewrite TB.elements_app.
      rewrite <- app_nil_end. intros.
      apply in_app_iff in H. simpl in H.
      destruct H. apply TB.InLeft. apply IHB1.
      auto. destruct H. apply TB.IsRoot.
      subst a. unfold eqcompetitive. split. apply /eqP;auto. 
      apply /eqP;auto. apply TB.InRight. apply IHB2.
      auto. 
    } Qed.

Lemma In_elementsA (B:TA.t)(a:TA.elt):
List.In a (TA.elements B) -> TA.InT a B.
Proof. induction B.
  { intros. inversion H. }
  { unfold TA.elements. simpl.
      rewrite TA.elements_app. rewrite TA.elements_app.
      rewrite <- app_nil_end. intros.
      apply in_app_iff in H. simpl in H.
      destruct H. apply TA.InLeft. apply IHB1.
      auto. destruct H. apply TA.IsRoot.
      subst a. unfold eqcompetitive. split. apply /eqP;auto. 
      apply /eqP;auto. apply TA.InRight. apply IHB2.
      auto. 
    } Qed.
    
Lemma In_elements_id (B:T_id.t)(a:T_id.elt):
List.In a (T_id.elements B) -> T_id.InT a B.
Proof. induction B.
  { intros. inversion H. }
  { unfold T_id.elements. simpl.
      rewrite T_id.elements_app. rewrite T_id.elements_app.
      rewrite <- app_nil_end. intros.
      apply in_app_iff in H. simpl in H.
      destruct H. apply T_id.InLeft. apply IHB1.
      auto. destruct H. apply T_id.IsRoot.
      subst a. apply /eqP. auto. 
      apply T_id.InRight. apply IHB2.
      auto. 
    } Qed.

Hint Immediate In_elements_id In_elementsB In_elementsA :ecda.

Lemma max_elt_in_listB (B:TB.t)(e:TB.elt):
TB.max_elt B = Some e -> List.In e (TB.elements B).
Proof. induction B. intros H. inversion H. intros H. simpl in H.
destruct B2 eqn: HB. simpl in H. rewrite TB.elements_node.
apply in_app_iff. right. simpl. left. inversion H. auto. apply IHB2 in H.
rewrite <- HB. rewrite <- HB in H. 
rewrite TB.elements_node. apply in_app_iff. right.
simpl. right. exact H. Qed.

Lemma max_elt_in_listA (B:TA.t)(e:TA.elt):
TA.max_elt B = Some e -> List.In e (TA.elements B).
Proof. induction B. intros H. inversion H. intros H. simpl in H.
destruct B2 eqn: HB. simpl in H. rewrite TA.elements_node.
apply in_app_iff. right. simpl. left. inversion H. auto. apply IHB2 in H.
rewrite <- HB. rewrite <- HB in H. 
rewrite TA.elements_node. apply in_app_iff. right.
simpl. right. exact H. Qed.

Lemma max_elt_in_list_id (B:T_id.t)(e:T_id.elt):
T_id.max_elt B = Some e -> List.In e (T_id.elements B).
Proof. induction B. intros H. inversion H. intros H. simpl in H.
destruct B2 eqn: HB. simpl in H. rewrite T_id.elements_node.
apply in_app_iff. right. simpl. left. inversion H. auto. apply IHB2 in H.
rewrite <- HB. rewrite <- HB in H. 
rewrite T_id.elements_node. apply in_app_iff. right.
simpl. right. exact H. Qed.

Hint Immediate max_elt_in_list_id max_elt_in_listB max_elt_in_listA :ecda.

Lemma max_elt_equal_list_maxB (B:TB.t)(e:TB.elt)(b:order)(B0:list order):
TB.Ok B -> NoDup (timesof (b::B0)) -> perm (TB.elements B) (b :: B0) -> TB.max_elt B = Some e
-> Sorted Properties.bcompetitive (b :: B0) -> e = b.
Proof. intros ok1 ndp H H0 H1.  apply max_elt_in_listB in H0 as Hb.
assert(Hl:List.In e (b :: B0)). eapply perm_In2. auto. auto.
simpl in Hl. destruct Hl. auto. 
apply Sorted_elim2 with (x:=e) in H1 as He.
apply TB.max_elt_spec2 with (y:=b) in H0 as H3.
destruct H3. split. unfold OTypes.bcompetitive.
unfold bcompetitive in He. move /orP in He.
destruct He. left. unfold Nat.lt. move /ltP in H3. auto.
right. move /andP in H3. destruct H3. move /eqP in H3.
move /leP in H4. auto. intro. 
unfold OTypes.eqcompetitive in H3. simpl in ndp. apply nodup_elim2 in ndp.
apply timesof_elim in H2. destruct H3. 
move /eqP in H4. rewrite H4 in H2. destruct (ndp H2). auto. 
apply perm_elim2 in H. 
unfold "[=]" in H. destruct H. assert(List.In b (TB.elements B)).
eauto. auto with ecda. unfold reflexive. unfold Properties.bcompetitive. intros. apply /orP. right. apply /andP. split. auto. auto. simpl.  auto. Qed.

Lemma max_elt_equal_list_minA (B:TA.t)(e:TA.elt)(b:order)(B0:list order):
TA.Ok B -> NoDup (timesof (b::B0)) -> perm (TA.elements B) (b :: B0) -> TA.max_elt B = Some e
-> Sorted Properties.acompetitive (b :: B0) -> e = b.
Proof. intros ok1 ndp H H0 H1. apply max_elt_in_listA in H0 as Hb.
assert(Hl:List.In e (b :: B0)). eapply perm_In2. auto. auto.
simpl in Hl. destruct Hl. auto. 
apply Sorted_elim2 with (x:=e) in H1 as He.
apply TA.max_elt_spec2 with (y:=b) in H0 as H3.
destruct H3. split. unfold OTypes.acompetitive.
unfold bcompetitive in He. move /orP in He.
destruct He. left. unfold Nat.lt. move /ltP in H3. auto.
right. move /andP in H3. destruct H3. move /eqP in H3.
move /leP in H4. auto. intro. 
unfold OTypes.eqcompetitive in H3. simpl in ndp. apply nodup_elim2 in ndp.
apply timesof_elim in H2. destruct H3. 
move /eqP in H4. rewrite H4 in H2. destruct (ndp H2). auto. 
apply perm_elim2 in H. 
unfold "[=]" in H. destruct H. assert(List.In b (TA.elements B)).
eauto. auto with ecda. unfold reflexive. unfold Properties.acompetitive. intros. apply /orP. right. apply /andP. split. auto. auto. simpl.  auto. Qed.

Hint Immediate max_elt_equal_list_minA max_elt_equal_list_maxB :ecda.

Lemma NoDupA_intro (l:list order)(a:order)(f:order -> order -> Prop):
Equivalence f -> f a a  -> NoDupA f (a :: l) -> ~List.In a l.
Proof. induction l. intuition. intro E. intros. intro. destruct H1. subst. 
inversion H0. subst. destruct H3. intuition. 
replace (a :: a0 :: l) with (a::nil ++ a0::l) in H. 
apply NoDupA_swap with (l:=a::nil) in H0. simpl in H0.
apply NoDupA_split with (l:=nil) in H0. simpl in H0.
apply IHl in H0. destruct (H0 H1). auto. auto. auto. 
simpl. auto. Qed.

Lemma NoDupA_NoDup (l:list order)(f:order -> order -> Prop): 
Equivalence f -> (forall a, f a a) -> NoDupA f l -> NoDup l. 
Proof. induction l. intuition. intuition.
  - apply nodup_intro. intuition. apply NoDupA_intro in H1.
    destruct (H1 H2). auto.  auto. apply H3. apply NoDupA_split with (l:=nil) in H1.
    simpl in H1. auto. Qed.


Lemma nodup_conflict_specB s x y `{TB.Ok s} :
TB.Intree x s -> TB.Intree y s -> OTypes.eqcompetitive x y-> x=y .
Proof.
induction s. 
- TB.intuition_in_tree.
-  TB.intuition_in_tree. 
  * unfold TB.lt_tree in H9. specialize (H9 x). apply TB.Intree_InT in H1.
    apply H9 in H1. destruct H1. destruct(H1 H2).
  * unfold TB.lt_tree in H10. specialize (H10 x). apply TB.Intree_InT in H1.
    apply H10 in H1. destruct H1. apply OrderedB.eq_sym in H2. destruct(H1 H2).
  * unfold TB.lt_tree in H9. specialize (H9 y). apply TB.Intree_InT in H3.
    apply H9 in H3. destruct H3. apply OrderedB.eq_sym in H2. destruct(H3 H2).
  * unfold TB.gt_tree in H10. unfold TB.lt_tree in H9. specialize (H10 x). 
    specialize (H9 y). apply TB.Intree_InT in H3. apply TB.Intree_InT in H1.
    apply H9 in H3. apply H10 in H1. destruct H3. destruct H1. 
    unfold OTypes.eqcompetitive in H2. destruct H2. move /eqP in H2.
    move /eqP in H6. unfold OTypes.bcompetitive in H1, H0. destruct H1;destruct H0.
      + lia.
      + lia.
      + lia.
      + unfold OTypes.eqcompetitive in H3, H5. destruct H3. split. apply /eqP. lia.
         apply /eqP. lia.
  * unfold TB.gt_tree in H10. specialize (H10 y). apply TB.Intree_InT in H3.
    apply H10 in H3. destruct H3.  destruct(H3 H2).
  * unfold TB.gt_tree in H10. unfold TB.lt_tree in H9. specialize (H10 y). 
    specialize (H9 x). apply TB.Intree_InT in H3. apply TB.Intree_InT in H1.
    apply H10 in H3. apply H9 in H1. destruct H3. destruct H1. 
    unfold OTypes.eqcompetitive in H2. destruct H2. move /eqP in H2.
    move /eqP in H6. unfold OTypes.bcompetitive in H1, H. destruct H1;destruct H.
      + lia.
      + lia.
      + lia.
      + unfold OTypes.eqcompetitive in H3, H5. destruct H3. split. apply /eqP. lia.
         apply /eqP. lia.
Qed.

Lemma nodup_conflict_specA s x y `{TA.Ok s} :
TA.Intree x s -> TA.Intree y s -> OTypes.eqcompetitive x y-> x=y.
Proof. 
induction s. 
- TA.intuition_in_tree.
-  TA.intuition_in_tree. 
  * unfold TA.lt_tree in H9. specialize (H9 x). apply TA.Intree_InT in H1.
    apply H9 in H1. destruct H1. destruct(H1 H2).
  * unfold TA.lt_tree in H10. specialize (H10 x). apply TA.Intree_InT in H1.
    apply H10 in H1. destruct H1. apply OrderedB.eq_sym in H2. destruct(H1 H2).
  * unfold TA.lt_tree in H9. specialize (H9 y). apply TA.Intree_InT in H3.
    apply H9 in H3. destruct H3. apply OrderedB.eq_sym in H2. destruct(H3 H2).
  * unfold TA.gt_tree in H10. unfold TA.lt_tree in H9. specialize (H10 x). 
    specialize (H9 y). apply TA.Intree_InT in H3. apply TA.Intree_InT in H1.
    apply H9 in H3. apply H10 in H1. destruct H3. destruct H1. 
    unfold OTypes.eqcompetitive in H2. destruct H2. move /eqP in H2.
    move /eqP in H6. unfold OTypes.bcompetitive in H1, H0. destruct H1;destruct H0.
      + lia.
      + lia.
      + lia.
      + unfold OTypes.eqcompetitive in H3, H5. destruct H3. split. apply /eqP. lia.
         apply /eqP. lia.
  * unfold TA.gt_tree in H10. specialize (H10 y). apply TA.Intree_InT in H3.
    apply H10 in H3. destruct H3.  destruct(H3 H2).
  * unfold TA.gt_tree in H10. unfold TA.lt_tree in H9. specialize (H10 y). 
    specialize (H9 x). apply TA.Intree_InT in H3. apply TA.Intree_InT in H1.
    apply H10 in H3. apply H9 in H1. destruct H3. destruct H1. 
    unfold OTypes.eqcompetitive in H2. destruct H2. move /eqP in H2.
    move /eqP in H6. unfold OTypes.bcompetitive in H1, H. destruct H1;destruct H.
      + lia.
      + lia.
      + lia.
      + unfold OTypes.eqcompetitive in H3, H5. destruct H3. split. apply /eqP. lia.
         apply /eqP. lia.
Qed.


Lemma nodup_conflict_spec_id s x y `{T_id.Ok s} :
T_id.Intree x s -> T_id.Intree y s -> Ordered_id.eq x y-> x=y.
Proof. induction s. 
- T_id.intuition_in_tree.
-  T_id.intuition_in_tree. 
  * unfold T_id.lt_tree in H9. specialize (H9 x). apply T_id.Intree_InT in H1.
    apply H9 in H1. unfold Ordered_id.eq in H2. lia.
  * unfold T_id.lt_tree in H10. specialize (H10 x). apply T_id.Intree_InT in H1.
    apply H10 in H1. unfold Ordered_id.eq in H2. lia.
  * unfold T_id.lt_tree in H9. specialize (H9 y). apply T_id.Intree_InT in H3.
    apply H9 in H3. unfold Ordered_id.eq in H2. lia.
  * unfold T_id.gt_tree in H10. unfold T_id.lt_tree in H9. specialize (H10 x). 
    specialize (H9 y). apply T_id.Intree_InT in H3. apply T_id.Intree_InT in H1.
    apply H9 in H3. apply H10 in H1. unfold Ordered_id.eq in H2. lia.
  * unfold T_id.gt_tree in H10. specialize (H10 y). apply T_id.Intree_InT in H3.
    apply H10 in H3. unfold Ordered_id.eq in H2. lia. 
  * unfold T_id.gt_tree in H10. unfold T_id.lt_tree in H9. specialize (H10 y). 
    specialize (H9 x). apply T_id.Intree_InT in H3. apply T_id.Intree_InT in H1.
    apply H10 in H3. apply H9 in H1.  unfold Ordered_id.eq in H2. lia.
Qed.



Lemma count_treeB (B1:TB.t)(a:TB.elt):
TB.Ok B1 -> count a (TB.elements B1) = 1 \/ count a (TB.elements B1) = 0.
Proof. intros H0. 
 assert(NoDupA OTypes.eqcompetitive (TB.elements B1)).
 apply TB.elements_spec2w. auto. apply NoDupA_NoDup in H as H1.
 apply nodup_count with (x:=a) in H1. lia. apply OrderedB.eq_equiv. 
    apply OrderedB.eq_refl. Qed.

Lemma count_tree_id (B1:T_id.t)(a:T_id.elt):
T_id.Ok B1 -> count a (T_id.elements B1) = 1 \/ count a (T_id.elements B1) = 0.
Proof. intros H0. 
 assert(NoDupA Ordered_id.eq (T_id.elements B1)).
 apply T_id.elements_spec2w. auto. apply NoDupA_NoDup in H as H1.
 apply nodup_count with (x:=a) in H1. lia. apply Ordered_id.eq_equiv. 
 apply Ordered_id.eq_refl. Qed.
 
Lemma count_treeA (A1:TA.t)(a:TA.elt):
TA.Ok A1 -> count a (TA.elements A1) = 1 \/ count a (TA.elements A1) = 0.
Proof. intros H0. 
 assert(NoDupA OrderedA.eq (TA.elements A1)).
 apply TA.elements_spec2w. auto. apply NoDupA_NoDup in H as H1.
 apply nodup_count with (x:=a) in H1. lia. apply OrderedA.eq_equiv. 
 apply OrderedA.eq_refl. Qed.
 
Lemma count_IntreeB s x`{TB.Ok s} :
TB.Intree x s <-> count x (TB.elements s) = 1.
Proof. split. 
    - intros H1. destruct (count_treeB s x ). auto. auto.
      apply TB.elements_spec_tree in H1. apply countP1 in H1.
      lia.
    - intros H1. assert(H2: count x (TB.elements s) >= 1).
      lia. apply countP1a in H2. apply TB.elements_spec_tree in H2. auto.
Qed.


Lemma count_Intree_id s x`{T_id.Ok s} :
T_id.Intree x s <-> count x (T_id.elements s) = 1.
Proof. split. 
    - intros H1. destruct (count_tree_id s x ). auto. auto.
      apply T_id.elements_spec_tree in H1. apply countP1 in H1.
      lia.
    - intros H1. assert(H2: count x (T_id.elements s) >= 1).
      lia. apply countP1a in H2. apply T_id.elements_spec_tree in H2. auto.
Qed.

Lemma count_IntreeA s x`{TA.Ok s} :
TA.Intree x s <-> count x (TA.elements s) = 1.
Proof. split. 
    - intros H1. destruct (count_treeA s x ). auto. auto.
      apply TA.elements_spec_tree in H1. apply countP1 in H1.
      lia.
    - intros H1. assert(H2: count x (TA.elements s) >= 1).
      lia. apply countP1a in H2. apply TA.elements_spec_tree in H2. auto.
Qed.

Hint Immediate count_IntreeA count_Intree_id count_IntreeB :ecda.
Hint Immediate count_treeA count_tree_id count_treeB :ecda.

(*
Lemma Intree_decB  s y :
~TB.Intree y s\/TB.Intree y s.
Proof. intros. assert((List.In y (TB.elements s))\/(~List.In y (TB.elements s))).
eauto.  destruct H. right. apply TB.elements_spec_tree. auto. left. intro.  
apply TB.elements_spec_tree in H0. destruct H. auto.
 Qed.

Lemma Intree_decA  s y :
~TA.Intree y s\/TA.Intree y s.
Proof. intros. assert((List.In y (TA.elements s))\/(~List.In y (TA.elements s))).
eauto.  destruct H. right. apply TA.elements_spec_tree. auto. left. intro.  
apply TA.elements_spec_tree in H0. destruct H. auto.
 Qed.

Lemma Intree_dec_id  s y :
~T_id.Intree y s\/T_id.Intree y s.
Proof. intros. assert((List.In y (T_id.elements s))\/(~List.In y (T_id.elements s))).
eauto.  destruct H. right. apply T_id.elements_spec_tree. auto. left. intro.  
apply T_id.elements_spec_tree in H0. destruct H. auto.
 Qed.

 
Lemma remove_treeB (B1:TB.t)(a b:TB.elt):
TB.Ok B1 -> count a (TB.elements (TB.remove b B1))  = 1 ->
count a (TB.elements B1) = 1.
Proof. intros. apply count_IntreeB in H0. apply TB.remove_spec_tree in H0.
destruct H0. apply count_IntreeB in H0. auto. auto. auto. apply TB.remove_ok.
auto. Qed.
*)

Lemma perm_remove_treeB (B:TB.t)(b:TB.elt)(B_id:T_id.t):
T_id.Ok B_id -> TB.Ok B -> List.In b (TB.elements B) ->
perm (TB.elements B) (T_id.elements B_id) ->
perm (TB.elements (TB.remove b B)) (T_id.elements (T_id.remove b B_id)).
Proof. intros okB1 okB2 H0 H.
assert(Hperm:=H). apply perm_intro. intros a. 
apply perm_elim with (a0:=a) in H. 
destruct (ord_eqb a b) eqn:Hab. 
- move /eqP in Hab. subst. 
  destruct (count_tree_id (T_id.remove b B_id) b) as [H1 | H1];
  destruct (count_treeB (TB.remove b B) b) as [H2 | H2].
  apply TB.remove_ok;auto. apply T_id.remove_ok;auto.
  apply T_id.remove_ok;auto. apply TB.remove_ok;auto.
  lia. apply count_Intree_id in H1;auto. apply T_id.remove_spec_tree in H1.
  destruct H1. destruct H3. lia. all:auto. apply T_id.remove_ok;auto. 
  apply TB.remove_ok;auto.  
  apply count_IntreeB in H2;auto. apply TB.remove_spec_tree in H2.
  destruct H2. destruct H3. unfold OTypes.eqcompetitive. auto. all:auto. apply
  TB.remove_ok;auto. lia.
- move /eqP in Hab. destruct (count_treeB B a) as [H2 | H2];
  destruct (count_tree_id B_id a) as [H3 | H3].  all:auto.
   + apply count_IntreeB in H2;auto. apply count_Intree_id in H3;auto.
      assert(H1:List.In b (T_id.elements B_id)).  apply perm_elim2 in Hperm. 
      unfold "[=]" in Hperm. destruct Hperm. eauto.
      apply T_id.elements_spec_tree in H1.
      apply TB.elements_spec_tree in H0. 
      destruct (count_treeB (TB.remove b B) a) as [H4 | H4]. 
      apply TB.remove_ok;auto.
      * destruct (count_tree_id (T_id.remove b B_id) a) as [H5 | H5]. 
      apply T_id.remove_ok;auto. lia. apply countP3 in H5. destruct H5. 
      apply T_id.elements_spec_tree. apply T_id.remove_spec_tree. auto. 
      split. auto. intro Hc. apply nodup_conflict_spec_id with (s:=B_id) in Hc.
      all:auto.
      * destruct (count_treeB (TB.remove b B) a) as [H5 | H5]. 
      apply TB.remove_ok;auto. lia. apply countP3 in H5. destruct H5. 
      apply TB.elements_spec_tree. apply TB.remove_spec_tree. auto. 
      split. auto. intro Hc. apply nodup_conflict_specB with (s:=B) in Hc.
      all:auto.
   + lia.
   + lia.
   + assert(H1:List.In b (T_id.elements B_id)).  apply perm_elim2 in Hperm. 
      unfold "[=]" in Hperm. destruct Hperm. eauto. 
      apply T_id.elements_spec_tree in H1.
      apply TB.elements_spec_tree in H0. 
      destruct (count_treeB (TB.remove b B) a) as [H4 | H4].
      apply TB.remove_ok;auto.
      * apply count_IntreeB in H4. apply TB.remove_spec_tree in H4.
        destruct H4. 
       apply countP3 in H2. apply TB.elements_spec_tree in H4.
       destruct (H2 H4).
       all:auto.  apply TB.remove_ok;auto. 
      * rewrite H4. symmetry. apply countP2. intro Hc.
        apply T_id.elements_spec_tree in Hc.
        apply T_id.remove_spec_tree in Hc. destruct Hc as [Hc H6].  
        apply T_id.elements_spec_tree in Hc. apply countP3 in H3.
        destruct (H3 Hc).  all:auto. 
Qed.


Lemma perm_remove_treeA (A:TA.t)(a:TA.elt)(A_id:T_id.t):
T_id.Ok A_id -> TA.Ok A -> List.In a (TA.elements A) ->
perm (TA.elements A) (T_id.elements A_id) ->
perm (TA.elements (TA.remove a A)) (T_id.elements (T_id.remove a A_id)).
Proof. intros okA1 okA2 H0 H.
assert(Hperm:=H). apply perm_intro. intros b. 
apply perm_elim with (a0:=b) in H. 
destruct (ord_eqb b a) eqn:Hab. 
- move /eqP in Hab. subst. 
  destruct (count_tree_id (T_id.remove a A_id) a) as [H1 | H1];
  destruct (count_treeA (TA.remove a A) a) as [H2 | H2].
  apply TA.remove_ok;auto. apply T_id.remove_ok;auto.
  apply T_id.remove_ok;auto. apply TA.remove_ok;auto.
  lia. apply count_Intree_id in H1;auto. apply T_id.remove_spec_tree in H1.
  destruct H1. destruct H3. lia. all:auto. apply T_id.remove_ok;auto. 
  apply TA.remove_ok;auto.  
  apply count_IntreeA in H2;auto. apply TA.remove_spec_tree in H2.
  destruct H2. destruct H3. unfold OTypes.eqcompetitive. auto. all:auto. apply
  TA.remove_ok;auto. lia.
- move /eqP in Hab. destruct (count_treeA A b) as [H2 | H2];
  destruct (count_tree_id A_id b) as [H3 | H3].  all:auto.
   + apply count_IntreeA in H2;auto. apply count_Intree_id in H3;auto.
      assert(H1:List.In a (T_id.elements A_id)).  apply perm_elim2 in Hperm. 
      unfold "[=]" in Hperm. destruct Hperm. eauto.
      apply T_id.elements_spec_tree in H1.
      apply TA.elements_spec_tree in H0. 
      destruct (count_treeA (TA.remove a A) b) as [H4 | H4]. 
      apply TA.remove_ok;auto.
      * destruct (count_tree_id (T_id.remove a A_id) b) as [H5 | H5]. 
      apply T_id.remove_ok;auto. lia. apply countP3 in H5. destruct H5. 
      apply T_id.elements_spec_tree. apply T_id.remove_spec_tree. auto. 
      split. auto. intro Hc. apply nodup_conflict_spec_id with (s:=A_id) in Hc.
      all:auto.
      * destruct (count_treeA (TA.remove a A) b) as [H5 | H5]. 
      apply TA.remove_ok;auto. lia. apply countP3 in H5. destruct H5. 
      apply TA.elements_spec_tree. apply TA.remove_spec_tree. auto. 
      split. auto. intro Hc. apply nodup_conflict_specA with (s:=A) in Hc.
      all:auto.
   + lia.
   + lia.
   + assert(H1:List.In a (T_id.elements A_id)).  apply perm_elim2 in Hperm. 
      unfold "[=]" in Hperm. destruct Hperm. eauto. 
      apply T_id.elements_spec_tree in H1.
      apply TA.elements_spec_tree in H0. 
      destruct (count_treeA (TA.remove a A) b) as [H4 | H4].
      apply TA.remove_ok;auto.
      * apply count_IntreeA in H4. apply TA.remove_spec_tree in H4.
        destruct H4. 
       apply countP3 in H2. apply TA.elements_spec_tree in H4.
       destruct (H2 H4).
       all:auto.  apply TA.remove_ok;auto. 
      * rewrite H4. symmetry. apply countP2. intro Hc.
        apply T_id.elements_spec_tree in Hc.
        apply T_id.remove_spec_tree in Hc. destruct Hc as [Hc H6].  
        apply T_id.elements_spec_tree in Hc. apply countP3 in H3.
        destruct (H3 Hc).  all:auto. 
Qed.

Lemma perm_remove_tree_delete_order_id (A:T_id.t)(b:T_id.elt)(A0:list order):
T_id.Ok A -> List.In b (T_id.elements A) -> perm (T_id.elements A) A0 -> perm (T_id.elements (T_id.remove b A)) (delete_order A0 (id b)).
Proof. intros ok1 H H0. apply perm_intro. intros. 
         assert(H1:List.In a (T_id.elements A)\/~List.In a (T_id.elements A)).
         eauto. destruct H1 as [H1 | H1].
      { assert(Hperm:=H0). 
         apply perm_elim with (a0:=a) in H0. 
         destruct (ord_eqb b a) eqn:Hab. 
         { move /eqP in Hab. subst. apply T_id.elements_spec_tree in H. 
           apply count_Intree_id in H;auto. 
           rewrite H in H0. symmetry in H0.
           assert(H2:count a A0 >= 1). lia.
           apply countP1a in H2. 
           destruct (count_tree_id (T_id.remove a A) a) as [H4 | H4].
           apply T_id.remove_ok.
           auto. rewrite H4. apply count_Intree_id in H4;auto. symmetry. 
           apply (T_id.remove_spec_tree A a a) in H4. destruct H4. destruct H4.
           unfold Nat.eq. auto. apply T_id.remove_ok. auto.
           rewrite H4. symmetry. 
                      apply delete_order_count_eq.
         } 
         { move /eqP in Hab. 
           destruct (count_tree_id (T_id.remove b A) a) as [H4 | H4].
           apply T_id.remove_ok. auto. 
           rewrite H4. apply count_Intree_id in H4;auto. symmetry.
           rewrite delete_order_count_neq. intro. destruct Hab.
           apply nodup_conflict_spec_id with (s:=A). auto.
           apply T_id.elements_spec_tree. auto.
           apply T_id.elements_spec_tree. auto. unfold Ordered_id.eq.
           auto.
           rewrite <- H0. apply count_Intree_id;auto.
           apply T_id.elements_spec_tree. all:auto.
           apply T_id.remove_ok;auto. apply T_id.elements_spec_tree in H. 
           apply T_id.elements_spec_tree in H1. 
           assert (~Nat.eq (id b) (id a)). intro.  
           apply nodup_conflict_spec_id with (s:= A) in H2. all:auto.
           assert(T_id.Intree a A/\~ Nat.eq (id b) (id a)). auto.
           apply T_id.remove_spec_tree in H3. 
           apply count_Intree_id in H3;auto. lia. apply T_id.remove_ok. all:auto.
        }
    }
    { assert(Hperm:=H0). 
       apply perm_elim with (a0:=a) in H0. assert(Hpermc:=H0).
       apply countP2 in H1.
       rewrite H1 in H0.  symmetry in H0.
       destruct (ord_eqb b a) eqn:Hab.
        { move /eqP in Hab. subst b. apply countP3 in H1. destruct (H1 H).
        }
        { destruct (id a =? id b) eqn:Hid.
         { move /eqP in Hid. move /eqP in Hab. assert(a<>b). auto.
           assert(count a (delete_order A0 (id b)) = 0). rewrite <- Hid.
           apply delete_order_count_eq. 
          cut(count a (T_id.elements (T_id.remove b A)) = 0). lia. 
          apply countP2. intro. apply T_id.elements_spec_tree in H4.
          apply T_id.remove_spec_tree in H4. destruct H4. 
          unfold Nat.eq in H5. lia. all:auto.
         }
         { move /eqP in Hid. move /eqP in Hab. assert(a<>b). auto.
           rewrite delete_order_count_neq. auto. rewrite H0. 
          apply countP2. intro. apply T_id.elements_spec_tree in H3.
          apply T_id.remove_spec_tree in H3. destruct H3. 
          apply count_Intree_id in H3. lia. all:auto.
         }
} }
Qed.



Lemma perm_remove_tree_deleteB (B:TB.t)(b:TB.elt)(B0:list order):
TB.Ok B ->List.In b (TB.elements B) -> perm (TB.elements B) B0 -> perm (TB.elements (TB.remove b B)) (delete b B0).
Proof. intros ok1 H H0. apply perm_intro. intros. 
         assert(H1:List.In a (TB.elements B)\/~List.In a (TB.elements B)).
         eauto. destruct H1 as [H1 | H1].
      { assert(Hperm:=H0). 
         apply perm_elim with (a0:=a) in H0. 
         destruct (ord_eqb b a) eqn:Hab. 
         { move /eqP in Hab. subst. apply TB.elements_spec_tree in H. 
           apply count_IntreeB in H;auto. 
           rewrite H in H0. symmetry in H0.
           assert(H2:count a B0 >= 1). lia.
           apply countP1a in H2. 
           destruct (count_treeB (TB.remove a B) a) as [H4 | H4].
           apply TB.remove_ok.
           auto. rewrite H4. apply count_IntreeB in H4;auto. symmetry. 
           apply (TB.remove_spec_tree B a a) in H4. destruct H4. destruct H4.
           unfold OTypes.eqcompetitive. auto. apply TB.remove_ok. auto.
           rewrite H4. symmetry. rewrite countP7 in H0. auto. lia.
         } 
         { move /eqP in Hab. 
           destruct (count_treeB (TB.remove b B) a) as [H4 | H4].
           apply TB.remove_ok. auto. 
           rewrite H4. apply count_IntreeB in H4;auto. symmetry.
           rewrite <- countP9.
           rewrite <- H0. apply count_IntreeB;auto.
           apply TB.elements_spec_tree. all:auto.
           apply TB.remove_ok;auto. apply TB.elements_spec_tree in H. 
           apply TB.elements_spec_tree in H1. 
           assert (~OTypes.eqcompetitive b a). intro.  
           apply nodup_conflict_specB with (s:= B) in H2. all:auto.
           assert(TB.Intree a B/\~ OTypes.eqcompetitive b a). auto.
           apply TB.remove_spec_tree in H3. 
           apply count_IntreeB in H3;auto. lia. apply TB.remove_ok. all:auto.
        }
    }
    { assert(Hperm:=H0). 
       apply perm_elim with (a0:=a) in H0. assert(Hpermc:=H0).
       apply countP2 in H1.
       rewrite H1 in H0.  symmetry in H0.
       destruct (ord_eqb b a) eqn:Hab.
        { move /eqP in Hab. subst b. apply countP3 in H1. destruct (H1 H).
        }
        { move /eqP in Hab. assert(a<>b). auto. 
          apply countP9 with (l:=B0) in H2.
          cut(count a (TB.elements (TB.remove b B)) = 0). lia. 
          apply countP2. intro. apply TB.elements_spec_tree in H3.
          apply TB.remove_spec_tree in H3. destruct H3.
          apply count_IntreeB in H3;auto. lia. all:auto.
} }
Qed.

Lemma perm_remove_tree_deleteA (A:TA.t)(b:TA.elt)(A0:list order):
TA.Ok A -> List.In b (TA.elements A) -> perm (TA.elements A) A0 -> perm (TA.elements (TA.remove b A)) (delete b A0).
Proof. intros ok1 H H0. apply perm_intro. intros. 
         assert(H1:List.In a (TA.elements A)\/~List.In a (TA.elements A)).
         eauto. destruct H1 as [H1 | H1].
      { assert(Hperm:=H0). 
         apply perm_elim with (a0:=a) in H0. 
         destruct (ord_eqb b a) eqn:Hab. 
         { move /eqP in Hab. subst. apply TA.elements_spec_tree in H. 
           apply count_IntreeA in H;auto. 
           rewrite H in H0. symmetry in H0.
           assert(H2:count a A0 >= 1). lia.
           apply countP1a in H2. 
           destruct (count_treeA (TA.remove a A) a) as [H4 | H4].
           apply TA.remove_ok.
           auto. rewrite H4. apply count_IntreeA in H4;auto. symmetry. 
           apply (TA.remove_spec_tree A a a) in H4. destruct H4. destruct H4.
           unfold OTypes.eqcompetitive. auto. apply TA.remove_ok. auto.
           rewrite H4. symmetry. rewrite countP7 in H0. auto. lia.
         } 
         { move /eqP in Hab. 
           destruct (count_treeA (TA.remove b A) a) as [H4 | H4].
           apply TA.remove_ok. auto. 
           rewrite H4. apply count_IntreeA in H4;auto. symmetry.
           rewrite <- countP9.
           rewrite <- H0. apply count_IntreeA;auto.
           apply TA.elements_spec_tree. all:auto.
           apply TA.remove_ok;auto. apply TA.elements_spec_tree in H. 
           apply TA.elements_spec_tree in H1. 
           assert (~OTypes.eqcompetitive b a). intro.  
           apply nodup_conflict_specA with (s:= A) in H2. all:auto.
           assert(TA.Intree a A/\~ OTypes.eqcompetitive b a). auto.
           apply TA.remove_spec_tree in H3. 
           apply count_IntreeA in H3;auto. lia. apply TA.remove_ok. all:auto.
        }
    }
    { assert(Hperm:=H0). 
       apply perm_elim with (a0:=a) in H0. assert(Hpermc:=H0).
       apply countP2 in H1.
       rewrite H1 in H0.  symmetry in H0.
       destruct (ord_eqb b a) eqn:Hab.
        { move /eqP in Hab. subst b. apply countP3 in H1. destruct (H1 H).
        }
        { move /eqP in Hab. assert(a<>b). auto. 
          apply countP9 with (l:=A0) in H2.
          cut(count a (TA.elements (TA.remove b A)) = 0). lia. 
          apply countP2. intro. apply TA.elements_spec_tree in H3.
          apply TA.remove_spec_tree in H3. destruct H3.
          apply count_IntreeA in H3;auto. lia. all:auto.
} }
Qed.

Lemma perm_remove_tree_delete_id (A:T_id.t)(b:T_id.elt)(A0:list order):
T_id.Ok A -> List.In b (T_id.elements A) -> perm (T_id.elements A) A0 -> perm (T_id.elements (T_id.remove b A)) (delete b A0).
Proof. intros ok1 H H0. apply perm_intro. intros. 
         assert(H1:List.In a (T_id.elements A)\/~List.In a (T_id.elements A)).
         eauto. destruct H1 as [H1 | H1].
      { assert(Hperm:=H0). 
         apply perm_elim with (a0:=a) in H0. 
         destruct (ord_eqb b a) eqn:Hab. 
         { move /eqP in Hab. subst. apply T_id.elements_spec_tree in H. 
           apply count_Intree_id in H;auto. 
           rewrite H in H0. symmetry in H0.
           assert(H2:count a A0 >= 1). lia.
           apply countP1a in H2. 
           destruct (count_tree_id (T_id.remove a A) a) as [H4 | H4].
           apply T_id.remove_ok.
           auto. rewrite H4. apply count_Intree_id in H4;auto. symmetry. 
           apply (T_id.remove_spec_tree A a a) in H4. destruct H4. destruct H4.
           unfold Nat.eq. auto. apply T_id.remove_ok. auto.
           rewrite H4. symmetry. rewrite countP7 in H0. auto. lia.
         } 
         { move /eqP in Hab. 
           destruct (count_tree_id (T_id.remove b A) a) as [H4 | H4].
           apply T_id.remove_ok. auto. 
           rewrite H4. apply count_Intree_id in H4;auto. symmetry.
           rewrite <- countP9.
           rewrite <- H0. apply count_Intree_id;auto.
           apply T_id.elements_spec_tree. all:auto.
           apply T_id.remove_ok;auto. apply T_id.elements_spec_tree in H. 
           apply T_id.elements_spec_tree in H1. 
           assert (~Nat.eq (id b) (id a)). intro.  
           apply nodup_conflict_spec_id with (s:= A) in H2. all:auto.
           assert(T_id.Intree a A/\~ Nat.eq (id b) (id a)). auto.
           apply T_id.remove_spec_tree in H3. 
           apply count_Intree_id in H3;auto. lia. apply T_id.remove_ok. all:auto.
        }
    }
    { assert(Hperm:=H0). 
       apply perm_elim with (a0:=a) in H0. assert(Hpermc:=H0).
       apply countP2 in H1.
       rewrite H1 in H0.  symmetry in H0.
       destruct (ord_eqb b a) eqn:Hab.
        { move /eqP in Hab. subst b. apply countP3 in H1. destruct (H1 H).
        }
        { move /eqP in Hab. assert(a<>b). auto. 
          apply countP9 with (l:=A0) in H2.
          cut(count a (T_id.elements (T_id.remove b A)) = 0). lia. 
          apply countP2. intro. apply T_id.elements_spec_tree in H3.
          apply T_id.remove_spec_tree in H3. destruct H3.
          apply count_Intree_id in H3;auto. lia. all:auto.
} }
Qed.

Hint Immediate perm_remove_tree_delete_id perm_remove_tree_deleteB
 perm_remove_tree_deleteA :ecda.
Hint Immediate perm_remove_treeB perm_remove_treeA :ecda.

Lemma InT_time_InA (A:TA.t)(a:TA.elt):
TA.InT a A -> List.In (otime a) (map (otime) (TA.elements A)). 
Proof. induction A. simpl. intro H. inversion H. intro. 
       rewrite TA.elements_node. rewrite map_app. 
 - apply in_app_iff. inversion H. 
   * subst.  right. simpl.  left. unfold OTypes.eqcompetitive in H1.
     destruct H1. move /eqP in H1. auto. 
   * subst. left. apply IHA1. auto.
   * subst. right. simpl. right. apply IHA2. auto.
Qed. 

Lemma InT_time_InB (A:TB.t)(a:TB.elt):
TB.InT a A -> List.In (otime a) (map (otime) (TB.elements A)). 
Proof. induction A. simpl. intro H. inversion H. intro. 
       rewrite TB.elements_node. rewrite map_app. 
 - apply in_app_iff. inversion H. 
   * subst.  right. simpl.  left. unfold OTypes.eqcompetitive in H1.
     destruct H1. move /eqP in H1. auto. 
   * subst. left. apply IHA1. auto.
   * subst. right. simpl. right. apply IHA2. auto.
Qed. 

Lemma InT_id_In_id (A:T_id.t)(a:T_id.elt):
T_id.InT a A -> List.In (id a) (map (id) (T_id.elements A)). 
Proof. induction A. simpl. intro H. inversion H. intro. 
       rewrite T_id.elements_node. rewrite map_app. 
 - apply in_app_iff. inversion H. 
   * subst.  right. simpl.  left. unfold Nat.eq in H1.
     auto. 
   * subst. left. apply IHA1. auto.
   * subst. right. simpl. right. apply IHA2. auto.
Qed. 


Lemma add_element_InA (A:TA.t)(a:TA.elt):
TA.Ok A -> ~List.In (otime a) (timesof (TA.elements A)) ->
TA.Intree a (TA.add a A).
Proof. intros ok1 H. apply TA.add_spec_tree. auto. intro. apply InT_time_InA in H0. replace (timesof) with (map otime) in H. destruct (H H0). auto. auto. Qed.

Lemma add_element_InB (A:TB.t)(a:TB.elt):
TB.Ok A -> ~List.In (otime a) (timesof (TB.elements A)) ->
TB.Intree a (TB.add a A).
Proof. intros ok1 H. apply TB.add_spec_tree. auto. intro. apply InT_time_InB in H0. replace (timesof) with (map otime) in H. destruct (H H0). auto. auto. Qed.

Lemma add_element_In_id (A:T_id.t)(a:T_id.elt):
T_id.Ok A -> ~List.In (id a) (ids (T_id.elements A)) ->
T_id.Intree a (T_id.add a A).
Proof. intros ok1 H. apply T_id.add_spec_tree. auto. 
intro. apply InT_id_In_id in H0. replace (ids) with (map id) in H. destruct (H H0). auto. auto. Qed.

Hint Immediate add_element_InB add_element_InA add_element_In_id :ecda.
Hint Immediate InT_time_InB InT_time_InA InT_id_In_id :ecda.

Lemma perm_add_list_headB (B:TB.t)(B0:list order)(a:TB.elt):
TB.Ok B -> NoDup (timesof (a::B0)) ->
perm (TB.elements B) (B0) -> 
perm (TB.elements (TB.add a B)) (a :: B0).
Proof. intros okB1 H0 H.
assert(Hperm:=H). apply perm_intro. intros a0. 
apply perm_elim with (a1:=a0) in H.
simpl.  destruct (ord_eqb a0 a) eqn:Hab.
{ move /eqP in Hab. subst a0. 
  destruct (count_treeB (TB.add a B) a) as [H4 | H4].
   apply TB.add_ok. auto. 
    - cut((count a B0) = 0). lia. apply countP2.
      intro. simpl in H0. apply NoDup_cons_iff in H0.
      destruct H0. destruct H0. apply timesof_elim. auto.
    - apply countP3 in H4. destruct H4. apply TB.elements_spec_tree.
      apply TB.add_spec_tree. auto. intro. apply InT_time_InB in H1. 
      replace (map otime) with timesof in H1. simpl in H0. 
      apply timesof_perm in Hperm. 
      apply Subset_elim4 with (l2:=timesof B0) in H1.
      apply NoDup_cons_iff in H0. destruct H0. destruct H0. auto. 
      eauto. auto. auto.
}
{ 
destruct (count_treeB B a0) as [H4 | H4]. auto.
-
rewrite H4 in H.
rewrite <- H.  assert(List.In a0 B0). apply countP1a.  lia.
 destruct (count_treeB (TB.add a B) a0) as [H5 | H5]. apply TB.add_ok. auto.
 auto. apply count_IntreeB in H4. apply TB.add_spec1_tree with (x:=a) in H4.
  apply count_IntreeB in H4. lia. apply TB.add_ok. auto. auto. auto.
  - destruct (count_treeB (TB.add a B) a0) as [H5 | H5]. apply TB.add_ok. auto.
    apply count_IntreeB in H5. apply countP3 in H4. move /eqP in Hab.
    destruct Hab. symmetry. apply TB.add_spec0_tree with (s:=B). auto. 
    intro. apply TB.elements_spec_tree in H1. destruct (H4 H1). auto.
    apply TB.add_ok. auto. lia.
}
 Qed.

Lemma perm_add_list_headA (A:TA.t)(A0:list order)(a:TA.elt):
TA.Ok A -> NoDup (timesof (a::A0)) ->
perm (TA.elements A) (A0) -> 
perm (TA.elements (TA.add a A)) (a :: A0).
Proof. intros okB1 H0 H.
assert(Hperm:=H). apply perm_intro. intros a0. 
apply perm_elim with (a1:=a0) in H.
simpl.  destruct (ord_eqb a0 a) eqn:Hab.
{ move /eqP in Hab. subst a0. 
  destruct (count_treeA (TA.add a A) a) as [H4 | H4].
   apply TA.add_ok. auto. 
    - cut((count a A0) = 0). lia. apply countP2.
      intro. simpl in H0. apply NoDup_cons_iff in H0.
      destruct H0. destruct H0. apply timesof_elim. auto.
    - apply countP3 in H4. destruct H4. apply TA.elements_spec_tree.
      apply TA.add_spec_tree. auto. intro. apply InT_time_InA in H1. 
      replace (map otime) with timesof in H1. simpl in H0. 
      apply timesof_perm in Hperm. 
      apply Subset_elim4 with (l2:=timesof A0) in H1.
      apply NoDup_cons_iff in H0. destruct H0. destruct H0. auto. 
      eauto. auto. auto.
}
{ 
destruct (count_treeA A a0) as [H4 | H4]. auto.
-
rewrite H4 in H.
rewrite <- H.  assert(List.In a0 A0). apply countP1a.  lia.
 destruct (count_treeA (TA.add a A) a0) as [H5 | H5]. apply TA.add_ok. auto.
 auto. apply count_IntreeA in H4. apply TA.add_spec1_tree with (x:=a) in H4.
  apply count_IntreeA in H4. lia. apply TA.add_ok. auto. auto. auto.
  - destruct (count_treeA (TA.add a A) a0) as [H5 | H5]. apply TA.add_ok. auto.
    apply count_IntreeA in H5. apply countP3 in H4. move /eqP in Hab.
    destruct Hab. symmetry. apply TA.add_spec0_tree with (s:=A). auto. 
    intro. apply TA.elements_spec_tree in H1. destruct (H4 H1). auto.
    apply TA.add_ok. auto. lia.
}
 Qed.

Hint Immediate perm_add_list_headB perm_add_list_headA :ecda.

Lemma perm_add_listB (B:TB.t)(B0:list order)(b a:TB.elt):
TB.Ok B -> ~ List.In (otime b) (timesof B0) -> 
(otime b) = (otime a) ->
(oprice b) = (oprice a) ->
perm (TB.elements B) (b::B0) -> 
perm  (TB.elements   (TB.add  a (TB.remove b B)))  (a :: B0).
Proof.
 intros H H0 H1 H2 H3. apply perm_intro. intros a0.
assert(Hperm:=H3).
apply perm_elim with (a1:=a0) in H3. 
assert(H5:List.In b (TB.elements B)). 
apply Subset_elim4 with (l1:=(b::B0)). auto. 
apply included_elim5. unfold perm in Hperm. move /andP in Hperm.
apply Hperm. assert(Ht:~List.In (otime a) (timesof (TB.elements (TB.remove b B)))). intro. 
apply perm_remove_tree_deleteB with (b:=b) in Hperm. simpl in Hperm.
replace (ord_eqb b b) with true in Hperm. 
apply timesof_perm in Hperm. 
destruct H0. rewrite H1. 
apply Subset_elim4 with (l2:=timesof (B0)) in H4. auto. 
apply included_elim5. unfold perm in Hperm. move /andP in Hperm.
apply Hperm. all:auto. 
destruct (count_treeB ((TB.add a (TB.remove b B))) a0).
  - apply TB.add_ok. apply TB.remove_ok. auto.
  - apply count_IntreeB in H4 as H6. destruct(ord_eqb a0 a) eqn:Ha. 
      * move /eqP in Ha. subst. simpl. replace (ord_eqb a a) with true.
        rewrite H1 in H0. cut((count a B0) = 0). lia. apply countP2. intro.
        apply timesof_elim in H7. destruct (H0 H7). rewrite ord_eqb_ref. auto.
      * simpl. rewrite Ha. apply TB.add_spec_tree in H6. destruct H6. subst.
        rewrite ord_eqb_ref in Ha. inversion Ha. 
        apply TB.remove_spec_tree in H6. destruct H6. 
        apply count_IntreeB in H6. simpl in H3. 
        replace (ord_eqb a0 b) with false in H3. lia. 
        move /eqP in Ha. unfold OTypes.eqcompetitive in H7. 
        destruct (oprice b =? oprice a0) eqn:Hap; 
        destruct (otime b =? otime a0) eqn:Hat. destruct H7. auto.
        move /eqP in Hat. destruct (ord_eqb a0 b) eqn:Hab. move /eqP in Hab.
        subst. lia. auto. 
        move /eqP in Hap. destruct (ord_eqb a0 b) eqn:Hab. move /eqP in Hab.
        subst. lia. auto. 
        move /eqP in Hat. destruct (ord_eqb a0 b) eqn:Hab. move /eqP in Hab.
        subst. lia. auto. all:auto. apply TB.remove_ok. auto. 
        intro. apply InT_time_InB in H8. 
        replace (map otime) with timesof in H8. destruct (Ht H8). auto.
      * simpl. apply TB.add_ok. apply TB.remove_ok. auto.
  - simpl.  destruct (ord_eqb a0 a) eqn: Ha. 
      * move /eqP in Ha. 
        subst. apply countP3 in H4. destruct H4. apply TB.elements_spec_tree.
        apply TB.add_spec_tree. apply TB.remove_ok. auto. intro. 
        apply InT_time_InB in H4. replace (map otime) with timesof in H4.
        destruct (Ht H4). auto. auto.
      * simpl in H3. destruct (ord_eqb a0 b) eqn: Hb.
        + move /eqP in Hb. 
          subst. apply TB.elements_spec_tree in H5. 
          apply count_IntreeB in H5.
          lia. auto.
        + destruct (otime b =? otime a0) eqn:Hba.
          move /eqP in Hba. rewrite Hba in H0. 
          assert(~List.In a0 B0). intro. apply timesof_elim in H6. 
          destruct (H0 H6). apply countP2 in H6. lia. 
          cut(count a0 (TB.elements B) = 0). lia. apply countP2.
          intro. apply countP3 in H4. destruct H4. apply TB.elements_spec_tree.
          apply TB.add_spec_tree. apply TB.remove_ok. auto. intro.
          apply InT_time_InB in H4. replace (map otime) with timesof in H4.
          destruct (Ht H4). auto. right. apply TB.remove_spec_tree. auto.
          split. apply TB.elements_spec_tree. auto.  
          apply TB.elements_spec_tree in H6. intro. move /eqP in Hba. 
          destruct H4. move /eqP in H7. lia. 
Qed.
  
Lemma perm_add_listA (A:TA.t)(A0:list order)(b a:TA.elt):
TA.Ok A -> ~ List.In (otime b) (timesof A0) -> 
(otime b) = (otime a) ->
(oprice b) = (oprice a) ->
perm (TA.elements A) (b::A0) -> 
perm  (TA.elements   (TA.add  a (TA.remove b A)))  (a :: A0).
Proof.
 intros H H0 H1 H2 H3. apply perm_intro. intros a0.
assert(Hperm:=H3).
apply perm_elim with (a1:=a0) in H3. 
assert(H5:List.In b (TA.elements A)). 
apply Subset_elim4 with (l1:=(b::A0)). auto. 
apply included_elim5. unfold perm in Hperm. move /andP in Hperm.
apply Hperm. assert(Ht:~List.In (otime a) (timesof (TA.elements (TA.remove b A)))). intro. 
apply perm_remove_tree_deleteA with (b:=b) in Hperm. simpl in Hperm.
replace (ord_eqb b b) with true in Hperm. 
apply timesof_perm in Hperm. 
destruct H0. rewrite H1. 
apply Subset_elim4 with (l2:=timesof (A0)) in H4. auto. 
apply included_elim5. unfold perm in Hperm. move /andP in Hperm.
apply Hperm. all:auto. 
destruct (count_treeA ((TA.add a (TA.remove b A))) a0).
  - apply TA.add_ok. apply TA.remove_ok. auto.
  - apply count_IntreeA in H4 as H6. destruct(ord_eqb a0 a) eqn:Ha. 
      * move /eqP in Ha. subst. simpl. replace (ord_eqb a a) with true.
        rewrite H1 in H0. cut((count a A0) = 0). lia. apply countP2. intro.
        apply timesof_elim in H7. destruct (H0 H7). rewrite ord_eqb_ref. auto.
      * simpl. rewrite Ha. apply TA.add_spec_tree in H6. destruct H6. subst.
        rewrite ord_eqb_ref in Ha. inversion Ha. 
        apply TA.remove_spec_tree in H6. destruct H6. 
        apply count_IntreeA in H6. simpl in H3. 
        replace (ord_eqb a0 b) with false in H3. lia. 
        move /eqP in Ha. unfold OTypes.eqcompetitive in H7. 
        destruct (oprice b =? oprice a0) eqn:Hap; 
        destruct (otime b =? otime a0) eqn:Hat. destruct H7. auto.
        move /eqP in Hat. destruct (ord_eqb a0 b) eqn:Hab. move /eqP in Hab.
        subst. lia. auto. 
        move /eqP in Hap. destruct (ord_eqb a0 b) eqn:Hab. move /eqP in Hab.
        subst. lia. auto. 
        move /eqP in Hat. destruct (ord_eqb a0 b) eqn:Hab. move /eqP in Hab.
        subst. lia. auto. all:auto. apply TA.remove_ok. auto. 
        intro. apply InT_time_InA in H8. 
        replace (map otime) with timesof in H8. destruct (Ht H8). auto.
      * simpl. apply TA.add_ok. apply TA.remove_ok. auto.
  - simpl.  destruct (ord_eqb a0 a) eqn: Ha. 
      * move /eqP in Ha. 
        subst. apply countP3 in H4. destruct H4. apply TA.elements_spec_tree.
        apply TA.add_spec_tree. apply TA.remove_ok. auto. intro. 
        apply InT_time_InA in H4. replace (map otime) with timesof in H4.
        destruct (Ht H4). auto. auto.
      * simpl in H3. destruct (ord_eqb a0 b) eqn: Hb.
        + move /eqP in Hb. 
          subst. apply TA.elements_spec_tree in H5. 
          apply count_IntreeA in H5.
          lia. auto.
        + destruct (otime b =? otime a0) eqn:Hba.
          move /eqP in Hba. rewrite Hba in H0. 
          assert(~List.In a0 A0). intro. apply timesof_elim in H6. 
          destruct (H0 H6). apply countP2 in H6. lia. 
          cut(count a0 (TA.elements A) = 0). lia. apply countP2.
          intro. apply countP3 in H4. destruct H4. apply TA.elements_spec_tree.
          apply TA.add_spec_tree. apply TA.remove_ok. auto. intro.
          apply InT_time_InA in H4. replace (map otime) with timesof in H4.
          destruct (Ht H4). auto. right. apply TA.remove_spec_tree. auto.
          split. apply TA.elements_spec_tree. auto.  
          apply TA.elements_spec_tree in H6. intro. move /eqP in Hba. 
          destruct H4. move /eqP in H7. lia. 
Qed.

Lemma perm_add_list_id (B:T_id.t)(B0:list order)(b a:T_id.elt):
T_id.Ok B -> ~ List.In (id b) (ids B0) -> 
(id b) = (id a) ->
perm (T_id.elements B) (b::B0) -> 
perm  (T_id.elements   (T_id.add  a (T_id.remove b B)))  (a :: B0).
Proof.
 intros H H0 H1 H3. apply perm_intro. intros a0.
assert(Hperm:=H3).
apply perm_elim with (a1:=a0) in H3. 
assert(H5:List.In b (T_id.elements B)). 
apply Subset_elim4 with (l1:=(b::B0)). auto. 
apply included_elim5. unfold perm in Hperm. move /andP in Hperm.
apply Hperm. assert(Ht:~List.In (id a) (ids (T_id.elements (T_id.remove b B)))). intro H4. 
apply perm_remove_tree_delete_id with (b:=b) in Hperm. simpl in Hperm.
replace (ord_eqb b b) with true in Hperm. 
apply ids_perm in Hperm. 
destruct H0. rewrite H1. 
apply Subset_elim4 with (l2:=ids (B0)) in H4. auto. 
apply included_elim5. unfold perm in Hperm. move /andP in Hperm.
apply Hperm. all:auto. 
destruct (count_tree_id ((T_id.add a (T_id.remove b B))) a0) as [H4 | H4].
  - apply T_id.add_ok. apply T_id.remove_ok. auto.
  - apply count_Intree_id in H4 as H6. destruct(ord_eqb a0 a) eqn:Ha. 
      * move /eqP in Ha. subst. simpl. replace (ord_eqb a a) with true.
        rewrite H1 in H0. cut((count a B0) = 0). lia. apply countP2. intro H7.
        apply ids_intro in H7. destruct (H0 H7). rewrite ord_eqb_ref. auto.
      * simpl. rewrite Ha. apply T_id.add_spec_tree in H6. destruct H6. subst.
        rewrite ord_eqb_ref in Ha. inversion Ha. 
        apply T_id.remove_spec_tree in H2. destruct H2. 
        apply count_Intree_id in H2. simpl in H3. 
        replace (ord_eqb a0 b) with false in H3. lia. 
        move /eqP in Ha. unfold Nat.eq in H6. 
        destruct (ord_eqb a0 b) eqn:Hab. move /eqP in Hab.
        subst. lia. auto. 
        all:auto. apply T_id.remove_ok. auto. 
        intro. apply InT_id_In_id in H7. 
        replace (map id) with ids in H7. destruct (Ht H7). auto.
      * simpl. apply T_id.add_ok. apply T_id.remove_ok. auto.
  - simpl.  destruct (ord_eqb a0 a) eqn: Ha. 
      * move /eqP in Ha. 
        subst. apply countP3 in H4. destruct H4. apply T_id.elements_spec_tree.
        apply T_id.add_spec_tree. apply T_id.remove_ok. auto. intro. 
        apply InT_id_In_id in H2. replace (map id) with ids in H2.
        destruct (Ht H2). auto. auto.
      * simpl in H3. destruct (ord_eqb a0 b) eqn: Hb.
        + move /eqP in Hb. 
          subst. apply T_id.elements_spec_tree in H5. 
          apply count_Intree_id in H5.
          lia. auto.
        + destruct (id b =? id a0) eqn:Hba.
          move /eqP in Hba. rewrite Hba in H0. 
          assert(~List.In a0 B0). intro. apply ids_intro in H2. 
          destruct (H0 H2). apply countP2 in H2. lia. 
          cut(count a0 (T_id.elements B) = 0). lia. apply countP2.
          intro. apply countP3 in H4. destruct H4. 
          apply T_id.elements_spec_tree.
          apply T_id.add_spec_tree. apply T_id.remove_ok. auto. intro.
          apply InT_id_In_id in H4. replace (map id) with ids in H4.
          destruct (Ht H4). auto. right. apply T_id.remove_spec_tree. auto.
          split. apply T_id.elements_spec_tree. auto.  
          apply T_id.elements_spec_tree in H2. intro. move /eqP in Hba. 
          destruct H4.  lia. 
Qed.


Hint Immediate perm_add_list_id perm_add_listB perm_add_listA :ecda.

Lemma perm_addA (A:TA.t)(A_id: T_id.t)(a:TA.elt):
TA.Ok A -> T_id.Ok A_id ->~ List.In (otime a) (timesof (TA.elements A)) -> ~ List.In (id a) (ids (TA.elements A)) -> 
perm (TA.elements A) (T_id.elements A_id) -> 
perm (TA.elements (TA.add a A))  (T_id.elements (T_id.add a A_id)).
Proof. intros okB1 okB2 H0 H H1.
assert(Hperm:=H1). apply perm_intro. intros a0. 
apply perm_elim with (a1:=a0) in H1.
assert(Hi:~ List.In (id a) (ids (T_id.elements A_id))).
apply ids_perm in Hperm. intro. 
destruct H. apply Subset_elim4 with (l2:=ids (TA.elements A)) in H2.
auto. apply included_elim5. unfold perm in Hperm. move /andP in Hperm.
apply Hperm.
destruct (count_tree_id (T_id.add a A_id) a0) as [Hid | Hid].
apply T_id.add_ok. auto. 
 - apply count_Intree_id in Hid. apply T_id.add_spec_tree in Hid.
   destruct Hid.
   * subst a0. cut(count a (TA.elements (TA.add a A)) = 1/\
     count a (T_id.elements (T_id.add a A_id)) = 1). lia. split.
     apply count_IntreeA. apply TA.add_ok. auto. apply add_element_InA. auto.
     auto. apply count_Intree_id. apply T_id.add_ok. auto.
     apply add_element_In_id. auto. auto.
   * cut(count a0 (TA.elements (TA.add a A)) = 1/\
     count a0 (T_id.elements (T_id.add a A_id)) = 1). lia. split.
     apply count_IntreeA. apply TA.add_ok. auto. apply TA.add_spec_tree.
     auto. intro H4. apply InT_time_InA in H4.
     replace (map id) with ids in H4. destruct (H0 H4). auto. right.
     apply count_IntreeA. auto. apply count_Intree_id in H2. lia. auto.
     apply count_Intree_id. apply T_id.add_ok. auto. apply T_id.add_spec_tree.
     auto. intro H4. apply InT_id_In_id in H4.
     replace (map id) with ids in H4. destruct (Hi H4). auto. auto.
   * auto.
   * intro H4. apply InT_id_In_id in H4. 
   replace (map id) with ids in H4. destruct (Hi H4). auto.
   * apply T_id.add_ok. auto.
 - cut (count a0 (TA.elements (TA.add a A)) = 0). lia. apply countP2.
   intro. apply countP3 in Hid. apply TA.elements_spec_tree in H2.
   apply TA.add_spec_tree in H2. destruct H2. subst a0. 
   destruct Hid. apply T_id.elements_spec_tree.
   apply T_id.add_spec_tree. auto. intro H4. apply InT_id_In_id in H4. 
   replace (map id) with ids in H4. destruct (Hi H4). auto. auto.
   destruct Hid. apply T_id.elements_spec_tree.
   apply T_id.add_spec_tree. auto. intro H4. apply InT_id_In_id in H4. 
   replace (map id) with ids in H4. destruct (Hi H4). auto. right.
   apply count_IntreeA in H2. apply count_Intree_id. auto. lia. auto. auto.
   intro H4. apply InT_time_InA in H4. 
   replace (map otime) with timesof in H4. destruct (H0 H4). auto.
Qed.

Lemma perm_addB (B:TB.t)(B_id: T_id.t)(a:TB.elt):
TB.Ok B -> T_id.Ok B_id ->~ List.In (otime a) (timesof (TB.elements B)) -> ~ List.In (id a) (ids (TB.elements B)) -> 
perm (TB.elements B) (T_id.elements B_id) -> 
perm (TB.elements (TB.add a B))  (T_id.elements (T_id.add a B_id)).
Proof. intros okB1 okB2 H0 H H1.
assert(Hperm:=H1). apply perm_intro. intros a0. 
apply perm_elim with (a1:=a0) in H1.
assert(Hi:~ List.In (id a) (ids (T_id.elements B_id))).
apply ids_perm in Hperm. intro. 
destruct H. apply Subset_elim4 with (l2:=ids (TB.elements B)) in H2.
auto. apply included_elim5. unfold perm in Hperm. move /andP in Hperm.
apply Hperm.
destruct (count_tree_id (T_id.add a B_id) a0) as [Hid | Hid].
apply T_id.add_ok. auto. 
 - apply count_Intree_id in Hid. apply T_id.add_spec_tree in Hid.
   destruct Hid.
   * subst a0. cut(count a (TB.elements (TB.add a B)) = 1/\
     count a (T_id.elements (T_id.add a B_id)) = 1). lia. split.
     apply count_IntreeB. apply TB.add_ok. auto. apply add_element_InB. auto.
     auto. apply count_Intree_id. apply T_id.add_ok. auto.
     apply add_element_In_id. auto. auto.
   * cut(count a0 (TB.elements (TB.add a B)) = 1/\
     count a0 (T_id.elements (T_id.add a B_id)) = 1). lia. split.
     apply count_IntreeB. apply TB.add_ok. auto. apply TB.add_spec_tree.
     auto. intro H4. apply InT_time_InB in H4.
     replace (map id) with ids in H4. destruct (H0 H4). auto. right.
     apply count_IntreeB. auto. apply count_Intree_id in H2. lia. auto.
     apply count_Intree_id. apply T_id.add_ok. auto. apply T_id.add_spec_tree.
     auto. intro H4. apply InT_id_In_id in H4.
     replace (map id) with ids in H4. destruct (Hi H4). auto. auto.
   * auto.
   * intro H4. apply InT_id_In_id in H4. 
   replace (map id) with ids in H4. destruct (Hi H4). auto.
   * apply T_id.add_ok. auto.
 - cut (count a0 (TB.elements (TB.add a B)) = 0). lia. apply countP2.
   intro. apply countP3 in Hid. apply TB.elements_spec_tree in H2.
   apply TB.add_spec_tree in H2. destruct H2. subst a0. 
   destruct Hid. apply T_id.elements_spec_tree.
   apply T_id.add_spec_tree. auto. intro H4. apply InT_id_In_id in H4. 
   replace (map id) with ids in H4. destruct (Hi H4). auto. auto.
   destruct Hid. apply T_id.elements_spec_tree.
   apply T_id.add_spec_tree. auto. intro H4. apply InT_id_In_id in H4. 
   replace (map id) with ids in H4. destruct (Hi H4). auto. right.
   apply count_IntreeB in H2. apply count_Intree_id. auto. lia. auto. auto.
   intro H4. apply InT_time_InB in H4. 
   replace (map otime) with timesof in H4. destruct (H0 H4). auto.
Qed.

Hint Immediate perm_addB perm_addA :ecda.

From Equations Require Import Equations.
Equations EMatch_ask (B: TB.t)(A: TA.t)(a : TA.elt)(B_id A_id : T_id.t):
((TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)) by wf (oquantity a) :=
EMatch_ask B A a B_id A_id := match (TB.max_elt B) with
|None => (TB.Leaf, (TA.add a A), B_id, (T_id.add a A_id), nil)
|Some e => (if (Nat.eqb ((oprice a) - (oprice e)) 0) then 
  (match (Compare_dec.lt_eq_lt_dec (oquantity e) (oquantity a)) with
   |inleft (right _) =>  ((TB.remove e B), A, (T_id.remove e B_id), A_id,
               ((Mk_transaction (id e) (id a) (oquantity a) (oquantity_cond a))::nil))
   |inright _ => (TB.add (Mk_order (id e) (otime e) ((oquantity e) - (oquantity a))
                      (oprice e) _) (TB.remove e B), A, T_id.add (Mk_order (id e) 
                      (otime e) ((oquantity e) - (oquantity a)) (oprice e) _) 
                      (T_id.remove e B_id), A_id, ((Mk_transaction (id e) (id a) 
                      (oquantity a) (oquantity_cond a))::nil))
   |inleft (left _) =>
         (let B0:=(TB.remove e B) in 
          let B0_id:=(T_id.remove e B_id) in 
          let BAM := (EMatch_ask B0 A (Mk_order (id a) (otime a) 
                                                  ((oquantity a) - (oquantity e)) 
                                                  (oprice a) _ ) B0_id  A_id) in  
                      (Bt BAM, At BAM, Bt_id BAM, At_id BAM,
                      (Mk_transaction (id e) (id a)   (oquantity e) (oquantity_cond e))::
                      (Mt BAM))) end)
  else (B, (TA.add a A), B_id, (T_id.add a A_id), nil)) end.
Next Obligation.
apply PeanoNat.Nat.ltb_nlt.  apply liaforrun;auto. Defined. 
Next Obligation. destruct e. simpl.
assert (P:=oquantity_cond ). auto. move /ltP in P. lia. Defined.
Next Obligation.
apply PeanoNat.Nat.ltb_nlt; apply liaforrun;auto. Defined.
Next Obligation.
apply PeanoNat.Nat.ltb_nlt; apply liaforrun;auto. Defined.

Equations EMatch_bid (B: TB.t)(A: TA.t)(b : TA.elt)(B_id A_id : T_id.t):
((TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)) by wf (oquantity b) :=
EMatch_bid B A b B_id A_id := match (TA.max_elt A) with
|None => ((TB.add b B), TA.Leaf, (T_id.add b B_id), A_id, nil)
|Some e => (if (Nat.eqb ((oprice e) - (oprice b)) 0) then 
  (match (Compare_dec.lt_eq_lt_dec (oquantity b) (oquantity e)) with
   |inleft (right _) =>  (B, (TA.remove e A), B_id, (T_id.remove e A_id), ((Mk_transaction (id b) (id e) (oquantity b) (oquantity_cond b))::nil))
   |inleft (left _) => (B, TA.add (Mk_order (id e) (otime e) ((oquantity e) - (oquantity b)) (oprice e) _) (TA.remove e A), B_id, T_id.add (Mk_order (id e) (otime e) ((oquantity e) - (oquantity b)) (oprice e) _) (T_id.remove e A_id), ((Mk_transaction (id b) (id e) (oquantity b) (oquantity_cond b))::nil))
   |inright _ =>
         (let A0:=(TA.remove e A) in 
          let A0_id:=(T_id.remove e A_id) in 
          let BAM := (EMatch_bid B A0 (Mk_order (id b) (otime b) ((oquantity b) - (oquantity e)) (oprice b) _ ) B_id  A0_id) in  
                      (Bt BAM, At BAM, Bt_id BAM, At_id BAM,
                      (Mk_transaction (id b) (id e) (oquantity e) (oquantity_cond e))::
                      (Mt BAM))) end)
  else (TB.add b B, A,T_id.add b B_id, A_id, nil)) end.
Next Obligation.
apply PeanoNat.Nat.ltb_nlt.  apply liaforrun;auto. Defined. 
Next Obligation. 
apply PeanoNat.Nat.ltb_nlt; apply liaforrun;auto. Defined.
Next Obligation.
apply PeanoNat.Nat.ltb_nlt; apply liaforrun;auto. Defined.
Next Obligation.
destruct e. simpl.
assert (P:=oquantity_cond ). auto. move /ltP in P. lia. Defined.




Fixpoint search_order (t : T_id.t) (i : nat) {struct t} : option T_id.elt :=
  match t with
  | T_id.Leaf => None
  | T_id.Node _ l k r =>
      match (lt_eq_lt_dec (id k) i) with
      |inleft (right _) => Some k
      |inright _  => search_order l i
      |inleft (left _) => search_order r i
      end
  end.

Lemma search_order_In (t : T_id.t) (i : nat)(k:T_id.elt):
search_order t i = Some k ->
T_id.Intree k t.
Proof. intros H. induction t. simpl in H. 
inversion H.  simpl in H. 
destruct (lt_eq_lt_dec (id t3) i) eqn:H1. destruct s.
apply T_id.InRighttree. auto. constructor. 
inversion H. auto. apply T_id.InLefttree. auto. Qed.

Lemma search_order_id (t : T_id.t) (i : nat)(k:T_id.elt):
search_order t i = Some k ->
(id k) = i.
Proof. intros H. induction t. simpl in H. 
inversion H.  simpl in H. 
destruct (lt_eq_lt_dec (id t3) i) eqn:H1. destruct s.
auto. inversion H. subst k. auto. auto. Qed.

Lemma search_order_In2 (t : T_id.t) (i : nat)(k:T_id.elt):
T_id.Ok t -> T_id.Intree k t -> search_order t (id k) = Some k.
Proof. intros ok1 Hin. induction t. 
T_id.intuition_in_tree. simpl. T_id.intuition_in_tree. 
destruct (lt_eq_lt_dec (id t3) (id t3)) eqn:H1.
destruct s. lia. unfold T_id.lt_tree in H6. auto.
lia. destruct (lt_eq_lt_dec (id t3) (id k) ) eqn:Hk. destruct s.
unfold T_id.lt_tree in H5. apply T_id.Intree_InT in H0. apply H5 in H0. 
unfold Nat.lt in H0. lia. unfold T_id.lt_tree in H5. apply T_id.Intree_InT in H0. apply H5 in H0. unfold Nat.lt in H0. lia.  auto.
destruct (lt_eq_lt_dec (id t3) (id k) ) eqn:Hk. destruct s.
auto. unfold T_id.gt_tree in H6. apply T_id.Intree_InT in H0. apply H6 in H0. 
unfold Nat.lt in H0. lia. unfold T_id.gt_tree in H6. apply T_id.Intree_InT in H0. apply H6 in H0. unfold Nat.lt in H0. lia.
Qed.

Lemma search_order_Leaf (t : T_id.t) (i : nat):
T_id.Ok t -> search_order t i = None ->
~List.In i (ids (T_id.elements t)).
Proof. intros ok1 H. intro H1. T_id.intuition_in_tree.
 apply ids_elim in H1. 
destruct H1 as [b H1]. destruct H1 as [H1 H2].
apply T_id.elements_spec_tree in H1 as H3. 
apply search_order_In2 in H3. subst i.
rewrite H in H3. inversion H3. auto. auto. Qed.


Definition EDel_order (B:TB.t)(A:TA.t)(i:nat)(B_id A_id:T_id.t):
((TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)).
destruct (search_order B_id i) eqn:Hb;destruct (search_order A_id i) eqn:Ha.
exact (TB.remove e B, TA.remove e0 A, T_id.remove e B_id, T_id.remove e0 A_id, nil).
exact (TB.remove e B, A, T_id.remove e B_id, A_id, nil).
exact (B, TA.remove e A, B_id, T_id.remove e A_id, nil).
exact (B, A, B_id, A_id, nil).
Defined.


Lemma same_order_diffq_ask (a e: order)(H: (oquantity e < oquantity a)):
{|id := id a;otime := otime a; oquantity := oquantity a - oquantity e;
  oprice := oprice a;  oquantity_cond := iff_flip_impl_subrelation
                      ((oquantity a - oquantity e <? 1) = false)
                      (~ oquantity a - oquantity e < 1)
                      (Nat.ltb_nlt (oquantity a - oquantity e) 1)
                      (liaforrun e a H) |} = 
{|id := id a; otime := otime a; oquantity := oquantity a - oquantity e;
  oprice := oprice a;  oquantity_cond := EMatch_ask_obligations_obligation_1 a e H |}.
Proof.
  f_equal. unfold EMatch_ask_obligations_obligation_1.  
  destruct (Nat.ltb_nlt (oquantity a - oquantity e) 1).
  apply BoolDecidableEqDepSet.UIP. 
Qed.

Lemma same_order_diffq_bid (a b: order)(l : oquantity a < oquantity b):
{|id := id b; otime := otime b; oquantity := oquantity b - oquantity a;
  oprice := oprice b; oquantity_cond := iff_flip_impl_subrelation
  ((oquantity b - oquantity a <? 1) = false)(~ oquantity b - oquantity a < 1)
  (Nat.ltb_nlt (oquantity b - oquantity a)  1) (liaforrun a b l) |}
=
{| id := id b; otime := otime b; oquantity := oquantity b - oquantity a;
   oprice := oprice b; oquantity_cond := 
   EMatch_bid_obligations_obligation_3 b a l |}.
Proof.
  f_equal. unfold EMatch_bid_obligations_obligation_3.  
  destruct (Nat.ltb_nlt (oquantity b - oquantity a) 1).
  apply BoolDecidableEqDepSet.UIP. 
Qed.




Lemma efficient_correct_ask (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
NoDup (timesof B) -> T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> Sorted Properties.bcompetitive B ->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
Mt (EMatch_ask tB tA ord tB_id tA_id) =
Mlist (Match_ask B A ord).
Proof. 
intros ndt ok1 ok2 ok3 ok4 H H0 H1 H2 H3. funelim (EMatch_ask tB tA ord tB_id tA_id). 
destruct (TB.max_elt B) eqn:Bmax;destruct B0 as [|b B0'] eqn:HB0.
{ apply TB.max_elt_spec1 in Bmax. apply TB.elements_spec1 in Bmax.
  apply perm_elim1 in H2. rewrite H2 in Bmax. inversion Bmax. } 
{ assert(e=b).  apply max_elt_equal_list_maxB with (B:=B)(B0:=B0').
  all:auto.  subst e. rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. f_equal. rewrite same_order_diffq_ask.
        apply H with (e:=b)(l:=l). all: auto. simpl in ndt. eauto. apply T_id.remove_ok. auto.
        apply TB.remove_ok. auto. eauto. 
        apply perm_remove_treeB. auto. auto.  (*tree remove perm property*)
        apply max_elt_in_listB. auto. auto. 
        replace B0' with (delete b (b::B0')). 
        apply perm_remove_tree_deleteB. auto. apply max_elt_in_listB.
        auto. auto. simpl. 
        destruct (ord_eqb b b) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto. 
      } 
      { simpl. auto. } 
    }
    { simpl. auto. } apply /eqP. simpl. auto.
  }
  { replace (S n =? 0) with false. simpl. auto. auto. }
}
{ rewrite <- Heqcall. simpl. auto. }
{  assert(H5:List.In b (TB.elements B)).
   apply perm_sym in H2.
   apply included_elim2 with (l:=B0').
   unfold perm in H2. move /andP in H2. apply H2. 
   apply TB.max_elt_spec3 in Bmax.  
   destruct Bmax with (a:=b). auto. auto with ecda. }
Qed.


Lemma efficient_correct_bid (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
NoDup (timesof A) -> T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> Sorted Properties.acompetitive A ->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
Mt (EMatch_bid tB tA ord tB_id tA_id) =
Mlist (Match_bid B A ord).
Proof. 
intros ndt ok1 ok2 ok3 ok4 H H0 H1 H2 H3. funelim (EMatch_bid tB tA ord tB_id tA_id). 
destruct (TA.max_elt A) eqn:Amax;destruct A0 as [|a A0'] eqn:HB0.
{ apply TA.max_elt_spec1 in Amax. apply TA.elements_spec1 in Amax.
  apply perm_elim1 in H4. rewrite H4 in Amax. inversion Amax. } 
{ assert(e=a). apply max_elt_equal_list_minA with (B:=A)(B0:=A0').
  all:auto. subst e. rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. replace (0 =? 0) with true in Heqcall. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hq.
    { destruct s eqn:Hs. 
      { simpl. f_equal. }
      { simpl. auto. } }
      { simpl. f_equal. rewrite same_order_diffq_bid.
        apply H with (e:=a)(l:=l). all: auto. 
        simpl in ndt. eauto. apply T_id.remove_ok.
        auto. apply TA.remove_ok. auto. eauto. 
        apply perm_remove_treeA. auto. auto.  (*tree remove perm property*)
        apply max_elt_in_listA. auto. auto. 
        replace A0' with (delete a (a::A0')). 
        apply perm_remove_tree_deleteA. auto. apply max_elt_in_listA.
        auto. auto. simpl. 
        destruct (ord_eqb a a) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto.
      } 
      auto. auto. 
    }
    { simpl. auto. } 
  }
{ rewrite <- Heqcall. simpl. auto. }
{  assert(H5:List.In a (TA.elements A)).
   apply perm_sym in H4.
   apply included_elim2 with (l:=A0').
   unfold perm in H4. move /andP in H4. apply H4. 
   apply TA.max_elt_spec3 in Amax.  
   destruct Amax with (a:=a). auto. eauto with ecda. }
Qed.

Hint Immediate efficient_correct_bid efficient_correct_ask : ecda.

Lemma efficient_correct_askB (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->Sorted Properties.bcompetitive B ->
NoDup (timesof B) ->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
perm (TB.elements (Bt (EMatch_ask tB tA ord tB_id tA_id))) (Blist (Match_ask B A ord)).
Proof. intros ok1 ok2 ok3 ok4 H Htime H0 H1 H2 H3. funelim (EMatch_ask tB tA ord tB_id tA_id). 
destruct (TB.max_elt B) eqn:Bmax;destruct B0 as [|b B0'] eqn:HB0.
{ apply TB.max_elt_spec1 in Bmax. apply TB.elements_spec1 in Bmax.
  apply perm_elim1 in H2. rewrite H2 in Bmax. inversion Bmax. } 
{ assert(e=b).  apply max_elt_equal_list_maxB with (B:=B)(B0:=B0').
  all:auto.  subst e. rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. f_equal. rewrite same_order_diffq_ask.
        apply H with (e:=b)(l:=l). all: auto. all:TB.intuition_in_tree.
        eauto. eauto. 
        apply perm_remove_treeB. all:auto.  (*tree remove perm property*)
        apply max_elt_in_listB. auto.
        replace B0' with (delete b (b::B0')). 
        apply perm_remove_tree_deleteB. auto. 
        apply max_elt_in_listB. auto. auto. simpl.
        destruct (ord_eqb b b) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto. 
      } 
      { simpl. auto. replace B0' with (delete b (b::B0')). 
        apply perm_remove_tree_deleteB. auto. 
        apply max_elt_in_listB. auto. auto. simpl.
        destruct (ord_eqb b b) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto. 
      } 
    }
    { simpl. f_equal. rewrite same_order_diffq_ask. 
    replace (EMatch_ask_obligations_obligation_3 a b l) with
    (EMatch_ask_obligations_obligation_1 b a l). apply perm_add_listB.
    all:auto. } apply /eqP. simpl. auto.
  }
  { replace (S n =? 0) with false. simpl. auto. auto. }
}
{ rewrite <- Heqcall. simpl. auto. }
{  assert(H5:List.In b (TB.elements B)).
   apply perm_sym in H2.
   apply included_elim2 with (l:=B0').
   unfold perm in H2. move /andP in H2. apply H2. 
   apply TB.max_elt_spec3 in Bmax. 
   destruct Bmax with (a:=b). auto. auto with ecda. } Qed.

Lemma efficient_correct_bidB (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
NoDup (timesof A) ->
NoDup (timesof (ord::B)) ->
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
Sorted Properties.acompetitive A ->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
perm (TB.elements (Bt (EMatch_bid tB tA ord tB_id tA_id))) (Blist (Match_bid B A ord)).
Proof. 
intros ndtA ndtB ok1 ok2 ok3 ok4 H H0 H1 H2 H3. funelim (EMatch_bid tB tA ord tB_id tA_id). 
destruct (TA.max_elt A) eqn:Amax;destruct A0 as [|a A0'] eqn:HB0.
{ apply TA.max_elt_spec1 in Amax. apply TA.elements_spec1 in Amax.
  apply perm_elim1 in H4. rewrite H4 in Amax. inversion Amax. } 
{ assert(e=a). apply max_elt_equal_list_minA with (B:=A)(B0:=A0').
  all:auto. subst e. rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. replace (0 =? 0) with true in Heqcall. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hq.
    { destruct s eqn:Hs. 
      { simpl. f_equal. auto. }
      { simpl. auto. } }
      { simpl. f_equal. rewrite same_order_diffq_bid.
        apply H with (e:=a)(l:=l). all: auto. all:TB.intuition_in_tree.
        eauto. eauto. 
        apply perm_remove_treeA. all:auto.  (*tree remove perm property*)
        apply max_elt_in_listA. auto.
        replace A0' with (delete a (a::A0')). 
        apply perm_remove_tree_deleteA. auto. 
        apply max_elt_in_listA. auto. auto. simpl.
        destruct (ord_eqb a a) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto.
     } auto. auto.
    }
     { simpl. all:auto. apply perm_add_list_headB. all:auto. } 
   }
   {  rewrite <- Heqcall. simpl. all:auto. apply perm_add_list_headB.
      all:auto. }
{  assert(H5:List.In a (TA.elements A)).
   apply perm_sym in H4.
   apply included_elim2 with (l:=A0').
   unfold perm in H4. move /andP in H4. apply H4. 
   apply TA.max_elt_spec3 in Amax.  
   destruct Amax with (a:=a). auto. eauto with ecda. }
 Qed.

Hint Immediate efficient_correct_askB efficient_correct_bidB : ecda.

Lemma efficient_correct_askA (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->Sorted Properties.bcompetitive B ->
NoDup (timesof B) ->
NoDup (timesof (ord::A)) ->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
perm (TA.elements (At (EMatch_ask tB tA ord tB_id tA_id))) (Alist (Match_ask B A ord)).
Proof. intros ok1 ok2 ok3 ok4 H HtimeB HtimeA H0 H1 H2 H3. funelim (EMatch_ask tB tA ord tB_id tA_id). 
destruct (TB.max_elt B) eqn:Bmax;destruct B0 as [|b B0'] eqn:HB0.
{ apply TB.max_elt_spec1 in Bmax. apply TB.elements_spec1 in Bmax.
  apply perm_elim1 in H2. rewrite H2 in Bmax. inversion Bmax. } 
{ assert(e=b).  apply max_elt_equal_list_maxB with (B:=B)(B0:=B0').
  all:auto.  subst e. rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. f_equal. rewrite same_order_diffq_ask.
        apply H with (e:=b)(l:=l). 
        all: auto. all:TB.intuition_in_tree. eauto. eauto. 
        apply perm_remove_treeB. all:auto.  (*tree remove perm property*)
        apply max_elt_in_listB. auto.
        replace B0' with (delete b (b::B0')). 
        apply perm_remove_tree_deleteB.
        auto. apply max_elt_in_listB. auto. auto. simpl.
        destruct (ord_eqb b b) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto. 
      } 
      { simpl. auto. } 
    }
    { simpl. auto. } apply /eqP. simpl. auto.
  }
  { replace (S n =? 0) with false. simpl. auto. apply perm_add_list_headA. all:auto. }
}
{ rewrite <- Heqcall. simpl. all:auto. apply perm_add_list_headA. all:auto. }
{  assert(H5:List.In b (TB.elements B)).
   apply perm_sym in H2.
   apply included_elim2 with (l:=B0').
   unfold perm in H2. move /andP in H2. apply H2. 
   apply TB.max_elt_spec3 in Bmax. 
   destruct Bmax with (a:=b). auto. auto with ecda. } Qed.
   
Lemma efficient_correct_bidA (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
Sorted Properties.acompetitive A ->
NoDup (timesof A) ->
NoDup (timesof (ord::B)) ->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
perm (TA.elements (At (EMatch_bid tB tA ord tB_id tA_id))) (Alist (Match_bid B A ord)).
Proof.
intros ndtA ndtB ok1 ok2 ok3 ok4 H H0 H1 H2 H3. funelim (EMatch_bid tB tA ord tB_id tA_id). 
destruct (TA.max_elt A) eqn:Amax;destruct A0 as [|a A0'] eqn:HB0.
{ apply TA.max_elt_spec1 in Amax. apply TA.elements_spec1 in Amax.
  apply perm_elim1 in H4. rewrite H4 in Amax. inversion Amax. } 
{ assert(e=a). apply max_elt_equal_list_minA with (B:=A)(B0:=A0').
  all:auto. subst e. rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. replace (0 =? 0) with true in Heqcall. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hq.
    { destruct s eqn:Hs. 
      { simpl. f_equal. rewrite same_order_diffq_bid. 
    replace (EMatch_bid_obligations_obligation_3 a b l) with
    (EMatch_bid_obligations_obligation_1 b a l). apply perm_add_listA.
    all:auto. }
     { simpl. auto. replace A0' with (delete a (a::A0')). 
        apply perm_remove_tree_deleteA. auto. 
        apply max_elt_in_listA. auto. auto. simpl.
        destruct (ord_eqb a a) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto. 
      }  }
      { simpl. f_equal. rewrite same_order_diffq_bid.
        apply H with (e:=a)(l:=l). all: auto. all:TB.intuition_in_tree.
        eauto. eauto. 
        apply perm_remove_treeA. all:auto.  (*tree remove perm property*)
        apply max_elt_in_listA. auto.
        replace A0' with (delete a (a::A0')). 
        apply perm_remove_tree_deleteA. auto. 
        apply max_elt_in_listA. auto. auto. simpl.
        destruct (ord_eqb a a) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto.
     } auto. auto.
    }
     { simpl. auto. } 
   }
   {  rewrite <- Heqcall. simpl. all:auto. }
{  assert(H5:List.In a (TA.elements A)).
   apply perm_sym in H4.
   apply included_elim2 with (l:=A0').
   unfold perm in H4. move /andP in H4. apply H4. 
   apply TA.max_elt_spec3 in Amax.  
   destruct Amax with (a:=a). auto. eauto with ecda. }
 Qed.

Hint Immediate efficient_correct_askA efficient_correct_bidA : ecda.

Lemma efficient_correct_askA_tree (tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> 
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TA.elements tA) (T_id.elements tA_id) ->
~List.In (otime ord) (timesof (TA.elements tA)) ->
~ List.In (id ord) (ids (TA.elements tA)) ->
perm (TA.elements (At (EMatch_ask tB tA ord tB_id tA_id))) 
(T_id.elements (At_id (EMatch_ask tB tA ord tB_id tA_id))).
Proof. 
intros ok1 ok2 ok3 ok4 H H0 Htime Hid. funelim (EMatch_ask tB tA ord tB_id tA_id). 
destruct (TB.max_elt B) eqn:Bmax.
{ rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice e) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity e) (oquantity a)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. eapply H with (l:=l).  all: auto.
        all:TB.intuition_in_tree. 
        apply perm_remove_treeB. all:auto. apply max_elt_in_listB. auto. 
      }
      { simpl. auto. } 
    }
    { simpl. auto. } apply /eqP. simpl. auto.
  }
  { replace (S n =? 0) with false. simpl. auto. auto. apply perm_addA. all:auto. }
}
{ rewrite <- Heqcall. simpl. apply perm_addA. all:auto. }
Qed.

Lemma efficient_correct_bidA_id (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
Sorted Properties.acompetitive A ->
NoDup (timesof A) ->
NoDup (ids A) ->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
perm (T_id.elements (At_id (EMatch_bid tB tA ord tB_id tA_id))) (Alist (Match_bid B A ord)).
Proof. intros ndtA ndtB ok1 ok2 ok3 ok4 H H0 H1 H2 H3. funelim (EMatch_bid tB tA ord tB_id tA_id). 
destruct (TA.max_elt A) eqn:Amax;destruct A0 as [|a A0'] eqn:HB0.
{ apply TA.max_elt_spec1 in Amax. apply TA.elements_spec1 in Amax.
  apply perm_elim1 in H4. rewrite H4 in Amax. inversion Amax. } 
{ assert(e=a). apply max_elt_equal_list_minA with (B:=A)(B0:=A0').
  all:auto. subst e. rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. replace (0 =? 0) with true in Heqcall. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hq.
    { destruct s eqn:Hs. 
      { simpl. f_equal. rewrite same_order_diffq_bid. 
    replace (EMatch_bid_obligations_obligation_3 a b l) with
    (EMatch_bid_obligations_obligation_2 b a l). apply perm_add_list_id.
    all:auto. apply perm_trans with (y:=(TA.elements A)). eauto. auto. }
     { simpl. auto. replace A0' with (delete a (a::A0')). 
        apply perm_remove_tree_delete_id. auto.
        apply perm_In2 with (l1:=(TA.elements A)). auto.  
        apply max_elt_in_listA. auto. auto. simpl.
        destruct (ord_eqb a a) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto. 
      }  }
      { simpl. f_equal. rewrite same_order_diffq_bid.
        apply H with (e:=a)(l:=l). all: auto. all:TB.intuition_in_tree.
        eauto. eauto. eauto. 
        apply perm_remove_treeA. all:auto.  (*tree remove perm property*)
        apply max_elt_in_listA. auto.
        replace A0' with (delete a (a::A0')). 
        apply perm_remove_tree_deleteA. auto. 
        apply max_elt_in_listA. auto. auto. simpl.
        destruct (ord_eqb a a) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto.
     } auto. auto.
    }
     { simpl. auto. } 
   }
   {  rewrite <- Heqcall. simpl. all:auto. }
{  assert(H5:List.In a (TA.elements A)).
   apply perm_sym in H4.
   apply included_elim2 with (l:=A0').
   unfold perm in H4. move /andP in H4. apply H4. 
   apply TA.max_elt_spec3 in Amax.  
   destruct Amax with (a:=a). auto. eauto with ecda. }
 Qed.


Hint Immediate efficient_correct_askA_tree efficient_correct_bidA_id : ecda.

Lemma efficient_correct_askB_id (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->Sorted Properties.bcompetitive B ->
NoDup (timesof B) ->
NoDup (ids B) ->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
perm (T_id.elements (Bt_id (EMatch_ask tB tA ord tB_id tA_id))) (Blist (Match_ask B A ord)).
Proof. intros ok1 ok2 ok3 ok4 H Htime Hids H0 H1 H2 H3. funelim (EMatch_ask tB tA ord tB_id tA_id). 
destruct (TB.max_elt B) eqn:Bmax;destruct B0 as [|b B0'] eqn:HB0.
{ apply TB.max_elt_spec1 in Bmax. apply TB.elements_spec1 in Bmax.
  apply perm_elim1 in H2. rewrite H2 in Bmax. inversion Bmax. } 
{ assert(e=b).  apply max_elt_equal_list_maxB with (B:=B)(B0:=B0').
  all:auto.  subst e. rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity a)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. f_equal. rewrite same_order_diffq_ask.
        apply H with (e:=b)(l:=l). all: auto. all:T_id.intuition_in_tree.
        eauto. eauto. auto. eauto.
        apply perm_remove_treeB. all:auto.  (*tree remove perm property*)
        apply max_elt_in_listB. auto.
        replace B0' with (delete b (b::B0')). 
        apply perm_remove_tree_deleteB. auto. 
        apply max_elt_in_listB. auto. auto. simpl.
        destruct (ord_eqb b b) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto. 
      } 
      { simpl. auto. replace B0' with (delete b (b::B0')). 
        apply perm_remove_tree_delete_id. auto.
        apply perm_In2 with (l1:=(TB.elements B)). auto. 
        apply max_elt_in_listB. auto. auto. simpl.
        destruct (ord_eqb b b) eqn:Hb. auto. unfold ord_eqb in Hb.
        move /andP in Hb. destruct Hb. split. apply /andP. split.
        apply /andP. split. all:auto. 
      } 
    }
    { simpl. f_equal. rewrite same_order_diffq_ask. 
    replace (EMatch_ask_obligations_obligation_4 a b l) with
    (EMatch_ask_obligations_obligation_1 b a l). 
    apply perm_add_list_id. 
    all:auto. apply perm_trans with (y:=(TB.elements B)). eauto. auto. }
    apply /eqP. simpl. auto.
  }
  { replace (S n =? 0) with false. simpl. auto. auto. }
}
{ rewrite <- Heqcall. simpl. auto. }
{  assert(H5:List.In b (TB.elements B)).
   apply perm_sym in H2.
   apply included_elim2 with (l:=B0').
   unfold perm in H2. move /andP in H2. apply H2. 
   apply TB.max_elt_spec3 in Bmax. 
   destruct Bmax with (a:=b). auto. auto with ecda. } Qed.

Lemma efficient_correct_bidB_tree (tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> 
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TA.elements tA) (T_id.elements tA_id) ->
~List.In (otime ord) (timesof (TB.elements tB)) ->
~ List.In (id ord) (ids (TB.elements tB)) ->
perm (TB.elements (Bt (EMatch_bid tB tA ord tB_id tA_id))) 
(T_id.elements (Bt_id (EMatch_bid tB tA ord tB_id tA_id))).
Proof. 
intros ok1 ok2 ok3 ok4 H H0 Htime Hid. funelim (EMatch_bid tB tA ord tB_id tA_id). 
destruct (TA.max_elt A) eqn:Bmax.
{ rewrite <- Heqcall.
  simpl. destruct (oprice e - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity e)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. auto. }
      {simpl. auto. } } 
      { eapply H with (l:=l).  all: auto.
        all:TB.intuition_in_tree. 
        apply perm_remove_treeA. all:auto. apply max_elt_in_listA. auto. 
      }
      { simpl. auto. } 
    }
    { replace (S n =? 0) with false. simpl. auto. auto. apply perm_addB. all:auto. }
}
{ rewrite <- Heqcall. simpl. apply perm_addB. all:auto. }
Qed.

Hint Immediate efficient_correct_askB_id efficient_correct_bidB_tree : ecda.

Lemma efficient_correct_askB_tree (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->Sorted Properties.bcompetitive B ->
NoDup (timesof B) ->
NoDup (ids B) ->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
perm (T_id.elements (Bt_id (EMatch_ask tB tA ord tB_id tA_id))) 
 (TB.elements (Bt (EMatch_ask tB tA ord tB_id tA_id))).
Proof. intros ok1 ok2 ok3 ok4 H Htime Hids H0 H1 H2 H3.
assert(perm (T_id.elements (Bt_id (EMatch_ask tB tA ord tB_id tA_id))) (Blist (Match_ask B A ord))). auto with ecda. 
assert(perm (TB.elements (Bt (EMatch_ask tB tA ord tB_id tA_id))) (Blist (Match_ask B A ord))). auto with ecda. eauto. Qed.

Lemma efficient_correct_askA_id (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->Sorted Properties.bcompetitive B ->
NoDup (timesof B) ->
NoDup (timesof (ord::A)) ->
NoDup (ids (ord::A)) ->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
perm (T_id.elements (At_id (EMatch_ask tB tA ord tB_id tA_id))) 
(Alist (Match_ask B A ord)).
Proof. intros. assert(perm (TA.elements (At (EMatch_ask tB tA ord tB_id tA_id))) (T_id.elements (At_id (EMatch_ask tB tA ord tB_id tA_id)))). 
apply efficient_correct_askA_tree. all: auto. 
 simpl in H5. intro. apply nodup_elim2 in H5.
 destruct H5. apply timesof_perm in H10.
 apply perm_elim2 in H10. unfold "[=]" in H10. destruct H10. eauto.
simpl in H6. intro. apply nodup_elim2 in H6.
destruct H6. apply ids_perm in H10.
 apply perm_elim2 in H10. unfold "[=]" in H10. destruct H10. eauto.
 assert(perm (TA.elements (At (EMatch_ask tB tA ord tB_id tA_id)))
  (Alist (Match_ask B A ord))). 
  apply efficient_correct_askA. all:auto. Qed.

Lemma efficient_correct_bidB_id (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
NoDup (ids (ord::B)) ->
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
Sorted Properties.acompetitive A ->
NoDup (timesof A) ->
NoDup (ids A) ->
NoDup (timesof (ord::B)) ->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
perm (T_id.elements (Bt_id (EMatch_bid tB tA ord tB_id tA_id)))
  (Blist (Match_bid B A ord)).
Proof. intro ndi. intros.
    assert(perm (TB.elements (Bt (EMatch_bid tB tA ord tB_id tA_id)))
  (Blist (Match_bid B A ord))).
  apply efficient_correct_bidB. all:auto.
  assert(perm (TB.elements (Bt (EMatch_bid tB tA ord tB_id tA_id)))
  (T_id.elements (Bt_id (EMatch_bid tB tA ord tB_id tA_id)))).
  apply efficient_correct_bidB_tree. all:auto.
  simpl in H6. apply nodup_elim2 in H6. intro Hn. destruct H6.
  apply timesof_perm in H8. apply perm_elim2 in H8. unfold "[=]" in H8.
  destruct H8. eauto. 
  simpl in ndi. apply nodup_elim2 in ndi. intro Hn. destruct ndi.
  apply ids_perm in H8. apply perm_elim2 in H8. unfold "[=]" in H8.
  destruct H8. eauto.
Qed.

Hint Immediate efficient_correct_askB_id efficient_correct_askA_id: ecda.

Lemma efficient_correct_askAtOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
TA.Ok (At (EMatch_ask tB tA ord tB_id tA_id)).
Proof. 
intros ok1 ok2 ok3 ok4. funelim (EMatch_ask tB tA ord tB_id tA_id). 
destruct (TB.max_elt B) eqn:Bmax.
{ rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice e) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity e) (oquantity a)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. eapply H with (l:=l). all:intuition. 
      }
      { simpl. auto. } 
    }
    { simpl. auto. } apply /eqP. simpl. auto.
  }
  { replace (S n =? 0) with false. simpl. all:intuition. }
}
{ rewrite <- Heqcall. simpl. all:intuition. }
Qed.

Lemma efficient_correct_askAidOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
T_id.Ok (At_id (EMatch_ask tB tA ord tB_id tA_id)).
Proof. 
intros ok1 ok2 ok3 ok4. funelim (EMatch_ask tB tA ord tB_id tA_id). 
destruct (TB.max_elt B) eqn:Bmax.
{ rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice e) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity e) (oquantity a)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. eapply H with (l:=l). all:intuition. 
      }
      { simpl. auto. } 
    }
    { simpl. auto. } apply /eqP. simpl. auto.
  }
  { replace (S n =? 0) with false. simpl. all:intuition. }
}
{ rewrite <- Heqcall. simpl. all:intuition. }
Qed.

Lemma efficient_correct_askBtOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
TB.Ok (Bt (EMatch_ask tB tA ord tB_id tA_id)).
Proof. 
intros ok1 ok2 ok3 ok4. funelim (EMatch_ask tB tA ord tB_id tA_id). 
destruct (TB.max_elt B) eqn:Bmax.
{ rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice e) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity e) (oquantity a)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. eapply H with (l:=l). all:intuition. 
      }
      { simpl. all:intuition.  } 
    }
    { simpl. all:intuition. } apply /eqP. simpl. auto.
  }
  { replace (S n =? 0) with false. simpl. all:intuition. }
}
{ rewrite <- Heqcall. simpl. all:intuition. }
Qed.


Lemma efficient_correct_askBidOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
T_id.Ok (Bt_id (EMatch_ask tB tA ord tB_id tA_id)).
Proof. 
intros ok1 ok2 ok3 ok4. funelim (EMatch_ask tB tA ord tB_id tA_id). 
destruct (TB.max_elt B) eqn:Bmax.
{ rewrite <- Heqcall.
  simpl. destruct (oprice a - oprice e) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity e) (oquantity a)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. eapply H with (l:=l). all:intuition. 
      }
      { simpl. all:intuition.  } 
    }
    { simpl. all:intuition. } apply /eqP. simpl. auto.
  }
  { replace (S n =? 0) with false. simpl. all:intuition. }
}
{ rewrite <- Heqcall. simpl. all:intuition. }
Qed.

Hint Immediate efficient_correct_askAtOk efficient_correct_askAidOk 
efficient_correct_askBtOk efficient_correct_askBidOk :ecda.


Lemma efficient_correct_bidBtOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
TB.Ok (Bt (EMatch_bid tB tA ord tB_id tA_id)).
Proof. 
intros ok1 ok2 ok3 ok4. funelim (EMatch_bid tB tA ord tB_id tA_id). 
destruct (TA.max_elt A) eqn:Bmax.
{ rewrite <- Heqcall.
  simpl. destruct (oprice e - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity e)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. all:intuition. }
      { simpl. all:intuition.  } }
    { simpl.  eapply H with (l:=l). all:intuition. } apply /eqP. simpl. auto. }
  { replace (S n =? 0) with false. simpl. all:intuition. }
}
{ rewrite <- Heqcall. simpl. all:intuition. }
Qed.


Lemma efficient_correct_bidAtOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
TA.Ok (At (EMatch_bid tB tA ord tB_id tA_id)).
Proof. 
intros ok1 ok2 ok3 ok4. funelim (EMatch_bid tB tA ord tB_id tA_id). 
destruct (TA.max_elt A) eqn:Bmax.
{ rewrite <- Heqcall.
  simpl. destruct (oprice e - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity e)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. all:intuition. }
      { simpl. all:intuition.  } }
    { simpl.  eapply H with (l:=l). all:intuition. } apply /eqP. simpl. auto. }
  { replace (S n =? 0) with false. simpl. all:intuition. }
}
{ rewrite <- Heqcall. simpl. all:intuition. }
Qed.

Lemma efficient_correct_bidBidOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
T_id.Ok (Bt_id (EMatch_bid tB tA ord tB_id tA_id)).
Proof. 
intros ok1 ok2 ok3 ok4. funelim (EMatch_bid tB tA ord tB_id tA_id). 
destruct (TA.max_elt A) eqn:Bmax.
{ rewrite <- Heqcall.
  simpl. destruct (oprice e - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity e)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. all:intuition. }
      { simpl. all:intuition.  } }
    { simpl.  eapply H with (l:=l). all:intuition. } apply /eqP. simpl. auto. }
  { replace (S n =? 0) with false. simpl. all:intuition. }
}
{ rewrite <- Heqcall. simpl. all:intuition. }
Qed.

Lemma efficient_correct_bidAidOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
T_id.Ok (At_id (EMatch_bid tB tA ord tB_id tA_id)).
Proof. 
intros ok1 ok2 ok3 ok4. funelim (EMatch_bid tB tA ord tB_id tA_id). 
destruct (TA.max_elt A) eqn:Bmax.
{ rewrite <- Heqcall.
  simpl. destruct (oprice e - oprice b) eqn:Hprice. 
  { replace (0 =? 0) with true. simpl.
    destruct (lt_eq_lt_dec (oquantity b) (oquantity e)) eqn:Hq1.
    { destruct s eqn:Hs.
      { simpl. all:intuition. }
      { simpl. all:intuition.  } }
    { simpl.  eapply H with (l:=l). all:intuition. } apply /eqP. simpl. auto. }
  { replace (S n =? 0) with false. simpl. all:intuition. }
}
{ rewrite <- Heqcall. simpl. all:intuition. }
Qed.


Hint Immediate efficient_correct_bidAtOk efficient_correct_bidAidOk 
efficient_correct_bidBtOk efficient_correct_bidBidOk :ecda.


Lemma efficient_correct_del (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A -> Mt (EDel_order tB tA (id ord) tB_id tA_id) = nil.
Proof.  unfold EDel_order. destruct (search_order tB_id (id ord)) eqn:Hbe.
destruct (search_order tA_id (id ord)) eqn:Hae. intros. simpl. auto. simpl. auto.
destruct (search_order tA_id (id ord)) eqn:Hae. simpl. auto. simpl. auto. Qed.


Lemma efficient_correct_delA_tree (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A -> 
perm (TA.elements (At (EDel_order tB tA (id ord) tB_id tA_id))) 
(T_id.elements (At_id (EDel_order tB tA (id ord) tB_id tA_id))).
Proof.  unfold EDel_order. intros H1 H2 H3 H4 H5 H6 H7 H8.  destruct (search_order tB_id (id ord)) eqn:HB;
destruct (search_order tA_id (id ord)) eqn:HA.
 - apply search_order_In in HB. apply search_order_In in HA.
   simpl. apply perm_remove_treeA. all:auto. 
   apply perm_elim with (a:=e0) in H7. apply count_Intree_id in HA.
   rewrite HA in H7. assert(count e0 (TA.elements tA) >= 1).
   lia. apply countP1a in H. auto. auto.
 - simpl. auto.
 - apply search_order_In in HA. 
   simpl. apply perm_remove_treeA. all:auto. 
   apply perm_elim with (a:=e) in H7. apply count_Intree_id in HA.
   rewrite HA in H7. assert(count e (TA.elements tA) >= 1).
   lia. apply countP1a in H. auto. auto.
 - simpl. auto.
Qed. 

Hint Immediate efficient_correct_del efficient_correct_delA_tree :ecda.


Lemma delete_order_nIn A e0:
~List.In (id e0) (ids A) -> delete_order A (id e0) = A.
Proof. induction A. simpl. auto. 
intros. simpl in H. apply in_inv4 in H. destruct H.
simpl. replace (id a =? id e0) with false. f_equal. apply IHA.
auto. symmetry. apply /eqP. auto. Qed.


Lemma delete_order_delete A e0:
List.In e0 A ->  NoDup (ids A)  -> delete_order A (id e0) = delete e0 A.
Proof. intros Hin H. induction A. 
  - simpl. auto.
  - simpl. destruct (id a =? id e0) eqn:Ha;destruct (ord_eqb e0 a) eqn:Hb.
    * rewrite delete_order_nIn. simpl in H. intro.
      apply nodup_elim2 with (a:= id a) in H. move /eqP in Hb. subst e0.
      destruct (H H0). auto.
    * simpl in Hin. destruct Hin. subst. move /eqP in Hb. destruct Hb. auto.
      simpl in H. apply nodup_elim2 with (a:= id a) in H as H2. 
      move /eqP in Ha. apply ids_intro in H0. rewrite Ha in H2. 
      destruct (H2 H0).
    * move /eqP in Hb. subst a. move /eqP in Ha. lia.
    * f_equal. apply IHA. simpl in Hin. destruct Hin. subst. move /eqP in Hb.
      destruct Hb. auto. auto. simpl in H. eauto. Qed.

Lemma efficient_correct_delA (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> 
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A -> 
perm (TA.elements (At (EDel_order tB tA (id ord) tB_id tA_id))) (Alist (Del_order B A (id ord))).
Proof. intros ok1 ok2 ok3 ok4 H2 H3 H4 HA. unfold EDel_order.
 simpl. assert(Hperm:=HA). destruct (search_order tB_id (id ord)) eqn:Hbe;
 destruct (search_order tA_id (id ord)) eqn:Hae. 
 - simpl. apply search_order_id in Hae as Hid1. rewrite <- Hid1.
   apply search_order_In in Hbe. apply search_order_In in Hae. 
   assert(He0: List.In e0 A). apply perm_In2 with (l1:=(T_id.elements tA_id)).
   eauto. apply T_id.elements_spec_tree. auto. 
   assert(perm (T_id.elements (T_id.remove e0 tA_id)) 
   (delete_order A (id e0))). apply perm_remove_tree_delete_order_id. all:auto.
   apply perm_In2 with (l1:=A). eauto. auto.
   assert(perm (TA.elements (TA.remove e0 tA)) 
   (T_id.elements (T_id.remove e0 tA_id))). 
   apply perm_remove_treeA. all:auto.
   apply perm_In2 with (l1:=A). eauto. auto.
 - simpl. apply search_order_In in Hbe. apply search_order_Leaf in Hae.
   rewrite delete_order_nIn. assert(Hperm2: perm (T_id.elements tA_id) A).
   eauto. apply ids_perm in Hperm2. intro. destruct Hae. 
   apply perm_elim2 in Hperm2. unfold "[=]" in Hperm2.
   destruct Hperm2. eauto.  auto. auto.
 - simpl. apply search_order_id in Hae as Hid1. apply search_order_In in Hae.
   rewrite <- Hid1. assert(He0: List.In e A). 
   apply perm_In2 with (l1:=(T_id.elements tA_id)).
   eauto. apply T_id.elements_spec_tree. auto.
   assert(perm (T_id.elements (T_id.remove e tA_id)) 
   (delete_order A (id e))). apply perm_remove_tree_delete_order_id. all:auto.
   apply perm_In2 with (l1:=A). eauto. auto.
   assert(perm (TA.elements (TA.remove e tA)) 
   (T_id.elements (T_id.remove e tA_id))). 
   apply perm_remove_treeA. all:auto.
   apply perm_In2 with (l1:=A). eauto. auto.
 - simpl. apply search_order_Leaf in Hae.
   rewrite delete_order_nIn. assert(Hperm2: perm (T_id.elements tA_id) A).
   eauto. apply ids_perm in Hperm2. intro. destruct Hae. 
   apply perm_elim2 in Hperm2. unfold "[=]" in Hperm2.
   destruct Hperm2. eauto.  auto. auto.
Qed.

Lemma efficient_correct_delA_id (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> 
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A -> 
perm (T_id.elements (At_id (EDel_order tB tA (id ord) tB_id tA_id))) (Alist (Del_order B A (id ord))).
Proof. intros. assert(perm (TA.elements (At (EDel_order tB tA (id ord) tB_id tA_id))) (Alist (Del_order B A (id ord)))).
apply efficient_correct_delA. all:auto.
assert(perm (TA.elements (At (EDel_order tB tA (id ord) tB_id tA_id))) 
(T_id.elements (At_id (EDel_order tB tA (id ord) tB_id tA_id)))).
apply efficient_correct_delA_tree with (A:=A)(B:=B). all:auto. Qed.


Hint Immediate efficient_correct_delA efficient_correct_delA_id :ecda.


Lemma efficient_correct_delB_tree (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A -> 
perm (TB.elements (Bt (EDel_order tB tA (id ord) tB_id tA_id))) 
(T_id.elements (Bt_id (EDel_order tB tA (id ord) tB_id tA_id))).
Proof.  unfold EDel_order. intros H1 H2 H3 H4 H5 H6 H7 H8. 
destruct (search_order tB_id (id ord)) eqn:HB;
destruct (search_order tA_id (id ord)) eqn:HA.
 - apply search_order_In in HB. apply search_order_In in HA.
   simpl. apply perm_remove_treeB. all:auto. 
   apply perm_In2 with (l1:=(T_id.elements tB_id)). auto. 
   apply T_id.elements_spec_tree. auto. 
 - apply search_order_In in HB. 
   simpl. apply perm_remove_treeB. all:auto.
   apply perm_In2 with (l1:=(T_id.elements tB_id)). auto. 
   apply T_id.elements_spec_tree. auto.  
 - simpl. auto.
 - simpl. auto.
Qed. 

Lemma efficient_correct_delB (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> 
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A -> 
perm (TB.elements (Bt (EDel_order tB tA (id ord) tB_id tA_id))) (Blist (Del_order B A (id ord))).
Proof. intros ok1 ok2 ok3 ok4 H2 HA H3 H4. unfold EDel_order.
 simpl. assert(Hperm:=HA). destruct (search_order tB_id (id ord)) eqn:Hbe;
 destruct (search_order tA_id (id ord)) eqn:Hae. 
 - simpl. apply search_order_id in Hbe as Hid1. rewrite <- Hid1.
   apply search_order_In in Hbe. apply search_order_In in Hae. 
   assert(He0: List.In e B). apply perm_In2 with (l1:=(T_id.elements tB_id)).
   eauto. apply T_id.elements_spec_tree. auto.
      assert(perm (T_id.elements (T_id.remove e tB_id)) 
   (delete_order B (id e))). apply perm_remove_tree_delete_order_id. all:auto.
   apply perm_In2 with (l1:=B). eauto. auto.
   assert(perm (TB.elements (TB.remove e tB)) 
   (T_id.elements (T_id.remove e tB_id))). 
   apply perm_remove_treeB. all:auto.
   apply perm_In2 with (l1:=B). eauto. auto.
 - simpl. apply search_order_id in Hbe as Hid1. apply search_order_In in Hbe.
   rewrite <- Hid1. assert(He0: List.In e B). 
   apply perm_In2 with (l1:=(T_id.elements tB_id)).
   eauto. apply T_id.elements_spec_tree. auto.
      assert(perm (T_id.elements (T_id.remove e tB_id)) 
   (delete_order B (id e))). apply perm_remove_tree_delete_order_id. all:auto.
   apply perm_In2 with (l1:=B). eauto. auto.
   assert(perm (TB.elements (TB.remove e tB)) 
   (T_id.elements (T_id.remove e tB_id))). 
   apply perm_remove_treeB. all:auto.
   apply perm_In2 with (l1:=B). eauto. auto.
 - simpl. apply search_order_In in Hae. apply search_order_Leaf in Hbe.
   rewrite delete_order_nIn. assert(Hperm2: perm (T_id.elements tB_id) B).
   eauto. apply ids_perm in Hperm2. intro. destruct Hbe. 
   apply perm_elim2 in Hperm2. unfold "[=]" in Hperm2.
   destruct Hperm2. eauto.  auto. auto.
 - simpl. apply search_order_Leaf in Hbe.
   rewrite delete_order_nIn. assert(Hperm2: perm (T_id.elements tB_id) B).
   eauto. apply ids_perm in Hperm2. intro. destruct Hbe. 
   apply perm_elim2 in Hperm2. unfold "[=]" in Hperm2.
   destruct Hperm2. eauto.  auto. auto.
Qed.

Lemma efficient_correct_delB_id (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> 
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A -> 
perm (T_id.elements (Bt_id (EDel_order tB tA (id ord) tB_id tA_id))) (Blist (Del_order B A (id ord))).
Proof. intros. assert(perm (TB.elements (Bt (EDel_order tB tA (id ord) tB_id tA_id))) (Blist (Del_order B A (id ord)))).
apply efficient_correct_delB. all:auto.
assert(perm (TB.elements (Bt (EDel_order tB tA (id ord) tB_id tA_id))) 
(T_id.elements (Bt_id (EDel_order tB tA (id ord) tB_id tA_id)))).
apply efficient_correct_delB_tree with (A:=A)(B:=B). all:auto. Qed.


Hint Immediate efficient_correct_delB efficient_correct_delB_id
efficient_correct_delB_tree :ecda.

Lemma efficient_correct_delBtOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> 
TB.Ok ((Bt (EDel_order tB tA (id ord) tB_id tA_id))).
Proof. intros. unfold EDel_order. 
destruct (search_order tB_id (id ord)) eqn:Hbe;
 destruct (search_order tA_id (id ord)) eqn:Hae.  
 - simpl. intuition.
 - simpl. intuition.
 - simpl. intuition.
 - simpl. intuition.
Qed.

Lemma efficient_correct_delAtOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> 
TA.Ok ((At (EDel_order tB tA (id ord) tB_id tA_id))).
Proof. intros. unfold EDel_order. 
destruct (search_order tB_id (id ord)) eqn:Hbe;
 destruct (search_order tA_id (id ord)) eqn:Hae.  
 - simpl. intuition.
 - simpl. intuition.
 - simpl. intuition.
 - simpl. intuition.
Qed.

Lemma efficient_correct_delAidOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> 
T_id.Ok ((At_id (EDel_order tB tA (id ord) tB_id tA_id))).
Proof. intros. unfold EDel_order. 
destruct (search_order tB_id (id ord)) eqn:Hbe;
 destruct (search_order tA_id (id ord)) eqn:Hae.  
 - simpl. intuition.
 - simpl. intuition.
 - simpl. intuition.
 - simpl. intuition.
Qed.

Lemma efficient_correct_delBidOk (A B: list order)(tB: TB.t)(tA: TA.t)(ord:order)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA -> 
T_id.Ok ((Bt_id (EDel_order tB tA (id ord) tB_id tA_id))).
Proof. intros. unfold EDel_order. 
destruct (search_order tB_id (id ord)) eqn:Hbe;
 destruct (search_order tA_id (id ord)) eqn:Hae.  
 - simpl. intuition.
 - simpl. intuition.
 - simpl. intuition.
 - simpl. intuition.
Qed.

Hint Immediate efficient_correct_delBidOk efficient_correct_delAidOk
efficient_correct_delBtOk efficient_correct_delAtOk :ecda.


Definition eProcess_instruction (B: TB.t)(A: TA.t)(tau: instruction)(B_id A_id : T_id.t):
((TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)) :=
match (cmd tau) with
|del => EDel_order B A (id (ord tau)) B_id A_id
|buy => EMatch_bid B A (ord tau) B_id A_id
|sell => EMatch_ask B A (ord tau) B_id A_id
end.


Fixpoint ploop (P:TB.t -> TA.t -> instruction ->  T_id.t -> T_id.t -> 
                  TB.t * TA.t * T_id.t * T_id.t * list transaction) 
                  (I:list instruction):((TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)).
destruct I as [|i I'] eqn:H.
exact (TB.empty, TA.empty, T_id.empty, T_id.empty, nil).
refine (let BAM := (ploop P I') in (P (Bt BAM) (At BAM) i (Bt_id BAM) (At_id BAM))). Defined.

Definition ploop2 (I:list instruction):(TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction) := fold_left (fun (accprod: _ * _ * _ * _ * _) tau => let (t_4, _) := accprod in let (t_3, ta_id) := t_4 in let (t_2, tb_id) := t_3 in let (tb, ta) := t_2 in  eProcess_instruction tb ta tau tb_id ta_id) I (TB.empty, TA.empty, T_id.empty, T_id.empty, nil).


Extraction ploop2.

Theorem efficient_correct_OK (A B: list order)(tB: TB.t)(tA: TA.t)(tau: instruction)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
let eBAM := eProcess_instruction tB tA tau tB_id tA_id in 
TA.Ok (At eBAM)/\TB.Ok (Bt eBAM)/\T_id.Ok (At_id eBAM)/\T_id.Ok (Bt_id eBAM).
Proof. unfold eProcess_instruction. destruct (cmd tau). 
- simpl. intros. repeat split. all:auto with ecda.
- simpl. intros. repeat split. all:auto with ecda.
- simpl. intros. repeat split. all:auto with ecda.
Qed.

Theorem efficient_correct_cmdB (A B: list order)(tB: TB.t)(tA: TA.t)(tau: instruction)(tB_id tA_id : T_id.t):
cmd tau = buy -> T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
NoDup (timesof A) -> NoDup (timesof ((ord tau)::B)) ->
NoDup (ids A) -> NoDup (ids ((ord tau)::B)) ->
(*admissible (fst (Absorb B A tau)) (snd (Absorb B A tau))->*)
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
let eBAM := eProcess_instruction tB tA tau tB_id tA_id in 
let BAM := Process_instruction B A tau in 
Mlist BAM = Mt eBAM/\
perm (Alist BAM) (TA.elements (At eBAM))/\
perm (Blist BAM) (TB.elements (Bt eBAM))/\
perm (Alist BAM) (T_id.elements (At_id eBAM))/\
perm (Blist BAM) (T_id.elements (Bt_id eBAM))/\
TA.Ok (At eBAM)/\TB.Ok (Bt eBAM)/\
T_id.Ok (At_id eBAM)/\T_id.Ok (Bt_id eBAM).
Proof. intro cmdb. 
simpl. unfold eProcess_instruction. unfold Process_instruction.
simpl. intros. rewrite cmdb. repeat split. all: auto with ecda.
  * symmetry. eapply efficient_correct_bid. all:auto.
    apply perm_nodup with (l:=timesof A). apply timesof_perm. eauto. 
    eauto.
    apply sort_correct. apply acompetitive_P. apply acompetitive_P.
  * apply perm_sym. eapply efficient_correct_bidA. all:auto.
    apply sort_correct. apply acompetitive_P. apply acompetitive_P.
    apply perm_nodup with (l:=timesof A). apply timesof_perm. eauto. 
    eauto.
  * apply perm_sym. eapply efficient_correct_bidB. all:auto.
    apply perm_nodup with (l:=timesof A). apply timesof_perm. eauto. 
    eauto.
    apply sort_correct. apply acompetitive_P. apply acompetitive_P.
  * apply perm_sym. eapply efficient_correct_bidA_id. all:auto.
    apply sort_correct. apply acompetitive_P. apply acompetitive_P.
    apply perm_nodup with (l:=timesof A). apply timesof_perm. eauto. 
    auto.
    apply perm_nodup with (l:=ids A). apply ids_perm. eauto. 
    auto.
  * apply perm_sym. eapply efficient_correct_bidB_id. all:auto.
    apply sort_correct. apply acompetitive_P. apply acompetitive_P.
    apply perm_nodup with (l:=timesof A). apply timesof_perm. eauto. 
    auto.
    apply perm_nodup with (l:=ids A). apply ids_perm. eauto. 
    auto.
Qed. 

Theorem efficient_correct (A B: list order)(tB: TB.t)(tA: TA.t)(tau: instruction)(tB_id tA_id : T_id.t):
T_id.Ok tA_id -> T_id.Ok tB_id -> TB.Ok tB -> TA.Ok tA ->
admissible (fst (Absorb B A tau)) (snd (Absorb B A tau))->
perm (TB.elements tB) (T_id.elements tB_id) ->
perm (TB.elements tB) B ->
perm (TA.elements tA) (T_id.elements tA_id) ->
perm (TA.elements tA) A ->
let eBAM := eProcess_instruction tB tA tau tB_id tA_id in 
let BAM := Process_instruction B A tau in 
Mlist BAM = Mt eBAM/\
perm (Alist BAM) (TA.elements (At eBAM))/\
perm (Blist BAM) (TB.elements (Bt eBAM))/\
perm (Alist BAM) (T_id.elements (At_id eBAM))/\
perm (Blist BAM) (T_id.elements (Bt_id eBAM))/\
TA.Ok (At eBAM)/\TB.Ok (Bt eBAM)/\
T_id.Ok (At_id eBAM)/\T_id.Ok (Bt_id eBAM).
Proof. 
unfold admissible. unfold Absorb. destruct tau. destruct cmd.
- simpl. unfold eProcess_instruction. unfold Process_instruction.
  simpl. intros. repeat split. all: auto with ecda.
  * symmetry. eapply efficient_correct_bid. all:auto.
    apply perm_nodup with (l:=timesof A). apply timesof_perm. eauto. 
    destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    eauto.
    apply sort_correct. apply acompetitive_P. apply acompetitive_P.
  * apply perm_sym. eapply efficient_correct_bidA. all:auto.
    apply sort_correct. apply acompetitive_P. apply acompetitive_P.
    apply perm_nodup with (l:=timesof A). apply timesof_perm. eauto. 
    destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    eauto. apply H3.
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    apply perm_sym. eapply efficient_correct_bidB. all:auto.
    apply perm_nodup with (l:=timesof A). apply timesof_perm. eauto. 
    eauto.
    apply sort_correct. apply acompetitive_P. apply acompetitive_P.
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    apply perm_sym. eapply efficient_correct_bidA_id. all:auto.
    apply sort_correct. apply acompetitive_P. apply acompetitive_P.
    apply perm_nodup with (l:=timesof A). apply timesof_perm. eauto. 
    auto.
    apply perm_nodup with (l:=ids A). apply ids_perm. eauto. 
    auto.
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    apply perm_sym. eapply efficient_correct_bidB_id. all:auto.
    apply sort_correct. apply acompetitive_P. apply acompetitive_P.
    apply perm_nodup with (l:=timesof A). apply timesof_perm. eauto. 
    auto.
    apply perm_nodup with (l:=ids A). apply ids_perm. eauto. 
    auto.
- simpl. unfold eProcess_instruction. unfold Process_instruction.
  simpl. intros. repeat split. all: auto with ecda.
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    symmetry. eapply efficient_correct_ask. all:auto.
    apply perm_nodup with (l:=timesof B). apply timesof_perm. eauto. auto.
    apply sort_correct. apply bcompetitive_P. apply bcompetitive_P.
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    apply perm_sym. eapply efficient_correct_askA. all:auto.
    apply sort_correct. apply bcompetitive_P. apply bcompetitive_P.
    apply perm_nodup with (l:=timesof B). apply timesof_perm. eauto. 
    eauto.
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    apply perm_sym. eapply efficient_correct_askB. all:auto.
    apply sort_correct. apply bcompetitive_P. apply bcompetitive_P.
    apply perm_nodup with (l:=timesof B). apply timesof_perm. eauto. 
    eauto.
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    apply perm_sym. eapply efficient_correct_askA_id. all:auto.
    apply sort_correct. apply bcompetitive_P. apply bcompetitive_P.
    apply perm_nodup with (l:=timesof B). apply timesof_perm. eauto. 
    auto.
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    apply perm_sym. eapply efficient_correct_askB_id. all:auto.
    apply sort_correct. apply bcompetitive_P. apply bcompetitive_P.
    apply perm_nodup with (l:=timesof B). apply timesof_perm. eauto. 
    auto.
    apply perm_nodup with (l:=ids B). apply ids_perm. eauto. 
    auto.
- simpl. unfold eProcess_instruction. unfold Process_instruction.
  simpl. intros. repeat split. all: auto with ecda.
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    symmetry. eapply efficient_correct_del. all:auto.
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    apply perm_sym. eapply efficient_correct_delA. all:auto. 
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    apply perm_sym. eapply efficient_correct_delB. all:auto. 
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    apply perm_sym. eapply efficient_correct_delA_id. all:auto.
  * destruct H3 as [H3 n1]. destruct n1 as [n2 n1]. destruct n1 as [n3 n1].
    apply perm_sym. eapply efficient_correct_delB_id. all:auto.
Qed.


Fixpoint eiterate (P: (TB.t)->(TA.t) -> instruction ->  (T_id.t) -> (T_id.t) ->((TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)))
(I : list instruction)(k:nat) :=
match k with
|0 => (TB.empty , TA.empty, T_id.empty, T_id.empty, nil) 
| S k' =>  let it:=(eiterate P I k') in P (Bt it) (At it) 
    (nth k' I tau0) (Bt_id it) (At_id it)
end.

Definition eiterated (P: (TB.t)->(TA.t) -> instruction ->  (T_id.t) -> (T_id.t) ->((TB.t)*(TA.t)*(T_id.t)*(T_id.t)*(list transaction)))
(I : list instruction)(k:nat) := 
if (Nat.ltb (length I) k) then (TB.empty , TA.empty, T_id.empty, T_id.empty, nil)  else eiterate P I k.

Lemma iterated_correct_aux (I : list instruction)(k:nat):
structured I  -> let P1 := Process_instruction in 
                      let P2 := eProcess_instruction in 
(Mlist (iterated P1 I k)) = (Mt (eiterated P2 I k))/\
perm (Blist (iterated P1 I k)) (TB.elements (Bt (eiterated P2 I k)))/\
perm (Alist (iterated P1 I k)) (TA.elements (At (eiterated P2 I k)))/\
perm (Blist (iterated P1 I k)) (T_id.elements (Bt_id (eiterated P2 I k)))/\
perm (Alist (iterated P1 I k)) (T_id.elements (At_id (eiterated P2 I k)))/\
TA.Ok (At (eiterated P2 I k))/\TB.Ok (Bt (eiterated P2 I k))/\
T_id.Ok (At_id (eiterated P2 I k))/\T_id.Ok (Bt_id (eiterated P2 I k))/\
NSS2021_lib.Subset (timesof (Blist (iterated P1 I k))) (timesof (tilln (orders I) (k-1)))/\
NSS2021_lib.Subset (timesof (Alist (iterated P1 I k))) (timesof (tilln (orders I) (k-1)))/\
(not (matchable (Blist (iterated P1 I k)) (Alist (iterated P1 I k))))/\
(NoDup (ids (Blist (iterated P1 I k)))) /\ (NoDup (ids (Alist (iterated P1 I k))))/\
(NoDup (timesof (Blist (iterated P1 I k)))) /\ (NoDup (timesof (Alist (iterated P1 I k))))/\  
(NSS2021_lib.Subset (ids (Blist (iterated P1 I k))) (ids (tilln (orders I) (k-1))))/\
(NSS2021_lib.Subset (ids (Alist (iterated P1 I k))) (ids (tilln (orders I) (k-1))))/\
(cmd (nth (k-1) I tau0) = del -> k>0 ->
   ~List.In (id (ord (nth (k-1) I tau0))) (ids (Blist (iterated P1 I k)))) /\
(cmd (nth (k-1) I tau0) = del -> k>0 ->
   ~List.In (id (ord (nth (k-1) I tau0))) (ids (Alist (iterated P1 I k)))).
Proof.
    { assert (~ matchable nil nil) as Hnil.
      { intro. unfold matchable in H. firstorder. }
      induction k. 
        { intros H H0 H1. simpl. repeat split. 
          all:auto. all:intuition. }
        { (*induction step*) 
          unfold iterated. unfold eiterated. intros H.
          destruct(Nat.ltb (|I|) (S k)) eqn:Hlength.
          { simpl. repeat split. all:auto. all:intuition. }
          { (*-------The case when length(I)>=k+1-----------*)
            move /leP in Hlength. 
            assert(S k <= (| I |)) as H2. lia.
            revert IHk. unfold iterated. unfold eiterated.
            destruct (Nat.ltb (| I |)) eqn:Hl2.
            { move /ltP in Hl2. lia. }
            { set(B10:= (Blist (iterate Process_instruction I k))).  
              set(A10:= (Alist (iterate Process_instruction I k))).
              set(B20:= TB.elements (Bt (eiterate eProcess_instruction I k))). 
              set(A20:= TA.elements (At (eiterate eProcess_instruction I k))).
              replace (S k -1) with k. 2:{  lia. }
              set (tau:=(nth k I tau0)). 
              intro IHk. (*assert(Hstruct:=H1). assert(Hstruct2:=H1).*)
              specialize (IHk H). (*specialize (IHk H0). specialize (IHk H1).*)
              destruct IHk as [kmperm H3]. destruct H3 as [kbperm H3].
              destruct H3 as [kaperm H3]. destruct H3 as [kbt H3].
              destruct H3 as [kat H3].
              destruct H3 as [knm H3]. destruct H3 as [knbdi H3].
              destruct H3 as [kndai H3]. destruct H3 as [kndbt H3]. 
              destruct H3 as [kndat H3]. destruct H3 as [kinclidb H3].
              destruct H3 as [kinclida H3]. destruct H3 as [ndib H3].
              destruct H3 as [ndia H3]. destruct H3 as [ndtb H3].
              destruct H3 as [ndta kdela].
              
              (*First to prove admissible*)
              assert(Had:admissible 
              (fst (Absorb (Blist (iterate Process_instruction I k))
                           (Alist (iterate Process_instruction I k)) 
                           (nth k I tau0)))
              (snd (Absorb (Blist (iterate Process_instruction I k))
                           (Alist (iterate Process_instruction I k)) 
                           (nth k I tau0)))).
        { (*To start admissible*) 
         assert(Hstruct:=H).
         unfold admissible. unfold Absorb. repeat split.
         { (*Nodup ids B *)
           destruct k eqn: hk. 
           { destruct (cmd (nth 0 I tau0)) eqn:cmdt. all:simpl;auto. }
           { unfold structured in H. destruct H as [Hid Hul].
             specialize (Hid (S n)). replace (S (S n)) with (S n +1) in H2.
             apply Hid in H2. destruct H2 as [H2 | H2]. 
             (*Three cases of structred*)
             (*case 1: delete*) 
             -- apply Absorb_del_nodup_id. all:auto. 
             (*case 2: structured*) 
             -- destruct H2 as [H2 | H2]. 
             --- destruct kdela as [idBsub kdela]. 
                 destruct kdela as [idAsub kdela].
                 apply Absorb_notIn_nodup_id. all: auto. 
             (*Case 3: structed*)
             --- destruct H2 as [H2a H2b]. assert(S n >0) as Hn. lia.
                 apply Absorb_notIn_nodup_id. all: auto.
                 subst tau. rewrite H2a. apply kdela. auto. auto.
                 subst tau. rewrite H2a. apply kdela. auto. auto. 
             -- lia.
           }
        }
        { (*Nodup ids A *)
           destruct k eqn: hk. 
           { destruct (cmd (nth 0 I tau0)) eqn:cmdt. all:simpl;auto. }
           { unfold structured in H. destruct H as [Hid Hul].
             specialize (Hid (S n)). replace (S (S n)) with (S n +1) in H2.
             apply Hid in H2. destruct H2 as [H2 | H2]. 
             (*Three cases of structred*)
             (*case 1: delete*) 
             -- apply Absorb_del_nodup_id. all:auto. 
             (*case 2: structured*) 
             -- destruct H2 as [H2 | H2]. 
             --- destruct kdela as [idBsub kdela]. 
                 destruct kdela as [idAsub kdela].
                 apply Absorb_notIn_nodup_id. all: auto.
             (*Case 3: structed*)
             --- destruct H2 as [H2a H2b]. assert(S n >0) as Hn. lia.
                 apply Absorb_notIn_nodup_id. all: auto.
                 subst tau. rewrite H2a. apply kdela. auto. auto.
                 subst tau. rewrite H2a. apply kdela. auto. auto. 
             -- lia.
           }
        }
        { (*Nodup times B *) simpl. unfold admissible. unfold Absorb.
          destruct k eqn: hk.
            { destruct (cmd (nth 0 I tau0)). 
                  all:simpl;auto.
            } 
            { unfold structured in H. destruct H as [Hid Hul].
              specialize (Hid (S n)). 
              replace (S (S n)) with (S n +1) in H2.
              apply Hid in H2. 2:{lia. } destruct H2 as [H2 | H2].
              { (*Case 1 structured.*)
               apply Absorb_notIn_nodup_time. 
               + auto.
               + auto.
               + intro h1. assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2.
                          apply kndat. auto. 
                 assert(~List.In (otime (ord tau)) 
                 (timesof (tilln (orders I) (S n -1)))) as hin3.
                 subst tau. assert((nth k (orders I) (ord tau0)) = 
                 ord (nth k I tau0)) as h4. apply map_nth.
                 subst k. rewrite <- h4. apply timesof_nodup_notIn.
                 auto. apply Hstruct. apply Hstruct.
                 rewrite <- ordersI_length. lia. lia. 
                 destruct (hin3 h2).
               + intro h1. assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2.
                          apply kinclidb. auto.
                 assert(~List.In (otime (ord tau)) 
                 (timesof (tilln (orders I) (S n -1)))) as hin3.
                 subst tau. assert((nth k (orders I) (ord tau0)) = 
                 ord (nth k I tau0)) as h4. apply map_nth.
                 subst k. rewrite <- h4. apply timesof_nodup_notIn.
                 auto. apply Hstruct. apply Hstruct. 
                 rewrite <- ordersI_length. lia. lia.
                 destruct (hin3 h2).
               }
               destruct H2 as [H2 | H2].
               { (*Case 2: structured*) 
                  assert(S n >0) as Hn. lia. 
                  apply Absorb_notIn_nodup_time. 
                        + auto.
                        + auto.
                        + intro h1. 
                          assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2. 
                          apply kndat. auto. 
                          assert(~List.In (otime (ord tau)) 
                          (timesof (tilln (orders I) (S n -1)))) as hin3.
                          subst tau. assert((nth k (orders I) (ord tau0)) = 
                          ord (nth k I tau0)) as h4. apply map_nth.
                          subst k. rewrite <- h4. apply timesof_nodup_notIn.
                          auto. apply Hstruct. apply Hstruct. 
                          rewrite <- ordersI_length. lia. lia.
                          destruct (hin3 h2).
                       + intro h1. 
                          assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2.
                          apply kinclidb. auto.
                          assert(~List.In (otime (ord tau)) 
                          (timesof (tilln (orders I) (S n -1)))) as hin3.
                          subst tau. assert((nth k (orders I) (ord tau0)) = 
                          ord (nth k I tau0)) as h4. apply map_nth.
                          subst k. rewrite <- h4. apply timesof_nodup_notIn.
                          auto. apply Hstruct. apply Hstruct. 
                          rewrite <- ordersI_length. lia. lia.
                          destruct (hin3 h2).
               }
               { (*Case 3: structured *)
                 destruct H2 as [H2a H2b]. assert(S n >0) as Hn. lia.
                 apply Absorb_notIn_nodup_time.  all: auto.
                 + intro h1. 
                          assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2.
                          apply kndat. auto.
                          assert(~List.In (otime (ord tau)) 
                          (timesof (tilln (orders I) (S n -1)))) as hin3.
                          subst tau. assert((nth k (orders I) (ord tau0)) = 
                          ord (nth k I tau0)) as h4. apply map_nth.
                          subst k. rewrite <- h4. apply timesof_nodup_notIn.
                          auto. apply Hstruct. apply Hstruct. 
                          rewrite <- ordersI_length. lia. lia. 
                          destruct (hin3 h2).
                 + intro h1. 
                          assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2.
                          apply kinclidb. auto.
                          assert(~List.In (otime (ord tau)) 
                          (timesof (tilln (orders I) (S n -1)))) as hin3.
                          subst tau. assert((nth k (orders I) (ord tau0)) = 
                          ord (nth k I tau0)) as h4. apply map_nth.
                          subst k. rewrite <- h4. apply timesof_nodup_notIn.
                          auto. apply Hstruct. apply Hstruct. 
                          rewrite <- ordersI_length. lia. lia. 
                          destruct (hin3 h2).
               }
             }
        }
        { (*Nodup times B *) simpl. unfold admissible. unfold Absorb.
          destruct k eqn: hk.
            { destruct (cmd (nth 0 I tau0)). 
                  all:simpl;auto.
            } 
            { unfold structured in H. destruct H as [Hid Hul].
              specialize (Hid (S n)). 
              replace (S (S n)) with (S n +1) in H2.
              apply Hid in H2. 2:{lia. } destruct H2 as [H2 | H2].
              { (*Case 1 structured.*)
               apply Absorb_notIn_nodup_time. 
               + auto.
               + auto.
               + intro h1. assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2.
                          apply kndat. auto. 
                 assert(~List.In (otime (ord tau)) 
                 (timesof (tilln (orders I) (S n -1)))) as hin3.
                 subst tau. assert((nth k (orders I) (ord tau0)) = 
                 ord (nth k I tau0)) as h4. apply map_nth.
                 subst k. rewrite <- h4. apply timesof_nodup_notIn.
                 auto. apply Hstruct. apply Hstruct.
                 rewrite <- ordersI_length. lia. lia. 
                 destruct (hin3 h2).
               + intro h1. assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2.
                          apply kinclidb. auto.
                 assert(~List.In (otime (ord tau)) 
                 (timesof (tilln (orders I) (S n -1)))) as hin3.
                 subst tau. assert((nth k (orders I) (ord tau0)) = 
                 ord (nth k I tau0)) as h4. apply map_nth.
                 subst k. rewrite <- h4. apply timesof_nodup_notIn.
                 auto. apply Hstruct. apply Hstruct. 
                 rewrite <- ordersI_length. lia. lia.
                 destruct (hin3 h2).
               }
               destruct H2 as [H2 | H2].
               { (*Case 2: structured*) 
                  assert(S n >0) as Hn. lia. 
                  apply Absorb_notIn_nodup_time. 
                        + auto.
                        + auto.
                        + intro h1. 
                          assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2. 
                          apply kndat. auto. 
                          assert(~List.In (otime (ord tau)) 
                          (timesof (tilln (orders I) (S n -1)))) as hin3.
                          subst tau. assert((nth k (orders I) (ord tau0)) = 
                          ord (nth k I tau0)) as h4. apply map_nth.
                          subst k. rewrite <- h4. apply timesof_nodup_notIn.
                          auto. apply Hstruct. apply Hstruct. 
                          rewrite <- ordersI_length. lia. lia.
                          destruct (hin3 h2).
                       + intro h1. 
                          assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2.
                          apply kinclidb. auto.
                          assert(~List.In (otime (ord tau)) 
                          (timesof (tilln (orders I) (S n -1)))) as hin3.
                          subst tau. assert((nth k (orders I) (ord tau0)) = 
                          ord (nth k I tau0)) as h4. apply map_nth.
                          subst k. rewrite <- h4. apply timesof_nodup_notIn.
                          auto. apply Hstruct. apply Hstruct. 
                          rewrite <- ordersI_length. lia. lia.
                          destruct (hin3 h2).
               }
               { (*Case 3: structured *)
                 destruct H2 as [H2a H2b]. assert(S n >0) as Hn. lia.
                 apply Absorb_notIn_nodup_time.  all: auto.
                 + intro h1. 
                          assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2.
                          apply kndat. auto.
                          assert(~List.In (otime (ord tau)) 
                          (timesof (tilln (orders I) (S n -1)))) as hin3.
                          subst tau. assert((nth k (orders I) (ord tau0)) = 
                          ord (nth k I tau0)) as h4. apply map_nth.
                          subst k. rewrite <- h4. apply timesof_nodup_notIn.
                          auto. apply Hstruct. apply Hstruct. 
                          rewrite <- ordersI_length. lia. lia. 
                          destruct (hin3 h2).
                 + intro h1. 
                          assert(List.In (otime (ord tau)) (timesof 
                          (tilln (orders I) (S n - 1)))) as h2.
                          apply kinclidb. auto.
                          assert(~List.In (otime (ord tau)) 
                          (timesof (tilln (orders I) (S n -1)))) as hin3.
                          subst tau. assert((nth k (orders I) (ord tau0)) = 
                          ord (nth k I tau0)) as h4. apply map_nth.
                          subst k. rewrite <- h4. apply timesof_nodup_notIn.
                          auto. apply Hstruct. apply Hstruct. 
                          rewrite <- ordersI_length. lia. lia. 
                          destruct (hin3 h2).
               }
             }
        }
     }
      repeat split. 
              {  simpl. apply efficient_correct. all:auto. }
              { simpl. apply efficient_correct. all:auto. }
              { simpl. apply efficient_correct. all:auto. }
              { simpl. apply efficient_correct. all:auto. }
              { simpl. apply efficient_correct. all:auto. } 
              { simpl. apply efficient_correct_OK. all:auto. } 
              { simpl. apply efficient_correct_OK. all:auto. } 
              { simpl. apply efficient_correct_OK. all:auto. } 
              { simpl. apply efficient_correct_OK. all:auto. }
              { replace (timesof (tilln (orders I) k)) with (timesof (tilln (orders I) (S k - 1))).
                replace (timesof (Blist (iterate Process_instruction I (S k)))) with
                (timesof (Blist (iterated Process_instruction I (S k)))).
                apply UniqueMatch.global_unique_aux with (k:= S k)
                (P1:=Process_instruction)(P2:=Process_instruction)(I:=I).
                apply Process_correct. apply Process_correct. auto.
                unfold iterated. destruct ((| I |) <? S k) eqn:HIk. move /ltP in HIk. lia.
                auto. replace (S k - 1) with k. auto. lia. }
              { replace (timesof (tilln (orders I) k)) with (timesof (tilln (orders I) (S k - 1))).
                replace (timesof (Alist (iterate Process_instruction I (S k)))) with
                (timesof (Alist (iterated Process_instruction I (S k)))).
                apply UniqueMatch.global_unique_aux with (k:= S k)
                (P1:=Process_instruction)(P2:=Process_instruction)(I:=I).
                apply Process_correct. apply Process_correct. auto.
                unfold iterated. destruct ((| I |) <? S k) eqn:HIk. move /ltP in HIk. lia.
                auto. replace (S k - 1) with k. auto. lia. }
              { replace (iterate Process_instruction I (S k)) with
                (iterated Process_instruction I (S k)).
                apply UniqueMatch.global_unique_aux with (k:= S k)
                (P1:=Process_instruction)(P2:=Process_instruction)(I:=I).
                apply Process_correct. apply Process_correct. auto.
                unfold iterated. destruct ((| I |) <? S k) eqn:HIk. move /ltP in HIk. lia.
                auto. }
              { replace (iterate Process_instruction I (S k)) with
                (iterated Process_instruction I (S k)).
                apply UniqueMatch.global_unique_aux with (k:= S k)
                (P1:=Process_instruction)(P2:=Process_instruction)(I:=I).
                apply Process_correct. apply Process_correct. auto.
                unfold iterated; destruct ((| I |) <? S k) eqn:HIk. move /ltP in HIk. lia.
                auto. }
              { replace (iterate Process_instruction I (S k)) with
                (iterated Process_instruction I (S k)).
                apply UniqueMatch.global_unique_aux with (k:= S k)
                (P1:=Process_instruction)(P2:=Process_instruction)(I:=I).
                apply Process_correct. apply Process_correct. auto.
                unfold iterated; destruct ((| I |) <? S k) eqn:HIk. move /ltP in HIk. lia.
                auto. }
              { replace (iterate Process_instruction I (S k)) with
                (iterated Process_instruction I (S k)).
                apply UniqueMatch.global_unique_aux with (k:= S k)
                (P1:=Process_instruction)(P2:=Process_instruction)(I:=I).
                apply Process_correct. apply Process_correct. auto.
                unfold iterated; destruct ((| I |) <? S k) eqn:HIk. move /ltP in HIk. lia.
                auto. }
              { replace (iterate Process_instruction I (S k)) with
                (iterated Process_instruction I (S k)).
                apply UniqueMatch.global_unique_aux with (k:= S k)
                (P1:=Process_instruction)(P2:=Process_instruction)(I:=I).
                apply Process_correct. apply Process_correct. auto.
                unfold iterated; destruct ((| I |) <? S k) eqn:HIk. move /ltP in HIk. lia.
                auto. }
              { replace (ids (tilln (orders I) k)) with (ids (tilln (orders I) (S k - 1))).
                 replace (iterate Process_instruction I (S k)) with
                (iterated Process_instruction I (S k)).
                apply UniqueMatch.global_unique_aux with (k:= S k)
                (P1:=Process_instruction)(P2:=Process_instruction)(I:=I).
                apply Process_correct. apply Process_correct. auto.
                unfold iterated; destruct ((| I |) <? S k) eqn:HIk. move /ltP in HIk. lia.
                auto. replace (S k - 1) with k. auto. lia. }
              { replace (ids (tilln (orders I) k)) with (ids (tilln (orders I) (S k - 1))).
                 replace (iterate Process_instruction I (S k)) with
                (iterated Process_instruction I (S k)).
                apply UniqueMatch.global_unique_aux with (k:= S k)
                (P1:=Process_instruction)(P2:=Process_instruction)(I:=I).
                apply Process_correct. apply Process_correct. auto.
                unfold iterated; destruct ((| I |) <? S k) eqn:HIk. move /ltP in HIk. lia.
                auto. replace (S k - 1) with k. auto. lia. }
              { replace (iterate Process_instruction I (S k)) with
                (iterated Process_instruction I (S k)). subst tau.
                replace (nth k I tau0) with (nth (S k -1) I tau0).
                apply UniqueMatch.global_unique_aux with (k:= S k)
                (P1:=Process_instruction)(P2:=Process_instruction)(I:=I).
                apply Process_correct. apply Process_correct. auto.
                 replace (S k - 1) with k. auto. lia.
                unfold iterated; destruct ((| I |) <? S k) eqn:HIk. move /ltP in HIk. lia.
                auto. }
              { replace (iterate Process_instruction I (S k)) with
                (iterated Process_instruction I (S k)). subst tau.
                replace (nth k I tau0) with (nth (S k -1) I tau0).
                apply UniqueMatch.global_unique_aux with (k:= S k)
                (P1:=Process_instruction)(P2:=Process_instruction)(I:=I).
                apply Process_correct. apply Process_correct. auto.
                 replace (S k - 1) with k. auto. lia.
                unfold iterated; destruct ((| I |) <? S k) eqn:HIk. move /ltP in HIk. lia.
                auto. } } } } }
Qed.

Definition cda_list (I : list instruction)(k:nat) := 
Mlist (iterated Process_instruction I k).

Definition cda_tree (I : list instruction)(k:nat) := 
Mt (eiterated eProcess_instruction I k).

Theorem identical_outputs (I : list instruction)(k:nat):
structured I  -> cda_list I k = cda_tree I k.
Proof. apply iterated_correct_aux. Qed. 


Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Coq.extraction.ExtrOcamlZBigInt.
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Constant Nat.sub =>  "fun n m -> if m>n then 0 else n-m".
Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant Nat.eqb => "( = )".
Extract Constant Nat.leb => "(<=)".
Extract Constant Nat.ltb => "(<)".
Extract Inductive prod => "(*)" [ "(,)" ]. 
Extract Constant Compare_dec.lt_eq_lt_dec =>
 "fun n m -> if n>m then None else Some (n<m)".

Extraction Language OCaml.
Require ExtrOcamlBasic.

Extraction "../application/Extracted_tree.ml" eProcess_instruction.

(* Examples of Bids and Asks trees

Definition A := TA.add {|id := 1;otime:=2;oquantity:=1;oprice:=2;oquantity_cond:=not1|} ( TA.add {|id := 1;otime:=1;oquantity:=1;oprice:=1;oquantity_cond:=not1|} ( TA.add {|id := 1;otime:=1;oquantity:=1;oprice:=2;oquantity_cond:=not1|} TA.empty)).

Definition bids:=(
{|id :=4;otime:=1;oquantity:=1;oprice:=5;oquantity_cond:=not1|}::
{|id := 2;otime:=1;oquantity:=1;oprice:=1;oquantity_cond:=not1|}::
{|id := 1;otime:=2;oquantity:=1;oprice:=2;oquantity_cond:=not1|}::
{|id :=3;otime:=1;oquantity:=1;oprice:=2;oquantity_cond:=not1|}::
nil).
Definition B := TB.add 
{|id := 1;otime:=2;oquantity:=1;oprice:=2;oquantity_cond:=not1|} 
( TB.add 
{|id := 3;otime:=1;oquantity:=1;oprice:=1;oquantity_cond:=not1|} 
( TB.add 
{|id := 2;otime:=1;oquantity:=1;oprice:=2;oquantity_cond:=not1|}
(TB.add 
{|id :=4;otime:=1;oquantity:=1;oprice:=5;oquantity_cond:=not1|}
 TB.empty))).

Definition B2 := TB.treeify (bids).

Eval compute in (TB.min_elt B).
Eval compute in (TB.elements B).
Eval compute in (TB.max_elt B2).
Eval compute in (TA.max_elt A).
Eval compute in (TA.elements A).
Print B2. 

Definition B4 := T_id.add 
{|id := 1;otime:=2;oquantity:=1;oprice:=2;oquantity_cond:=not1|} 
( T_id.add 
{|id := 3;otime:=1;oquantity:=1;oprice:=1;oquantity_cond:=not1|} 
(T_id.add 
{|id :=4;otime:=1;oquantity:=1;oprice:=5;oquantity_cond:=not1|}
( T_id.add 
{|id := 2;otime:=1;oquantity:=1;oprice:=2;oquantity_cond:=not1|}
 T_id.empty))).

Definition B3 := T_id.treeify (bids).

Eval compute in (T_id.min_elt B4).
Eval compute in (T_id.max_elt B4).
Eval compute in (T_id.elements B4).
Eval compute in (T_id.max_elt B4).
*)

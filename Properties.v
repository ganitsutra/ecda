(*########################################################*)
(*#-------3 Main Properties and other related terms------#*)
(*########################################################*) 




Require Export Definitions.

Set Implicit Arguments.


Section Properties.


Section competitiveness.

Definition bcompetitive (b b':order):= (Nat.ltb (oprice b') (oprice b)) ||
((Nat.eqb (oprice b') (oprice b)) && (Nat.leb (otime b) (otime b') )).


Definition acompetitive (a a':order):= (Nat.ltb (oprice a) (oprice a')) ||
((Nat.eqb (oprice a) (oprice a')) && (Nat.leb (otime a) (otime a') )).

Definition eqcompetitive (a a':order):= ((Nat.eqb (oprice a) (oprice a')) && (Nat.eqb (otime a) (otime a') )).


Lemma bcompetitive_contadiction (b b':order):
bcompetitive b b'-> bcompetitive b' b -> ~eqcompetitive b b' -> False.
Proof. unfold bcompetitive.  unfold eqcompetitive. intros. 
       move /orP in H. move /orP in H0. destruct H0; destruct H.
       {  move /ltP in H. move /ltP in H0. lia. }
       {  destruct H1. move /andP in H. destruct H.
          apply /andP. move /eqP in H.  split. apply /eqP. 
          auto. move /ltP in H0. move /leP in H1. lia. }
       {  destruct H1. move /andP in H0. destruct H0.
          apply /andP. move /eqP in H0.  split. apply /eqP. 
          auto. move /ltP in H. move /leP in H1. lia. }
       {  destruct H1. move /andP in H0. destruct H0.
          move /andP in H. destruct H. apply /andP. split.
          auto. move /leP in H1. move /leP in H2. apply /eqP. lia. } Qed.

Lemma acompetitive_contadiction (a a':order):
acompetitive a a'-> acompetitive a' a -> ~eqcompetitive a a' -> False.
Proof. unfold acompetitive.  unfold eqcompetitive. intros. 
       move /orP in H. move /orP in H0. destruct H0; destruct H.
       {  move /ltP in H. move /ltP in H0. lia. }
       {  destruct H1. move /andP in H. destruct H.
          apply /andP. move /eqP in H.  split. apply /eqP. 
          auto. move /ltP in H0. move /leP in H1. lia. }
       {  destruct H1. move /andP in H0. destruct H0.
          apply /andP. move /eqP in H0.  split. apply /eqP. 
          auto. move /ltP in H. move /leP in H1. lia. }
       {  destruct H1. move /andP in H0. destruct H0.
          move /andP in H. destruct H. apply /andP. split.
          auto. move /leP in H1. move /leP in H2. apply /eqP. lia. } Qed.

Lemma bcompetitive_P : transitive bcompetitive /\ comparable2 bcompetitive.
Proof.  { split.
          { unfold transitive. unfold bcompetitive.  
            intros y x z H H1. move /orP in H1. move /orP in H.
            apply /orP. destruct H1;destruct H. 
            { left. move /leP in H0. move /leP in H. apply /leP. lia. }
            { move /andP in H. destruct H. left.  
              move /leP in H0. move /eqP in H. apply /leP. lia. }
            { move /andP in H0. destruct H0. left.
              move /leP in H. move /eqP in H0. apply /leP. lia. }
            { move /andP in H0. move /andP in H. destruct H0. destruct H.
              right.
              move /eqP in H. move /eqP in H0. apply /andP.
              split. apply /eqP. lia. apply /leP. move /leP in H1. 
              move /leP in H2. lia. } }
            { unfold comparable2.
              unfold bcompetitive. intros. destruct x. destruct y.  simpl. 
              assert((oprice0 = oprice)\/(oprice0 < oprice)\/(oprice < oprice0)).
              lia. destruct H.
              subst. assert(Nat.ltb oprice oprice = false).
              apply /ltP. lia. rewrite H. simpl.
              assert(Nat.eqb oprice oprice =true). auto. rewrite H0. simpl. 
              assert((otime0 <= otime)\/(otime < otime0)). lia. destruct H1.
              right. apply /leP. auto. left. apply /leP. lia.
              destruct H. left. apply /orP. left. apply /ltP. auto. right.
              apply /orP. left. apply /ltP. auto.
               } } Qed.

Lemma acompetitive_P : transitive acompetitive /\ comparable2 acompetitive.
Proof.  { split.
          { unfold transitive. unfold acompetitive.  
            intros y x z H H1. move /orP in H1. move /orP in H.
            apply /orP. destruct H1;destruct H. 
            { left. move /leP in H0. move /leP in H. apply /leP. lia. }
            { move /andP in H. destruct H. left.  
              move /leP in H0. move /eqP in H. apply /leP. lia. }
            { move /andP in H0. destruct H0. left.
              move /leP in H. move /eqP in H0. apply /leP. lia. }
            { move /andP in H0. move /andP in H. destruct H0. destruct H.
              right.
              move /eqP in H. move /eqP in H0. apply /andP.
              split. apply /eqP. lia. apply /leP. move /leP in H1. 
              move /leP in H2. lia. } }
            { unfold comparable2.
              unfold acompetitive. intros. destruct x. destruct y.  simpl. 
              assert((oprice0 = oprice)\/(oprice < oprice0)\/(oprice0 < oprice)).
              lia. destruct H.
              subst. assert(Nat.ltb oprice oprice = false).
              apply /ltP. lia. rewrite H. simpl.
              assert(Nat.eqb oprice oprice =true). auto. rewrite H0. simpl. 
              assert((otime0 <= otime)\/(otime < otime0)). lia. destruct H1.
              right. apply /leP. auto. left. apply /leP. lia.
              destruct H. left. apply /orP. left. apply /ltP. auto. right.
              apply /orP. left. apply /ltP. auto.
               } } Qed.

Lemma not_acompetitive (a1 a2:order): ~acompetitive a1 a2 -> acompetitive a2 a1.
Proof. unfold acompetitive. intros H. unfold not in H. apply /orP.
       destruct(Nat.ltb (oprice a1) (oprice a2)) eqn:H1. 
       { simpl in H. destruct H. auto. }
       { simpl in H.  destruct(Nat.eqb (oprice a1) (oprice a2)) eqn: H2.
          { simpl in H. destruct (Nat.leb (otime a1) (otime a2)) eqn: H3.
           destruct H. auto. right. apply /andP. split. move /eqP in H2.
           rewrite H2. apply /eqP. auto. move /leP in H3. apply /leP. lia. }
          { simpl in H. destruct (Nat.leb (otime a1) (otime a2)) eqn: H3.
            move /ltP in H1. move /eqP in H2. left. apply /ltP. lia. 
            move /ltP in H1. move /eqP in H2. move /leP in H3. 
            left. apply /ltP. lia.
           }
         }
         Qed.  

Lemma not_bcompetitive (b1 b2:order): ~bcompetitive b1 b2 -> bcompetitive b2 b1.
Proof. unfold bcompetitive. intros H. unfold not in H. apply /orP.
       destruct(Nat.ltb (oprice b2) (oprice b1)) eqn:H1. 
       { simpl in H. destruct H. auto. }
       { simpl in H.  destruct(Nat.eqb (oprice b2) (oprice b1)) eqn: H2.
          { simpl in H. destruct (Nat.leb (otime b1) (otime b2)) eqn: H3.
           destruct H. auto. right. apply /andP. split. move /eqP in H2.
           rewrite H2. apply /eqP. auto. move /leP in H3. apply /leP. lia. }
          { destruct (Nat.leb (otime b1) (otime b2)) eqn: H3.
            move /ltP in H1. move /eqP in H2. left. apply /ltP. lia. 
            move /ltP in H1. move /eqP in H2. move /leP in H3. 
            left. apply /ltP. lia.
           }
         }
         Qed.  



End competitiveness.

Notation "s === t" := (perm s t) (at level 80, no associativity).

Inductive command:Set:= 
|buy
|sell
|del.

Record instruction :Type:= Mk_instruction { cmd : command; ord : order}.
Definition action0:=del.
Definition tau0:={| cmd := action0; ord := w0 |}.

Definition Absorb (B A: list order)(tau: instruction):=
match (cmd tau) with
|buy => ((ord tau)::B, A)
|sell =>(B, (ord tau)::A)
|del =>(delete_order B (id (ord tau)), delete_order A (id (ord tau)))
end. 

Lemma Absorb_perm (B1 B2 A1 A2 : list order)(tau: instruction):
perm B1 B2 -> perm A1 A2 ->
perm (fst (Absorb B1 A1 tau)) (fst (Absorb B2 A2 tau))/\
perm (snd (Absorb B1 A1 tau)) (snd (Absorb B2 A2 tau)).
Proof. case (cmd tau) eqn:H. unfold Absorb. replace (cmd tau) with buy. simpl. eauto.
unfold Absorb. replace (cmd tau) with sell. simpl. eauto.
unfold Absorb. replace (cmd tau) with del. simpl. intros. split.
apply delete_order_perm. auto. apply delete_order_perm. auto. Qed.

Lemma Absorb_notIn_nodup_id (B A: list order)(tau: instruction):
NoDup (ids B) ->NoDup (ids A) -> ~In (id (ord tau)) (ids B) -> ~In (id (ord tau)) (ids A) ->
NoDup (ids (fst (Absorb B A tau)))/\NoDup (ids (snd (Absorb B A tau))).
Proof. intros. case (cmd tau) eqn:Ht. 
split. unfold Absorb. replace (cmd tau) with buy. simpl. eauto.
unfold Absorb. replace (cmd tau) with buy. simpl. eauto.
unfold Absorb. replace (cmd tau) with sell. simpl. eauto.
unfold Absorb. replace (cmd tau) with del. simpl. split.
apply delete_order_ids_nodup. auto. apply delete_order_ids_nodup. auto.
Qed.

Lemma Absorb_del_nodup_id (B A: list order)(tau: instruction):
NoDup (ids B) ->NoDup (ids A) -> (cmd tau ) = del ->
NoDup (ids (fst (Absorb B A tau)))/\NoDup (ids (snd (Absorb B A tau))).
Proof. intros. unfold Absorb. rewrite H1. simpl. split. apply delete_order_ids_nodup. auto. apply delete_order_ids_nodup. auto. Qed.

Lemma Absorb_notIn_nodup_time (B A: list order)(tau: instruction):
NoDup (timesof B) ->NoDup (timesof A) -> ~In (otime (ord tau)) (timesof B) -> 
~In (otime (ord tau)) (timesof A) ->
NoDup (timesof (fst (Absorb B A tau)))/\NoDup (timesof (snd (Absorb B A tau))). 
Proof. intros. case (cmd tau) eqn:Ht. 
unfold Absorb. replace (cmd tau) with buy. simpl. eauto. 
unfold Absorb. replace (cmd tau) with sell. simpl. eauto. 
unfold Absorb. replace (cmd tau) with del. simpl.
split. apply delete_order_timesof_nodup. auto. apply delete_order_timesof_nodup. auto.
Qed.



Definition Condition1 (M: list transaction)(B A hat_B hat_A: list order)
(tau: instruction):Prop:=
not (matchable hat_B hat_A). 

Definition Condition2a (M: list transaction)(B:list order):Prop:=
forall b b', (In b B)/\(In b' B)/\(bcompetitive b b'/\~eqcompetitive b b')/\(In (id b') (ids_bid_aux M)) -> 
(Qty_bid M (id b)) = (oquantity b).


Definition Condition2b (M: list transaction)(A:list order):Prop:=
forall a a', (In a A)/\(In a' A)/\(acompetitive a a'/\~eqcompetitive a a')/\(In (id a') (ids_ask_aux M)) -> 
(Qty_ask M (id a)) = (oquantity a).


Definition Condition3a (M: list transaction)(B A: list order)
(tau: instruction):Prop:=
let B' := (fst (Absorb B A tau)) in
let A' := (snd (Absorb B A tau)) in
Matching M B' A'.

Definition Condition3b (M: list transaction)(B A hat_B: list order)
(tau: instruction):Prop:=
let B' := (fst (Absorb B A tau)) in
hat_B === (odiff B' (bids M B')).

Definition Condition3c (M: list transaction)(B A hat_A: list order) 
(tau: instruction):Prop:=
let A' := (snd (Absorb B A tau)) in
(hat_A === (odiff A' (asks M A'))).

Definition admissible (B A :list order) := 
(NoDup (ids B))/\(NoDup (ids A))/\
(NoDup (timesof B))/\(NoDup (timesof A)).


Definition Legal_input (B A :list order)(tau: instruction):=
admissible (fst (Absorb B A tau)) (snd (Absorb B A tau))/\
not (matchable B A).


Lemma legal_perm (B1 B2 A1 A2 : list order)(tau: instruction):
perm B1 B2/\ perm A1 A2/\Legal_input B1 A1 tau -> Legal_input B2 A2 tau.
Proof. unfold Legal_input. intros H. destruct H. destruct H0. 
destruct H1 as [Hb Ha]. unfold admissible in Hb. 
destruct Hb as [Hb Hc]. destruct Hc as [Hc Hd].  destruct Hd as [Hd He].
assert(G1:=H). assert(G2:=H0).
unfold perm in G1. move /andP in G1. destruct G1 as [G1a G1b].
unfold perm in G2. move /andP in G2. destruct G2 as [G2a G2b].  
apply Absorb_perm with (B1:=B1)(B2:=B2)(tau:=tau) in H0.
destruct H0. repeat split.   
apply ids_perm in H0. eauto. 
apply ids_perm in H1. eauto. 
apply timesof_perm in H0. eauto. 
apply timesof_perm in H1. eauto.  
intro. destruct Ha.
unfold matchable in H2. destruct H2. destruct H2.
unfold matchable. exists x. exists x0. destruct H2.
destruct H3. 
split. eauto. split. eauto. auto. auto. Qed. 

Definition Properties (Process: (list order) ->(list order) ->instruction
-> (list order)*(list order)*(list transaction)):=
forall A B tau,
Legal_input B A tau -> 
let B' := (fst (Absorb B A tau)) in
let A' := (snd (Absorb B A tau)) in
let hat_B := (Blist (Process B A tau)) in
let hat_A := (Alist (Process B A tau)) in
let M := (Mlist (Process B A tau)) in

Condition1 M B A hat_B hat_A tau /\
Condition2a M B'/\
Condition2b M A'/\
Condition3a M B A tau /\
Condition3b M B A hat_B tau /\
Condition3c M B A hat_A tau.

(*----------------Term require for Gloal theorem part----------------*)

Fixpoint orders (I:list instruction) :(list order):=
match I with
|nil => nil
|i::I' => (ord i)::orders I'
end.


Fixpoint tilln (l: list order)(k:nat):=
match (l,k) with 
|(nil, 0) => nil 
|(x::l', 0) => x::nil 
|(nil, S k) => nil
|(hd::tail, S k) => hd::(tilln tail k)
end.


Lemma tilln_contains_nth (l: list order)(k:nat):
l<>nil/\|l|>=k+1 -> In (nth k l w0) (tilln l k).
Proof. revert k. induction l. intros. destruct H. destruct H. auto.
       destruct k.  simpl. auto. simpl. 
       intros. destruct H. assert(l<>nil). intro.
       subst l. simpl in H0. lia. right. apply IHl. split.
       auto. lia. Qed.


Lemma tilln_Subset_whole (l: list order)(k:nat):
Subset (tilln l k) l.
Proof. revert k. induction l. destruct k eqn: Hk. simpl. auto.
simpl. auto. destruct k eqn: Hk. simpl. auto. simpl. 
apply Subset_intro. auto. Qed.


Lemma tilln_Subset_next (I: list order)(k:nat):
Subset (tilln I (k-1)) (tilln I k).
Proof. revert I. induction k. simpl. auto. intros. 
replace (S k -1) with k. destruct k. destruct I. simpl. auto.
simpl. auto. destruct I. simpl. auto. simpl. 
replace (S k -1) with k in IHk. specialize (IHk I).
eauto. lia. lia. Qed.


Lemma timesof_nodup_notIn (B: list order)(k: nat): 
NoDup (timesof B) -> Sorted Nat.ltb (timesof B) -> 
S k <= (| B |) -> k>0 ->
~In (otime (nth k B w0)) (timesof (tilln B (k - 1))).
Proof. revert B. induction k. intros. lia. 
 destruct B. simpl. intros. lia. replace (S k -1) with k.
destruct k. simpl. intros. destruct B. simpl in H1. lia.
simpl. intro. destruct H3.
apply Sorted_elim4 with (x:= (otime o0)) in H0. move /ltP in H0.  lia.
simpl.  auto.  auto. simpl. intros. assert(In (nth (S k) B w0) B).
assert(In (nth (S k) B w0) (tilln B (S k))).
apply tilln_contains_nth. split. intro.
subst B. simpl in H1. lia. lia. assert(Subset (tilln B (S k)) B).
apply tilln_Subset_whole. auto. intro.
destruct H4. apply timesof_elim in H3. 
apply Sorted_elim4 with (x:= (otime (nth (S k) B w0))) in H0. 
move /ltP in H0.  lia.  auto. assert(S (S k) <= (| B |)). lia.
apply IHk in H5. replace (S k -1) with k in H5.
destruct (H5 H4). lia. eauto. eauto. lia. lia. Qed.


Lemma ordersI_length (I:list instruction) :
|I| = |orders I|.
Proof. induction I. simpl;auto. simpl;lia. Qed.

Lemma ordersI_nil (I:list instruction) :
I <> nil -> (orders I) <> nil.
Proof. intros. induction I. destruct H. auto. simpl. 
       intro. inversion H0. Qed.


Definition structured (I :list instruction):= 
(forall t:nat,  (t+1) <= (length I) -> (cmd (nth t I tau0) = del)\/
(~In (id (ord (nth t I tau0))) (ids (tilln (orders I) (t-1))))\/
((id (ord (nth t I tau0))) = (id (ord (nth (t-1) I tau0)))/\ 
(cmd (nth (t-1) I tau0) = del)))
/\ Sorted (Nat.ltb) (timesof (orders I))/\ NoDup ((timesof (orders I))).

Fixpoint iterate (P: (list order)->(list order) -> instruction -> (list order)*(list order)*(list transaction))
(I : list instruction)(k:nat) :=
match k with
|0 => (nil, nil, nil) 
| S k' =>  let it:=(iterate P I k') in P (Blist it) (Alist it) 
    (nth k' I tau0)
end.


Definition iterated (P: (list order)->(list order) -> instruction -> (list order)*(list order)*(list transaction))
(I : list instruction)(k:nat) := 
if (Nat.ltb (length I) k) then (nil,nil,nil) else iterate P I k.

End Properties.
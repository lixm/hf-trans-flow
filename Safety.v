
(* Mechanized proof of the preservation of consensus by the transaction flow *) 
(* The invariant established is formalized as the proposition cl *)

Require Import Logic.FunctionalExtensionality.
Require Import Lia.

Require Import LibTactics.
Require Import SfLib.
Require Import MyUtils. 
Require Import Entities. 
Require Import TransFlow. 

Lemma eq_mp :
  forall (mp1 mp2 : mp_tp key val),
    (forall k, mp1 k = mp2 k) -> mp1 = mp2.
Proof. intros; apply functional_extensionality; assumption. Qed.

Definition k_step_peer_add_blk (hf : hash_func) (pid : peer_id) 
  := k_R config (step_rel_act hf (Act_peer_add_blk pid)). 

Definition ep_of_epcc (epcc : chaincode_id -> option (prod endorsement_pol chaincode)) :=
  fun (ccid : chaincode_id) =>
    match epcc ccid with
      Some (ep, cc) => Some ep
    | None => None
    end.

Definition same_ep_ledger (peers peers' : mp_tp peer_id peer_node) pid :=
  forall pn pn', 
    peers pid = Some pn ->
    peers' pid = Some pn' ->
    (ep_of_epcc pn.(peer_ep_cc) = ep_of_epcc pn'.(peer_ep_cc) /\
     pn.(peer_ledger) = pn'.(peer_ledger)).

Lemma same_ep_ledger_transitive :
  forall peers peers' peers'' pid, 
    (peers pid <> None <-> peers'' pid <> None) ->
    same_ep_ledger peers peers'' pid ->
    same_ep_ledger peers'' peers' pid ->
    same_ep_ledger peers peers' pid.
Proof.
  introv.
  intros H_peers_peers''_none. 
  intros H_same_lgr1 H_same_lgr2. 
  unfold same_ep_ledger in *.
  intros.
  rewrite H in H_peers_peers''_none.
  assert (peers'' pid <> None). 
  {
    intro H_contra. rewrite H_contra in H_peers_peers''_none.
    inversion H_peers_peers''_none.
    assert (Some pn <> None) by (intro contra; inversion contra).
    apply H1 in H3. apply H3. auto. 
  }
  assert (exists pn'', peers'' pid = Some pn'').
  {
    destruct (peers'' pid). exists p. auto.
    apply ex_falso_quodlibet. apply H1. auto. 
  }
  inversion H2 as [pn'' H_pn''].
  specialize (H_same_lgr1 pn pn'' H H_pn'').
  specialize (H_same_lgr2 pn'' pn' H_pn'' H0).
  inversion H_same_lgr1; inversion H_same_lgr2; split; congruence.   
Qed.

Lemma add_pmsg_preserves_ledger :
  forall peers peers' pmsg pn_idxs pid, 
    peers' = add_pmsg_for_peers pmsg peers pn_idxs -> 
    (
      (peers pid <> None <-> peers' pid <> None) /\
      (same_ep_ledger peers peers' pid)
    ).
Proof.
  introv.
  intro H_peers'_peers.
  gen peers. 
  induction pn_idxs.
  (* base case *)
  intros. 
  unfold add_pmsg_for_peers in H_peers'_peers.
  simpl in  H_peers'_peers.
  subst.
  split.
  intuition.
  unfold same_ep_ledger. intros.
  rewrite H in H0. inversion H0; subst.
  auto. 
  (* inductive caes *)
  intros. 
  unfold add_pmsg_for_peers in H_peers'_peers.
  simpl in H_peers'_peers.
  remember
    (func_upd peer_id (option peer_node) beq_peer_id_dec peers a
              match peers a with
              | Some pr => Some (peer_add_trans_propose_msg pr pmsg)
              | None => None
              end) as peers1.
  specialize (IHpn_idxs peers1).
  unfold add_pmsg_for_peers in IHpn_idxs. 
  specialize (IHpn_idxs H_peers'_peers).
  inversion IHpn_idxs as [H_peers1_peers'_none H_peers1_peers'_lgr]; 
    clear IHpn_idxs.
  clear H_peers'_peers.
  assert (H_first: 
            (peers pid <> None <-> peers1 pid <> None) /\
            (same_ep_ledger peers peers1 pid)). 
  {
    destruct (beq_peer_id_dec a pid).
    (* a = pid *)
    rewrite e in Heqpeers1. 
    rewrite Heqpeers1.
    rewrite func_upd_eq.
    assert (H_peers_pid : (exists p, peers pid = Some p) \/ peers pid = None).
    {
      destruct (peers pid).
      left. exists p. auto.
      right; auto. 
    }
    inversion H_peers_pid as [H_some | H_none].
    (* exists p, peers pid = Some p *)
    inversion H_some as [p0 H_p0].
    rewrite H_p0. 
    split.
    split; (intro; intro H_neq; inversion H_neq).

    (* same_ledger *)
    unfold same_ep_ledger.
    intros.
    rewrite H_p0 in H.
    inverts H. 
    rewrite func_upd_eq in H0. 
    inverts H0.
    unfold peer_add_trans_propose_msg.
    simpl. 
    auto.
    (* peers pid = None *)
    rewrite H_none.
    split. intuition.
    unfold same_ep_ledger.
    introv. rewrite H_none. 
    intro H_contra. inversion H_contra. 

    (* a <> pid *)
    rewrite Heqpeers1.
    rewrite func_upd_neq; auto. 
    split. intuition.
    unfold same_ep_ledger. intros.
    rewrite func_upd_neq in H0; auto. 
    split; congruence; auto.
  }
  inversion H_first as [H_peers_peers1_none H_peers_peers1_lgr]; 
    clear H_first.
  split.
  intuition.
  eapply same_ep_ledger_transitive; eauto. 
  
Qed.

Definition same_ep_ledger_in_peers (peers peers' : mp_tp peer_id peer_node) := 
  forall pid, 
    (
      (peers pid <> None <-> peers' pid <> None) /\
      (same_ep_ledger peers peers' pid) 
    ).

Definition same_ep_ledger_ext (peers1 peers2 : mp_tp peer_id peer_node) pid1 pid2 :=
  forall pn1 pn2, 
    peers1 pid1 = Some pn1 ->
    peers2 pid2 = Some pn2 ->
    (ep_of_epcc pn1.(peer_ep_cc) = ep_of_epcc pn2.(peer_ep_cc) /\ 
     pn1.(peer_ledger) = pn2.(peer_ledger)). 

Definition same_ep_ledger_in_peers_ext
           (peers1 peers2 : mp_tp peer_id peer_node) pid1 pid2 :=
    (
      (peers1 pid1 <> None <-> peers2 pid2 <> None) /\
      (same_ep_ledger_ext peers1 peers2 pid1 pid2) 
    ). 

Definition ord_blks_ext (os os' : ordering_service) :=  
  forall sn,
    os.(os_blks_created) sn <> None ->
    os.(os_blks_created) sn = os'.(os_blks_created) sn.

Lemma cli_prop_step_preservation :
  forall hf clients peers os clients' peers' os' cli_id pn_idxs, 
    step hf clients peers os clients' peers' os' (Act_cli_prop cli_id pn_idxs) -> 
    ((same_ep_ledger_in_peers peers peers') /\ os = os'). 
Proof.
  introv. intro H_step.
  inversion H_step.
  rename H5 into H_peers_peers'.
  split.
  unfold same_ep_ledger_in_peers. intros.
  cut ((peers pid <> None <-> peers' pid <> None) /\
       (same_ep_ledger peers peers' pid)). 
  intro.
  inversion H5 as [H_same_peer_emptiness H_same_lgr].
  auto. 
  eapply add_pmsg_preserves_ledger; eauto.
  auto.
Qed.

Lemma peer_resp_step_preservation :
  forall hf clients peers os clients' peers' os' peer_id cli_id, 
  step hf clients peers os clients' peers' os' (Act_peer_resp peer_id cli_id) ->
  (same_ep_ledger_in_peers peers peers' /\ os = os').
Proof.
  intros.
  rename H into H_step.
  inversion H_step.
  rename H1 into H_peers_peer_id. 
  rename H2 into H_pn_ledger.
  rename H3 into H_pmsg.
  rename H4 into H_tx.
  rename H5 into H_tid.
  rename H6 into H_ed_code. 
  rename H7 into H_op_in_lst.
  rename H8 into H_ccode_ws. 
  rename H9 into H_rwsets.
  rename H10 into H_prop.
  rename H11 into H_ep_sig.
  rename H12 into H_emsg.
  rename H13 into H_clients. 
  rename H14 into H_clients'.
  rename H15 into H_peers'. 
  rename H16 into H_os'_os.
  clear H. clear H0. 

  split; auto. (* os' = os *)

  unfold same_ep_ledger_in_peers.
  introv.

  destruct (beq_peer_id_dec pid peer_id).
  (* pid = peer_id *)
  split.
  (* same peer emptiness *)
  rewrite e in *. 
  rewrite H_peers'. rewrite mp_upd_eq.
  rewrite H_peers_peer_id.
  split; (intro; intro contra; inversion contra).
  
  (* same_ep_ledger *)
  unfold same_ep_ledger.
  rewrite e in *. 
  introv.
  intros H_peers_pid H_peers'_pid. 
  rewrite H_peers' in H_peers'_pid.
  rewrite mp_upd_eq in H_peers'_pid.
  inversion H_peers'_pid.
  unfold upd_peer_pmsgs in H0. 
  assert (pn = pn0) by congruence.
  subst.
  simpl. auto. 
  
  (* pid <> peer_id *)
  split.
  (* same peer emptiness *)
  rewrite H_peers'.
  rewrite mp_upd_neq; auto.
  intuition.

  (* same_ep_ledger *)
  unfold same_ep_ledger.
  introv.
  intros H_peers_pid H_peers'_pid. 
  rewrite H_peers' in H_peers'_pid.
  rewrite mp_upd_neq in H_peers'_pid; auto.
  rewrite H_peers_pid in H_peers'_pid.
  inversion H_peers'_pid; subst.
  auto.
  
Qed.

Lemma peer_drop_prop_preservation : 
  forall hf clients peers os clients' peers' os' peer_id, 
    step hf clients peers os clients' peers' os' (Act_peer_drop_prop peer_id) -> 
    (same_ep_ledger_in_peers peers peers' /\ os = os'). 
Proof.
  introv.
  intro H_step.
  inversion H_step.
  rename H0 into H_peers_peer_id.
  rename H1 into H_pmsgs.
  rename H2 into H_peers'.
  rename H3 into H_clients'.
  rename H4 into H_os'.
  clear H. 

  split; auto. (* os = os' *)

  unfold same_ep_ledger_in_peers.
  introv.

  destruct (beq_peer_id_dec pid peer_id).
  
  (* pid = peer_id *)
  rewrite e in *.
  split.
  (* same peer emptiness *)
  rewrite H_peers'.
  rewrite mp_upd_eq. rewrite H_peers_peer_id.
  split; (intro; intro contra; inversion contra).
  
  (* same ledger *)
  unfold same_ep_ledger.
  introv.
  intros H_peers_peer_id' H_peers'_peer_id. 
  rewrite H_peers_peer_id in H_peers_peer_id'.
  inversion H_peers_peer_id'; subst. 
  rewrite mp_upd_eq in H_peers'_peer_id.
  inversion H_peers'_peer_id.
  unfold ep_of_epcc. simpl.
  unfold upd_peer_pmsgs in H0.
  rewrite <- H0 in *; simpl in *.
  split; auto. 
  
  (* pid <> peer_id *)
  split.
  rewrite H_peers'. rewrite mp_upd_neq; auto.
  intuition.

  (* same ledger *)
  unfold same_ep_ledger.
  introv.
  intros H_peers_pid H_peers'_pid. 
  rewrite H_peers' in H_peers'_pid.
  rewrite mp_upd_neq in H_peers'_pid; auto. 
  rewrite H_peers_pid in H_peers'_pid.
  inversion H_peers'_pid; subst. 
  intuition.
Qed.

Lemma same_peers_impl_same_ep_lgr :
  forall peers peers' pid, 
    peers = peers' -> same_ep_ledger peers peers' pid. 
Proof.
  unfold same_ep_ledger.
  intros. 
  subst. rewrite H0 in H1.
  inversion H1; subst.
  split; auto.
Qed. 
  
Lemma same_peers_impl_same_ep_lgr_in_peers : 
  forall peers peers', 
    peers = peers' -> same_ep_ledger_in_peers peers peers'. 
Proof.
  introv.
  intro H_peer_eq_peers'.
  unfold same_ep_ledger_in_peers.
  introv.
  rewrite H_peer_eq_peers'. 
  intuition. 
  apply same_peers_impl_same_ep_lgr; auto.  
Qed.

Lemma cli_send_trans_preservation : 
  forall hf clients peers os clients' peers' os' cli_id, 
    step hf clients peers os clients' peers' os' (Act_cli_send_trans cli_id) -> 
    ((same_ep_ledger_in_peers peers peers') /\ (ord_blks_ext os os')). 
Proof.
  introv.
  intro H_step.
  inversion H_step.
  rename H12 into H_peers'. 
  rename H13 into H_os'.
  
  clear H.
  split.
  apply same_peers_impl_same_ep_lgr_in_peers; auto.
  unfold ord_blks_ext.
  introv.
  intro H_os_blks_chid_sn_nn.
  rewrite H_os'.
  unfold upd_os_pending_trans.
  simpl. auto. 
Qed.

Lemma os_blks_ext_refl :
  forall os, ord_blks_ext os os. 
Proof. intros. unfold ord_blks_ext. intros. auto. Qed. 
  
Lemma os_eq_ext :
  forall os1 os2, os1 = os2 -> ord_blks_ext os1 os2. 
Proof. introv; intro H_os_eq; inversion H_os_eq; apply os_blks_ext_refl; auto. Qed. 

Lemma cli_drop_prop_preservation : 
  forall hf clients peers os clients' peers' os' cli_id, 
    step hf clients peers os clients' peers' os' (Act_cli_drop_prop cli_id) -> 
    ((same_ep_ledger_in_peers peers peers') /\ (ord_blks_ext os os')). 
Proof.
  introv.
  intro H_step.
  inversion H_step.
  split; 
    [apply same_peers_impl_same_ep_lgr_in_peers; auto |
     apply os_eq_ext; auto].
Qed. 

Lemma os_crt_preservation : 
  forall hf clients peers os clients' peers' os', 
    step hf clients peers os clients' peers' os' (Act_ord_crt_blk) -> 
    ((same_ep_ledger_in_peers peers peers') /\ (ord_blks_ext os os')).
Proof. 
  introv.
  intro H_step.
  inversion H_step.
  rename H8 into H_os''.
  rename H9 into H_os'.
  split.
  apply same_peers_impl_same_ep_lgr_in_peers; auto.
  unfold ord_blks_ext.
  introv.
  intro H_os_blks_crt_nn.
  rewrite H_os'' in H_os'.
  unfold upd_os_pending_trans in H_os'.
  unfold inc_os_blk_num in H_os'; simpl in H_os'.
  unfold upd_os_last_blk_hash in H_os'; simpl in H_os'.
  unfold os_record_new_blk in H_os'; simpl in H_os'.
  rewrite H_os'; simpl.
  rewrite H5. unfold blk_no. simpl.
  rewrite H4.  
  assert (H_sn_ne: sn <> S last_blk_no).
  { intro H_eq. subst. apply H_os_blks_crt_nn. auto. }
  rewrite mp_upd_neq; auto.
Qed.

Lemma peer_add_blk_preservation :
  forall hf clients peers os clients' peers' os' pid1 pid2, 
    step hf clients peers os clients' peers' os' (Act_peer_add_blk pid1) ->
    pid2 <> pid1 ->
    (same_ep_ledger_in_peers_ext peers peers' pid2 pid2 /\ os = os').
Proof.
  introv.
  intros H_step H_pids_neq.
  inversion H_step; subst.
  split; auto.
  unfold same_ep_ledger_in_peers_ext.
  rewrite mp_upd_neq; auto. 
  split. 
  split; intro; auto.
  unfold same_ep_ledger_ext.
  introv. intros H_peers_pid2 H_mp_upd.
  rewrite mp_upd_neq in H_mp_upd; auto. 
  rewrite H_mp_upd in H_peers_pid2.
  inversion H_peers_pid2; auto.
Qed.

Lemma peer_add_blks_preserves_os :
  forall hf k clients peers os clients' peers' os' pid,
    k_step_peer_add_blk hf pid k 
                        (clients, (peers, os)) (clients', (peers', os')) ->
    os = os'.
Proof.
  induction k.
  intros.
  inverts H. auto.
  intros.
  inverts H.
  inverts H1.
  inversion H as
      [peers0 [os0 [clients'' [peers'' [os'' H_body]]]]]; clear H.
  inversion H_body as [H_eq1 [H_eq2 H_step]]; clear H_body.
  inversion H_eq1; subst.
  inverts H_step.
  fold (k_step_peer_add_blk hf pid k) in H2.
  apply IHk in H2.
  auto.
Qed.   
      
Lemma some_implies_nn :
  forall (A : Type) (x : option A) e, x = Some e -> x <> None.
Proof.
  intros.
  destruct x.
  intro. inversion H0. inversion H.
Qed.

Lemma nn_implies_some :
  forall (A : Type) (x : option A), x <> None -> (exists e, x = Some e).
Proof.
  intros.
  destruct x.
  exists a; auto.
  apply ex_falso_quodlibet; apply H; auto.
Qed.

Lemma nn_ex_1 :
  forall (A : Type) (x1 x2 : option A) a1,
    (x1 <> None <-> x2 <> None) ->
    x1 = Some a1 ->
    (exists a2, x2 = Some a2).
Proof.
  intros.
  apply nn_implies_some.
  apply H.
  eapply some_implies_nn; eauto.
Qed.

Lemma nn_ex_2 :
  forall (A : Type) (x1 x2 : option A) a2,
    (x1 <> None <-> x2 <> None) ->
    x2 = Some a2 ->
    (exists a1, x1 = Some a1).
Proof.
  intros; eapply nn_ex_1; eauto; intuition. 
Qed. 

Lemma same_ep_lgr_implies :
  forall peers peers' pid pn', 
    same_ep_ledger_in_peers peers peers' -> 
    peers' pid = Some pn' -> 
    (exists pn,
        (peers pid = Some pn /\
         pn.(peer_ledger) = pn'.(peer_ledger) /\
         ep_of_epcc pn.(peer_ep_cc) = ep_of_epcc pn'.(peer_ep_cc))). 
Proof.
  introv. 
  intro H_same_lgr_in_peers.
  intro H_peers'_pid.
  unfold same_ep_ledger_in_peers in *.
  specialize (H_same_lgr_in_peers pid).
  inversion H_same_lgr_in_peers as [H_same_peer_emptiness H_same_lgr].
  clear H_same_lgr_in_peers.
  
  assert (H_ex_pn : exists pn, peers pid = Some pn)
    by (eapply nn_ex_2; eauto). 
  inversion H_ex_pn as [pn H_peers_pid]; clear H_ex_pn.
  exists pn.
  split; auto.
  unfold same_ep_ledger in *.
  specialize (H_same_lgr pn pn' H_peers_pid H_peers'_pid).
  intuition. 
Qed.

Lemma same_ep_lgr_implies_ext :
  forall peers1 peers2 pid1 pid2 pn1, 
    same_ep_ledger_in_peers_ext peers1 peers2 pid1 pid2 -> 
    peers1 pid1 = Some pn1 -> 
    (exists pn2,
        (peers2 pid2 = Some pn2 /\
         pn2.(peer_ledger) = pn1.(peer_ledger) /\
         ep_of_epcc pn2.(peer_ep_cc) = ep_of_epcc pn1.(peer_ep_cc))). 
Proof.
  introv.
  intros H_same_eplgr_ext H_peers1_pid1.
  unfold same_ep_ledger_in_peers_ext in H_same_eplgr_ext.
  inversion H_same_eplgr_ext as [H_same_peer_emptiness H_same_lgr_ext].
  clear H_same_eplgr_ext.

  assert (H_ex_pn: exists pn, peers2 pid2 = Some pn).
  { eapply nn_ex_1; eauto. }
  inversion H_ex_pn as [pn2 H_peers2_pid2]; clear H_ex_pn.
  exists pn2.
  split; auto.
  unfold same_ep_ledger_ext in H_same_lgr_ext.
  specialize (H_same_lgr_ext pn1 pn2 H_peers1_pid1 H_peers2_pid2).
  intuition. 
Qed. 

Lemma same_ep_ledger_sym :
  forall peers1 peers2 pid, 
    same_ep_ledger peers1 peers2 pid -> same_ep_ledger peers2 peers1 pid. 
Proof.
  intros.
  unfold same_ep_ledger in *.
  intros.
  specialize (H pn' pn H1 H0). 
  intuition. 
Qed.
                      
Lemma same_ledger_in_peers_sym :
  forall peers1 peers2, 
    same_ep_ledger_in_peers peers1 peers2 -> same_ep_ledger_in_peers peers2 peers1. 
Proof.
  introv.
  intro H_same_ledger_12.
  unfold same_ep_ledger_in_peers in *.
  introv.
  specialize (H_same_ledger_12 pid).
  inversion H_same_ledger_12 as [H_peers12 H_same_ledger]. 
  split.
  intuition.
  apply same_ep_ledger_sym; auto.
Qed.

Lemma peer_add_blk_simulate :
  forall clients1 peers1 os1 clients1' peers1' os1' clients2 peers2 os2
         hf peer_id, 
    same_ep_ledger_in_peers peers1 peers2 ->
    ord_blks_ext os1 os2 ->
    step_rel_act hf (Act_peer_add_blk peer_id)
                 (clients1, (peers1, os1)) (clients1', (peers1', os1')) ->
    (exists clients2' peers2' os2',
        (
          step_rel_act hf (Act_peer_add_blk peer_id) 
                       (clients2, (peers2, os2)) (clients2', (peers2', os2')) /\
          same_ep_ledger_in_peers peers1' peers2' /\ ord_blks_ext os1' os2'
        )
    ).
Proof.
  introv.
  intros H_same_lgr H_ord_blks H_step_rel_act.
  inversion H_step_rel_act.
  inversion H as
      [peers0 [os0 [clients0' [peers0' [os0' H_step_0]]]]]; clear H.
  inversion H_step_0 as [H_eq1 [H_eq2 H_step_core]]; clear H_step_0. 
  inversion H_eq1; clear H_eq1. 
  rewrite <- H0 in *; rewrite <- H1 in *; rewrite <- H2 in *.
  clear H0; clear H1; clear H2. 
  inversion H_eq2; clear H_eq2. 
  rewrite <- H0 in *; rewrite <- H1 in *; rewrite <- H2 in *.
  clear H0; clear H1; clear H2.
  inversion H_step_core.
  clear H. 
  rename pn into pn1. 
  rename H0 into H_peers1_peer_id.
  rename H1 into H_os_blks_1. 
  rename H2 into H_new_blk_1.
  rename H3 into H_lgr_1.
  rename H4 into H_last_blk_1.
  rename H5 into H_txs_validate_1. 
  rename H6 into H_new_blk'_1.
  rename H7 into H_clients1'.
  rename H8 into H_peers1'.
  rename H9 into  H_os1'.

  assert (H_ex_pn_right: 
            (exists pn2,
                (peers2 peer_id = Some pn2 /\
                 (pn2.(peer_ledger) = pn1.(peer_ledger) /\
                  ep_of_epcc pn2.(peer_ep_cc) = ep_of_epcc pn1.(peer_ep_cc))))). 
  {
    assert (same_ep_ledger_in_peers peers2 peers1).
    { intro. apply same_ledger_in_peers_sym; auto. }
    eapply same_ep_lgr_implies; eauto. 
  }
  inversion H_ex_pn_right as [pn2 [H_peers2_peer_id [H_same_peer_lgr H_same_ep]]];
    clear H_ex_pn_right.

  exists clients2.
  exists (mp_upd Entities.peer_id peer_node beq_peer_id_dec peers2 peer_id
                 (peer_update_ledger pn2 new_blk' wsc')). 
  exists os2.
  split.
  
  (* step_rel_act on the right *)

  unfold step_rel_act.
  repeat eexists.
  eapply Step_peer_add_block with
      (peer_id0 := peer_id) (pn := pn2) 
      (blks := blks) (wsc := wsc) (wsc' := wsc') (new_blk := new_blk); eauto. 
  unfold ord_blks_ext in H_ord_blks.
  rewrite <- H_os_blks_1. symmetry.
  apply H_ord_blks.
  eapply some_implies_nn; eauto. 
  congruence.

  unfold ep_of_epcc in H_same_ep.
  congruence. 

  split.
  rewrite H_peers1'. 
  unfold same_ep_ledger_in_peers.
  introv.
  destruct (beq_peer_id_dec pid peer_id).
  (* pid = peer_id *)
  subst. unfold same_ep_ledger. 
  repeat rewrite mp_upd_eq.
  split. split; (intro; intro H_contra; inversion H_contra).
  intros. inversion H; subst. inversion H0; subst.
  unfold peer_update_ledger.
  simpl.
  split.
  congruence. 
  rewrite H_same_peer_lgr. auto.
  (* pid <> peer_id *)
  unfold peer_update_ledger; simpl.
  split. 
  repeat (rewrite mp_upd_neq; auto).
  apply H_same_lgr; auto.
  unfold same_ep_ledger; simpl.
  repeat (rewrite mp_upd_neq; auto). 
  intros. 
  unfold same_ep_ledger_in_peers in H_same_lgr.
  assert (H_same_ep_ledger:  same_ep_ledger peers1 peers2 pid)
    by (apply H_same_lgr; auto).
  unfold same_ep_ledger in H_same_ep_ledger.
  eapply H_same_ep_ledger; eauto.

  (* ord_blks_ext os1' os2 chid *)
  rewrite H_os1'. assumption.

Qed.

Lemma peer_add_blk_simulate_ext :
  forall clients1 peers1 os1 clients1' peers1' os1' clients2 peers2 os2
         hf pid1 pid2, 
    same_ep_ledger_in_peers_ext peers1 peers2 pid1 pid2 ->
    ord_blks_ext os1 os2 ->
    step_rel_act hf (Act_peer_add_blk pid1)
                 (clients1, (peers1, os1)) (clients1', (peers1', os1')) ->
    (exists clients2' peers2' os2',
        (
          step_rel_act hf (Act_peer_add_blk pid2) 
                       (clients2, (peers2, os2)) (clients2', (peers2', os2')) /\
          same_ep_ledger_in_peers_ext peers1' peers2' pid1 pid2 /\ ord_blks_ext os1' os2'
        )
    ).
Proof.
  introv.
  intros H_same_eplgr_in_peers_ext H_ord_blks_ext H_step_rel_1.
  inversion H_step_rel_1.
  inversion H as
      [peers0 [os0 [clients0' [peers0' [os0' H_step_0]]]]]; clear H.
  inversion H_step_0 as [H_eq1 [H_eq2 H_step_core]]; clear H_step_0. 
  inversion H_eq1; clear H_eq1. 
  rewrite <- H0 in *; rewrite <- H1 in *; rewrite <- H2 in *.
  clear H0; clear H1; clear H2. 
  inversion H_eq2; clear H_eq2. 
  rewrite <- H0 in *; rewrite <- H1 in *; rewrite <- H2 in *.
  clear H0; clear H1; clear H2.
  inversion H_step_core.
  clear H. 
  rename pn into pn1. 
  rename H0 into H_peers1_peer_id.
  rename H1 into H_os_blks_1. 
  rename H2 into H_new_blk_1.
  rename H3 into H_lgr_1.
  rename H4 into H_last_blk_1.
  rename H5 into H_txs_validate_1. 
  rename H6 into H_new_blk'_1.
  rename H7 into H_clients1'.
  rename H8 into H_peers1'.
  rename H9 into  H_os1'.

  assert (H_ex_pn_right: 
            (exists pn2,
                (peers2 pid2 = Some pn2 /\
                 (pn2.(peer_ledger) = pn1.(peer_ledger) /\
                  ep_of_epcc pn2.(peer_ep_cc) = ep_of_epcc pn1.(peer_ep_cc))))).
  { eapply same_ep_lgr_implies_ext; eauto. }
  
  inversion H_ex_pn_right as [pn2 [H_peers2_peer_id [H_same_peer_lgr H_same_ep]]];
    clear H_ex_pn_right.

  exists clients2.
  exists (mp_upd Entities.peer_id peer_node beq_peer_id_dec peers2 pid2
                 (peer_update_ledger pn2 new_blk' wsc')). 
  exists os2.
  split.
  
  (* step_rel_act on the right *)
  unfold step_rel_act.
  repeat eexists.
  eapply Step_peer_add_block with
      (peer_id0 := pid2) (pn := pn2) 
      (blks := blks) (wsc := wsc) (wsc' := wsc') (new_blk := new_blk); eauto. 
  unfold ord_blks_ext in H_ord_blks_ext.
  rewrite <- H_os_blks_1. symmetry.
  apply H_ord_blks_ext.
  eapply some_implies_nn; eauto. 
  congruence.
  unfold ep_of_epcc in H_same_ep.
  congruence. 

  (* same_ep_ledger_in_peers_ext *)
  split.
  rewrite H_peers1'. 
  unfold same_ep_ledger_in_peers_ext.
  repeat rewrite mp_upd_eq.
  split.
  (* same ledger emptiness *) 
  split; intro; intro; discriminate.
  (* same_ep_ledger_ext *)
  unfold same_ep_ledger_ext.
  introv.
  repeat rewrite mp_upd_eq.
  intros. inversion H; subst. inversion H0; subst. clear H. clear H0. 
  unfold peer_update_ledger.
  simpl.
  split.
  congruence. 
  rewrite H_same_peer_lgr. auto.

  (* ord_blks_ext *)
  rewrite H_os1'. auto.
Qed. 

Lemma peer_add_blk_simulate_k_steps :
  forall clients1 peers1 os1 clients1' peers1' os1' clients2 peers2 os2
         hf peer_id k, 
    same_ep_ledger_in_peers peers1 peers2 ->
    ord_blks_ext os1 os2 -> 
    k_step_peer_add_blk hf peer_id k 
                        (clients1, (peers1, os1)) (clients1', (peers1', os1')) -> 
    (exists clients2' peers2' os2',
        (
          k_step_peer_add_blk hf peer_id k 
                              (clients2, (peers2, os2)) (clients2', (peers2', os2')) /\
          same_ep_ledger_in_peers peers1' peers2' /\
          ord_blks_ext os1' os2'
        )
    ).
Proof.
  intros. 
  gen clients1 peers1 os1 clients2 peers2 os2. 
  induction k. 
  (* base case *)
  intros.
  exists clients2. exists peers2. exists os2.
  split.
  econstructor; eauto. 
  inversion H1; subst.
  split; auto.
  (* inductive case *)
  introv.
  intro H_S_k_step_left.
  introv.
  intro H_same_ep_ledger_in_peers.
  introv. 
  intro H_os_blks_ext. 
  inversion H_S_k_step_left.
  clear H2. clear H3. clear x. clear x'. 
  destruct x''.
  destruct p.
  rename m into clients1''. rename m0 into peers1''. rename o into os1''.
  eapply peer_add_blk_simulate with (clients2 := clients2) in H0; eauto.
  inversion H0 as [clients2'' [peers2'' [os2'' H_body]]]; clear H0.
  inversion H_body as
      [H_step_rel_right [H_same_ep_lgr_in_peers'' H_ord_blks_ext'']]; 
    clear H_body.
  eapply IHk with (clients2 := clients2'') in H_same_ep_lgr_in_peers''; eauto.
  rename H_same_ep_lgr_in_peers'' into H_ex_sim_k_step_right.
  inversion H_ex_sim_k_step_right as 
      [clients2' [peers2' [os2' H_body]]]; clear H_ex_sim_k_step_right.
  inversion H_body as [H_sim_k_steps_right [H_same_ep_lgr' H_ord_blks_ext']];
    clear H_body. 
  exists clients2'. exists peers2'. exists os2'.
  split.
  econstructor; eauto.
  split; auto. 
Qed.

Lemma peer_add_blk_simulate_k_steps_ext :
  forall clients1 peers1 os1 clients1' peers1' os1' clients2 peers2 os2
         hf pid1 pid2 k, 
    same_ep_ledger_in_peers_ext peers1 peers2 pid1 pid2 ->
    ord_blks_ext os1 os2 -> 
    k_step_peer_add_blk hf pid1 k 
                        (clients1, (peers1, os1)) (clients1', (peers1', os1')) -> 
    (exists clients2' peers2' os2',
        (
          k_step_peer_add_blk hf pid2 k 
                              (clients2, (peers2, os2)) (clients2', (peers2', os2')) /\
          same_ep_ledger_in_peers_ext peers1' peers2' pid1 pid2 /\
          ord_blks_ext os1' os2'
        )
    ).
Proof.
  intros. 
  gen clients1 peers1 os1 clients2 peers2 os2. 
  induction k. 
  (* base case *)
  intros.
  exists clients2. exists peers2. exists os2.
  split.
  econstructor; eauto. 
  inversion H1; subst.
  split; auto.
  (* inductive case *)
  introv.
  intro H_S_k_step_left.
  introv.
  intro H_same_ep_ledger_in_peers_ext.
  introv. 
  intro H_os_blks_ext. 
  inversion H_S_k_step_left.
  clear H2. clear H3. clear x. clear x'. 
  destruct x''.
  destruct p.
  rename m into clients1''. rename m0 into peers1''. rename o into os1''.
  eapply peer_add_blk_simulate_ext with (clients2 := clients2) in H0; eauto.
  inversion H0 as [clients2'' [peers2'' [os2'' H_body]]]; clear H0.
  inversion H_body as
      [H_step_rel_right [H_same_ep_lgr_in_peers''_ext H_ord_blks_ext'']]; 
    clear H_body.
  eapply IHk with (clients2 := clients2'') in H_same_ep_lgr_in_peers''_ext; eauto.
  rename H_same_ep_lgr_in_peers''_ext into H_ex_sim_k_step_right.
  inversion H_ex_sim_k_step_right as 
      [clients2' [peers2' [os2' H_body]]]; clear H_ex_sim_k_step_right.
  inversion H_body as [H_sim_k_steps_right [H_same_ep_lgr'_ext H_ord_blks_ext']];
    clear H_body. 
  exists clients2'. exists peers2'. exists os2'.
  split.
  econstructor; eauto.
  split; auto. 
Qed.

Lemma step_preserves_peer_ep_cc :
  forall hf clients peers os clients' peers' os' act pid pn pn', 
    step hf clients peers os clients' peers' os' act ->
    peers pid = Some pn ->
    peers' pid = Some pn' ->
    ep_of_epcc pn.(peer_ep_cc) = ep_of_epcc pn'.(peer_ep_cc).
Proof.
  intros.
  inversion H.

  (* cli_prop *)
  assert (H_same_eplgr: 
      (peers pid <> None <-> peers' pid <> None) /\
      (same_ep_ledger peers peers' pid)
    ).
  { eapply add_pmsg_preserves_ledger; eauto. }
  inversion H_same_eplgr as [H_same_nn H_same_ep_lgr];
    clear H_same_eplgr. 
  unfold same_ep_ledger in H_same_ep_lgr. 
  specialize (H_same_ep_lgr pn pn' H0 H1).
  inversion H_same_ep_lgr.
  auto.

  (* peer_resp *)
  rewrite H16 in H1.
  destruct (beq_peer_id_dec pid peer_id).
  (* pid = peer_id *)
  rewrite e in *.
  rewrite mp_upd_eq in H1.
  inversion H1; subst.
  simpl. congruence.
  (* pid <> peer_id *)
  rewrite mp_upd_neq in H1. 
  congruence. intuition.

  (* peer_drop_prop *)
  rewrite H4 in H1. 
  destruct (beq_peer_id_dec pid peer_id).
  (* pid = peer_id *)
  rewrite e in *.
  rewrite mp_upd_eq in H1.
  inversion H1; subst.
  simpl. congruence.
  (* pid <> peer_id *)
  rewrite mp_upd_neq in H1.
  congruence. intuition.

  (* cli_send_trans *)
  congruence.

  (* cli_drop_prop *)
  congruence.

  (* ord_crt_blk *)
  congruence.

  (* peer_add_blk *)
  rewrite H10 in H1.
  destruct (beq_peer_id_dec pid peer_id).
  (* pid = peer_id *)
  rewrite e in *.
  rewrite mp_upd_eq in H1.
  inversion H1; subst.
  unfold peer_update_ledger. simpl. 
  congruence.
  (* pid <> peer_id *)
  rewrite mp_upd_neq in H1.
  congruence. intuition.
  
Qed.

Lemma peer_add_blk_preserve_pn_emptiness :
  forall hf pid clients peers os clients' peers' os' pn, 
    step_rel_act hf
                 (Act_peer_add_blk pid)
                 (clients, (peers, os)) (clients', (peers', os')) ->
  peers pid = Some pn -> 
  (exists pn', peers' pid = Some pn').
Proof.
  intros.
  inversion H; subst.
  inversion H1 as [peers0 [os0 [clients'0 [peers'0 [os'0 H_body]]]]]; clear H1.
  inversion H_body as [H_eq1 [H_eq2 H_step]]; clear H_body.
  inversion H_eq1; subst. inversion H_eq2; subst.
  inversion H_step; subst.
  rewrite mp_upd_eq.
  eexists; eauto.
Qed. 

Lemma steps_preserve_peer_ep_cc :
  forall hf pid k clients peers os clients' peers' os' pn pn', 
    k_step_peer_add_blk hf pid k (clients, (peers, os)) (clients', (peers', os')) -> 
    peers pid = Some pn ->
    peers' pid = Some pn' -> 
    ep_of_epcc pn.(peer_ep_cc) = ep_of_epcc pn'.(peer_ep_cc).
Proof.
  induction k.
  intros.
  inverts H. congruence.
  intros.
  inverts H.
  remember H3 as H_step_rel.
  clear HeqH_step_rel. 
  inverts H3.
  fold (k_step_peer_add_blk hf pid k) in H4.

  inversion H as [peers0 [os0 [clients'' [peers'' [os'' H_body]]]]]; clear H. 
  inversion H_body as [H_eq1 [H_eq2 H_step]]; clear H_body.
  inversion H_eq1; subst.

  assert (H_ex_pn'': exists pn'', peers'' pid = Some pn'').
  { eapply peer_add_blk_preserve_pn_emptiness; eauto. }
  inversion H_ex_pn'' as [pn'' H_peers''_pid]; clear H_ex_pn''. 
  
  asserts_rewrite (ep_of_epcc pn.(peer_ep_cc) = ep_of_epcc pn''.(peer_ep_cc)).
  { eapply step_preserves_peer_ep_cc; eauto. }
  
  eapply IHk; eauto. 
Qed. 
  
Definition cl 
           (hf : hash_func) 
           (clients : mp_tp client_id client)
           (peers : mp_tp peer_id peer_node)
           (os : ordering_service) : Prop :=
  forall pid1 pid2 pn1 pn2,
    pid1 <> pid2 -> 
    peers pid1 = Some pn1 ->
    peers pid2 = Some pn2 ->
    (
      ep_of_epcc pn1.(peer_ep_cc) = ep_of_epcc pn2.(peer_ep_cc) /\
      (
        forall blks1 blks2 wsc1 wsc2, 
          (pn1.(peer_ledger) = (Ledger (BC blks1) wsc1) ->
           pn2.(peer_ledger) = (Ledger (BC blks2) wsc2) ->
           List.length blks1 <= List.length blks2 -> (
             blks1 = firstn (List.length blks1) blks2 /\
             (exists peers' clients' os' pn1',
                 k_step_peer_add_blk
                   hf pid1 ((List.length blks2) - (List.length blks1))
                   (clients, (peers, os)) (clients', (peers', os')) /\ 
                 peers' pid1 = Some pn1' /\
                 pn1'.(peer_ledger) = pn2.(peer_ledger))))
      )
    ). 

Lemma ledger_preserved_impl_invariant_preserved :
  forall hf clients peers os clients' peers' os', 
    cl hf clients peers os ->
    same_ep_ledger_in_peers peers peers' -> 
    ord_blks_ext os os' -> 
    cl hf clients' peers' os'.
Proof.
  introv.
  intros H_cl H_same_ep_ledger_in_peers H_ord_blks_ext.
  unfold cl. 
  introv.
  intros H_pid1_neq_pid2 H_peers'_pid1 H_peers'_pid2.

  rename pn1 into pn1'. rename pn2 into pn2'.
  assert (H_ex_pn: 
            (exists pn1,
                (peers pid1 = Some pn1 /\
                 pn1.(peer_ledger) = pn1'.(peer_ledger) /\
                 ep_of_epcc (pn1.(peer_ep_cc)) = ep_of_epcc (pn1'.(peer_ep_cc))))).  
  { eapply same_ep_lgr_implies; eauto. }
  inversion H_ex_pn as [pn1 [H_peers_pid1 [H_eq_lgr1 H_eq_ep1]]]; clear H_ex_pn. 

  assert (H_ex_pn: 
            (exists pn2,
                (peers pid2 = Some pn2 /\
                 pn2.(peer_ledger) = pn2'.(peer_ledger) /\
                 ep_of_epcc pn2.(peer_ep_cc) = ep_of_epcc pn2'.(peer_ep_cc)))). 
  { eapply same_ep_lgr_implies; eauto. } 
  inversion H_ex_pn as [pn2 [H_peers_pid2 [H_eq_lgr2 H_eq_ep2]]]; clear H_ex_pn.
  
  specialize (H_cl pid1 pid2 pn1 pn2 H_pid1_neq_pid2).
  specialize (H_cl H_peers_pid1 H_peers_pid2).
  inversion H_cl as [H_ep_cc_eq H_forall]; clear H_cl.
  split.
  congruence. 

  introv. 
  intros H_lgr1' H_lgr2' H_blk_len_lt'.
  rename blks1 into blks1'. rename blks2 into blks2'.

  rename H_forall into H_cl. 
  specialize (H_cl blks1' blks2').
  specialize (H_cl wsc1 wsc2). 
  rewrite <- H_eq_lgr1 in H_lgr1'.
  rewrite <- H_eq_lgr2 in H_lgr2'. 
  specialize (H_cl H_lgr1' H_lgr2'). 
  specialize (H_cl H_blk_len_lt').
  inversion H_cl as [H_blks_prefix H_catch_up].
  clear H_cl.
  
  split.
  (* bc prefix *) 
  auto.
  (* eventual agreement in bc and wsc *)
  inversion H_catch_up as [peers'' [clients'' [os'' [pn1'' H_body]]]]; 
    clear H_catch_up.
  inversion H_body as [H_k_step_from_orig [H_peers''_pid1 H_lgr'']]; 
    clear H_body. 
  
  eapply peer_add_blk_simulate_k_steps with
      (clients2 := clients') (peers2 := peers') (os2 := os') in H_k_step_from_orig;
    eauto. 
  rename H_k_step_from_orig into H_sim_res.
  inversion H_sim_res
    as [clients''' [peers''' [os''' [H_k_steps''' [H_same_eplgr''' H_ord_ext''']]]]].
  clear H_sim_res. 
  exists peers'''. exists clients'''. exists os'''.

  unfold same_ep_ledger_in_peers in H_same_eplgr'''.
  specialize (H_same_eplgr''' pid1). 
  inversion H_same_eplgr''' as [H_same_peer_emptiness''' H_same_ep_lgr'''];
    clear H_same_ep_lgr'''.
  assert (H_ex_pn''': exists pn1''', peers''' pid1 = Some pn1''').
  { eapply nn_ex_1; eauto. }
  inversion H_ex_pn''' as [pn1''' H_peers'''_pid1]; clear H_ex_pn'''.
  
  exists pn1'''. 
  split.
  auto.
  split.
  auto. 

  assert (H_same_eplgr_final : same_ep_ledger peers'' peers''' pid1).
  { inversion H_same_eplgr''' as [Ha Hb]; auto. }
  unfold same_ep_ledger in H_same_eplgr_final. 
  specialize (H_same_eplgr_final pn1'' pn1''').
  specialize (H_same_eplgr_final H_peers''_pid1 H_peers'''_pid1).
  inversion H_same_eplgr_final as [H_ep_eq_final H_lgr_eq_final];
    clear H_same_eplgr_final.
  congruence.
  
Qed.

Lemma blk_step_extends_bc :
  forall hf clients peers os clients' peers' os' pid pn pn' blks blks' wsc wsc', 
    step hf clients peers os clients' peers' os' (Act_peer_add_blk pid) ->
    peers pid = Some pn ->
    peers' pid = Some pn' ->
    pn.(peer_ledger) = Ledger (BC blks) wsc ->
    pn'.(peer_ledger) = Ledger (BC blks') wsc' ->
    exists new_blk, blks' = List.app blks (new_blk :: nil).
Proof.
  introv.
  intros H_step H_peers_pid H_peers'_pid H_ledger_pn H_ledger_pn'.
  inversion H_step.
  rename H8 into H_peers'.
  unfold peer_update_ledger in H_peers'. simpl in H_peers'.
  unfold upd_peer_ledger in H_peers'. simpl in H_peers'. 
  rewrite H_peers' in H_peers'_pid.
  simpl in H_peers'_pid.
  rewrite <- H in *.
  rewrite mp_upd_eq in H_peers'_pid.
  inversion H_peers'_pid; subst.
  simpl in H_ledger_pn'.
  rewrite H3 in H_ledger_pn'.
  inversion H_ledger_pn'; subst.
  assert (H_eq: pn = pn0) by congruence.
  assert (H_eq_blks: blks = blks0) by congruence.
  exists (Blk new_hdr new_trans_lst flags).
  congruence.
Qed.

Lemma blk_step_peer_intact :
  forall hf clients peers os clients' peers' os' pid1 pid2, 
    step hf clients peers os clients' peers' os' (Act_peer_add_blk pid1) ->
    pid1 <> pid2 -> 
    peers' pid2 = peers pid2. 
Proof.
  introv.
  intros H_step H_pid_neq.
  inversion H_step; subst.
  rewrite mp_upd_neq; auto.
Qed.

Lemma trans_validate_deterministic :
  forall tx ep ws ws1 ws2 flag1 flag2, 
    trans_validate tx ep ws ws1 flag1 ->
    trans_validate tx ep ws ws2 flag2 ->
    (ws1 = ws2 /\ flag1 = flag2).
Proof.   
  introv.
  intro H_tx_validate1.
  intro H_tx_validate2.
  inversion H_tx_validate1; subst.
  inversion H_tx_validate2; subst.

  (* validated on both sides *)
  
  inversion H; subst.
  clear H2. clear H6. clear H1. clear H5. clear H0. clear H4. 
  split. 2: { auto. }
  apply functional_extensionality.
  intro k.
  specialize (H3 k). specialize (H7 k).
  inversion H3.
  
  inversion H7.
  inversion H0; inversion H1; congruence.
  inversion H0.
  inversion H1.
  inversion H5 as [vl [vl' [vr [H_wset0_k H_ws_k]]]]; clear H5.
  rewrite H2 in H_wset0_k.
  inversion H_wset0_k.
  inversion H5 as [vl [vr [H_wset0_k H_rem]]]; clear H5.
  rewrite H2 in H_wset0_k.
  inversion H_wset0_k.
  
  inversion H7.
  inversion H0.
  inversion H2 as [vl [vl' [vr [H_wset0_k H_ws_k]]]]; clear H2.
  inversion H1. rewrite H2 in H_wset0_k. inversion H_wset0_k.
  inversion H2 as [vl [vr [H_wset0_k H_rem]]]; clear H2. 
  inversion H1. rewrite H2 in H_wset0_k.
  inversion H_wset0_k.

  inversion H0.
  inversion H1.
  inversion H2 as [vl [vl' [vr [H_wset0_k [H_ws_k H_ws1_k]]]]]; clear H2.
  inversion H4 as [vl'' [vl''' [vr' [H_wset0_k' [H_ws_k' H_ws2_k]]]]]; clear H4.
  rewrite H_ws_k' in H_ws_k. inversion H_ws_k; subst.
  congruence.
  inversion H2 as [vl [vl' [vr [H_wset0_k H_rem]]]]; clear H2.
  inversion H4 as [vl'' [vr' [H_wset0_k' H_rem']]]; clear H4.
  rewrite H_wset0_k in H_wset0_k'. inversion H_wset0_k'.
  inversion H1.
  inversion H2 as [vl [vr [H_wset0_k H_rem]]]; clear H2. 
  inversion H4 as [vl' [vl'' [vr' [H_wset0_k' [H_ws_k H_ws2_k]]]]]; clear H1.
  rewrite H_wset0_k in H_wset0_k'.
  inversion H_wset0_k'.
  inversion H2 as [vl [vr [H_wset0_k [H_ws_k H_ws1_k]]]]; clear H2.
  inversion H4 as [vl' [vr' [H_wset0_k' [H_ws_k' H_ws2_k]]]]; clear H4.
  congruence.

  (* validated on one side but not the other -- contradiction *)
  inversion H; subst. 
  inversion H4.
  congruence. 
  inversion H5. congruence. 
  inversion H6 as [k [vr [H_rset0_k H_all_vl]]]; clear H6.
  specialize (H2 k vr H_rset0_k).
  inversion H2 as [vl H_ws2_k]; clear H2.
  specialize (H_all_vl vl). congruence.

  inversion H_tx_validate2; subst.
  inversion H; subst.
  inversion H0.
  congruence.
  inversion H5.
  congruence.
  inversion H6 as [k [vr [H_rset0_k H_all]]]; clear H6.
  specialize (H3 k vr H_rset0_k).
  inversion H3 as [vl H_ws1_k]; clear H3.
  specialize (H_all vl).
  congruence.

  (* not validated on either side *)
  split; auto.
  
Qed.

Lemma trans_lst_validate_deterministic:
  forall trans_lst wsc wsc1 wsc2 flags1 flags2 pn, 
   trans_lst_validate trans_lst
          (fun ccid : chaincode_id =>
           match peer_ep_cc pn ccid with
           | Some (a, _) => Some a | None => None
           end) wsc wsc1 flags1 ->
   trans_lst_validate trans_lst
          (fun ccid : chaincode_id =>
           match peer_ep_cc pn ccid with
           | Some (a, _) => Some a | None => None 
           end) wsc wsc2 flags2 ->
   (wsc1 = wsc2 /\ flags1 = flags2).
Proof.
  induction trans_lst.
  (* trans_lst = [] *)
  intros. 
  inversion H; subst.
  inversion H0; subst. split; auto.

  (* trans_lst = a :: _ *)
  intros.
  inversion H; subst.
  inversion H0; subst. 
  clear H. clear H0.
  assert (H_eq: ws = ws0) by congruence.
  rewrite H_eq in *.
  assert (H_eq': ed_pol = ed_pol0) by congruence.
  rewrite H_eq' in *. 
  assert (H_conj: ws' = ws'0 /\ flg = flg0).
  { eapply trans_validate_deterministic; eauto. }
  inversion H_conj as [H_ws_eq H_flg_eq].
  clear H_conj. 
  remember (mp_upd chaincode_id world_state beq_cc_id_dec wsc (tx_ccid a) ws')
    as mp_upd_ws'.
  assert (H_mp_upd_ws'_eq_ws'0:
            mp_upd_ws' =
            mp_upd chaincode_id world_state beq_cc_id_dec wsc (tx_ccid a) ws'0). 
  { rewrite Heqmp_upd_ws'. congruence. }
  rewrite <- H_mp_upd_ws'_eq_ws'0 in H15.
  specialize (IHtrans_lst (mp_upd_ws') wsc1 wsc2).
  specialize (IHtrans_lst flgs flgs0 pn). 
  specialize (IHtrans_lst H11 H15).
  inversion IHtrans_lst. 
  split; congruence.
Qed.

Lemma nth_ex :
  forall (A : Type) (lst : list A),
    List.length lst > 0 -> 
    exists e, nth_error lst (List.length lst - 1) = Some e.
Proof.
  induction lst. 
  intros. simpl in H. inversion H.
  intros.
  destruct lst.
  simpl. exists a; auto.
  assert (List.length (a0 :: lst) > 0).
  simpl. lia.
  apply IHlst in H0.
  simpl.
  simpl in H0.
  asserts_rewrite (List.length lst = List.length lst - 0).
  lia. auto.
Qed.

Lemma peer_blk_step_deterministic :
  forall hf pid clients peers os clients1 peers1 os1 clients2 peers2 os2, 
    step_rel_act hf (Act_peer_add_blk pid)
                 (clients, (peers, os)) (clients1, (peers1, os1)) ->
    step_rel_act hf (Act_peer_add_blk pid) 
                 (clients, (peers, os)) (clients2, (peers2, os2)) ->
    (clients1 = clients2 /\ peers1 = peers2 /\ os1 = os2).
Proof.
  introv. 
  intros step_rel_act1 step_rel_act2.
  inverts step_rel_act1.
  inverts step_rel_act2.
  inversion H as [peers0 [os0 [clients' [peers' [os' H_body]]]]]; clear H.
  inversion H_body as [H_eq_conf1 [H_eq_conf2 H_step]]; clear H_body.
  inverts H_eq_conf1.
  inverts H_eq_conf2.
  inversion H0 as [peers [os [clients'' [peers'' [os'' H_body]]]]]; clear H0.
  inversion H_body as [H_eq_conf1' [H_eq_conf2' H_step']]; clear H_body. 
  inverts H_eq_conf1'.
  inverts H_eq_conf2'. 
  inversion H_step; subst.
  inversion H_step'; subst.
  split. auto. split. 2: { auto. }
  assert (H_pn_eq_pn0: pn = pn0) by congruence.
  rewrite H_pn_eq_pn0 in *. clear H_pn_eq_pn0. 
  assert (H_wsc_eq_wsc0: wsc = wsc0) by congruence.
  rewrite H_wsc_eq_wsc0 in *. clear H_wsc_eq_wsc0.
  assert (H_blks_eq_blks0: blks = blks0) by congruence.
  rewrite H_blks_eq_blks0 in *. clear H_blks_eq_blks0.  

  clear H_step. clear H_step'.
  assert (H_cases: List.length blks0 = 0 \/ List.length blks0 > 0).
  { destruct (List.length blks0); lia. }
  inversion H_cases.
  (* List.length blks0 = 0 *)
  inversion H4. inversion H9.
  specialize (H7 H).
  specialize (H12 H).
  rewrite H7 in H1. rewrite H12 in H6.
  rewrite H1 in H6.
  inversion H6; subst.
  
  assert (H_wsc_flg_eq: wsc' = wsc'0 /\ flags = flags0).
  { eapply trans_lst_validate_deterministic; eauto. }
  inversion H_wsc_flg_eq.
  congruence. 
  
  (* length blks0 > 0 *)
  assert (H_ex_blk':
            exists blk', nth_error blks0 (Datatypes.length blks0 - 1) = Some blk').
  { eapply nth_ex; eauto. }
  inversion H_ex_blk' as [blk' H_nth_error]; clear H_ex_blk'. 

  inversion H4 as [H_zero H_gt_zero]; clear H4. clear H_zero. 
  specialize (H_gt_zero H). 
  specialize (H_gt_zero blk' H_nth_error).
  inversion H_gt_zero as [H_blk_no H_blk_prev_hash]; clear H_gt_zero. 

  inversion H9 as [H_zero' H_gt_zero']; clear H9. clear H_zero'. 
  specialize (H_gt_zero' H).
  specialize (H_gt_zero' blk' H_nth_error).
  inversion H_gt_zero' as [H_blk_no' H_blk_prev_hash']; clear H_gt_zero'.
  
  rewrite H_blk_no in *. rewrite H_blk_no' in *.
  rewrite H1 in H6. inversion H6; subst.

  assert (H_wsc_flg_eq': wsc' = wsc'0 /\ flags = flags0).
  { eapply trans_lst_validate_deterministic; eauto. }
  inversion H_wsc_flg_eq'.
  congruence. 

Qed.

Lemma peer_add_blk_ext_bc :
  forall hf clients peers os clients' peers' os' pid pn pn' blks blks' wsc wsc',  
    step_rel_act hf
                 (Act_peer_add_blk pid) (clients, (peers, os))
                 (clients', (peers', os')) -> 
    peers pid = Some pn ->
    peers' pid = Some pn' ->
    pn.(peer_ledger) = Ledger (BC blks) wsc -> 
    pn'.(peer_ledger) = Ledger (BC blks') wsc' ->  
    (exists blk', List.app blks [blk'] = blks'). 
Proof.
  introv.
  intro H_step_rel_act.
  intros H_peers_pid H_peers'_pid H_ledger_pn H_ledger_pn'.
  inversion H_step_rel_act; subst.
  inversion H as
      [peers0 [os0 [clients'0 [peers'0 [os'0 H_body]]]]]; clear H.
  inversion H_body as [H_eq1 [H_eq2 H_step]]; clear H_body.
  inversion H_eq1; subst.
  inversion H_eq2; subst.
  assert (exists blk', blks' = List.app blks [blk']).
  { eapply blk_step_extends_bc; eauto. }
  inversion H. exists x0. auto.
Qed. 

Lemma peer_add_blks_preserve_pn_emptiness :
  forall hf pid k clients peers os clients' peers' os' pn,
    k_step_peer_add_blk hf pid k 
                        (clients, (peers, os)) (clients', (peers', os')) -> 
    peers pid = Some pn -> 
    (exists pn', peers' pid = Some pn'). 
Proof.
  induction k.
  intros.
  inverts H. rewrite H0. exists pn. auto.
  intros. 
  inverts H.
  inverts H2.
  inversion H as [peers0 [os0 [clients'' [peers'' [os'' [H_eq1 [H_eq2 H_step]]]]]]];
    clear H.
  inverts H_eq1. inversion H_eq2; subst.
  fold  (k_step_peer_add_blk hf pid k) in H3.
  assert (H_ex1: exists pn'', peers'' pid = Some pn'').
  {
    eapply peer_add_blk_preserve_pn_emptiness; eauto.
    econstructor. repeat eexists. eauto.
  }
  inversion H_ex1 as [pn'' H_peer''_pid]; clear H_ex1. 
  specialize (IHk clients'' peers'' os'' clients' peers' os' pn'' H3 H_peer''_pid).
  auto.
Qed. 

Lemma peer_add_blks_ext_bc : 
  forall hf pid k clients peers os clients' peers' os' pn pn' blks blks' wsc wsc', 
    k_step_peer_add_blk hf pid k 
                        (clients, (peers, os)) (clients', (peers', os')) -> 
    peers pid = Some pn ->
    peers' pid = Some pn' ->
    pn.(peer_ledger) = Ledger (BC blks) wsc -> 
    pn'.(peer_ledger) = Ledger (BC blks') wsc' ->  
    (exists blks'', (List.length blks'' = k /\ List.app blks blks'' = blks')).
Proof.
  induction k.
  (* base case *)
  intros.
  inversion H; subst.
  assert (H_eq: pn = pn') by congruence.
  assert (H_eq': blks = blks') by congruence.
  rewrite H_eq'. 
  exists []. simpl. split; auto. autorewrite with list. auto.

  (* inductive case *)
  intros.
  inversion H; subst.
  destruct x'' as [clients'' [peers'' os'']].

  assert (H_ex_pn'': exists pn'', peers'' pid = Some pn'').
  { eapply peer_add_blk_preserve_pn_emptiness; eauto. }
  inversion H_ex_pn'' as [pn'' H_pn'']; clear H_ex_pn''.
  assert (H_ex: exists blks1 wsc1, peer_ledger pn'' = Ledger (BC blks1) wsc1).
  { destruct (peer_ledger pn''). destruct b. repeat eexists; eauto. }
  inversion H_ex as [blks1 [wsc1 H_pn''_ledger]]; clear H_ex. 

  assert (H_ex_blks'_step_1: exists blk', List.app blks [blk'] = blks1).
  { eapply peer_add_blk_ext_bc; eauto. }
  
  fold (k_step_peer_add_blk hf pid) in H6.
  specialize (IHk clients'' peers'' os'' clients' peers' os').
  specialize (IHk pn'' pn' blks1 blks' wsc1 wsc'). 
  specialize (IHk H6 H_pn'' H1 H_pn''_ledger H3).
  inversion IHk as [blks0 [H_len_blks0 H_ext]]; clear IHk.
  inversion H_ex_blks'_step_1 as [blk1 H_blks1]; clear H_ex_blks'_step_1.
  rewrite <- H_blks1 in H_ext.
  assert (((blks ++ [blk1]) ++ blks0)%list = (blks ++ ([blk1] ++ blks0))%list).
  { symmetry. eapply app_assoc. }
  simpl in H4.

  exists (blk1 :: blks0).
  simpl. split; congruence.
Qed.

Lemma peer_add_blk_local :
  forall hf clients peers os clients' peers' os' pid pid', 
    pid <> pid' -> 
    step hf clients peers os clients' peers' os' (Act_peer_add_blk pid) ->
    peers pid' = peers' pid'.
Proof.
  intros.
  inverts H0. 
  rewrite mp_upd_neq; auto.
Qed.   


(* proof of the main theorem *)

Theorem consensus_preserved : 
  forall hf clients peers os clients' peers' os' act,
    cl hf clients peers os ->
    step hf clients peers os clients' peers' os' act ->
    cl hf clients' peers' os'. 
Proof. 
  introv. 
  intro H_cl.
  intro H_step.
  inversion H_step.

  (* Act_cli_prop cli_id target_pn_idxs = act *) 
  rename H5 into H_act.
  rewrite <- H_act in H_step.
  assert (H_lgr_os_rel: same_ep_ledger_in_peers peers peers' /\ os = os').
  { eapply cli_prop_step_preservation; eauto. }
  inversion H_lgr_os_rel as [H_lgr_rel H_os_rel].
  assert (H_os_ext : ord_blks_ext os os'). 
  { apply os_eq_ext; auto. }
  eapply ledger_preserved_impl_invariant_preserved; eauto. 

  (* Act_peer_resp peer_id cli_id = act *) 
  rename H15 into H_act.
  rewrite <- H_act in H_step.
  assert (H_lgr_os_rel: same_ep_ledger_in_peers peers peers' /\ os = os'). 
  { eapply peer_resp_step_preservation; eauto. }
  inversion H_lgr_os_rel as [H_lgr_rel H_os_rel].
  assert (H_os_ext : ord_blks_ext os os'). 
  { apply os_eq_ext; auto. }
  eapply ledger_preserved_impl_invariant_preserved; eauto.

  (* Act_peer_drop_prop peer_id = act *) 
  rename H4 into H_act.
  rewrite <- H_act in H_step.
  assert (H_lgr_os_rel: same_ep_ledger_in_peers peers peers' /\ os = os').
  { eapply peer_drop_prop_preservation; eauto. } 
  inversion H_lgr_os_rel as [H_lgr_rel H_os_rel].
  assert (H_os_ext : ord_blks_ext os os'). 
  { apply os_eq_ext; auto. }
  eapply ledger_preserved_impl_invariant_preserved; eauto.

  (* Act_cli_send_trans cli_id = act *) 
  rename H13 into H_act.
  rewrite <- H_act in H_step.
  assert (H_lgr_os_rel: same_ep_ledger_in_peers peers peers' /\ ord_blks_ext os os').
  { eapply cli_send_trans_preservation; eauto. }
  inversion H_lgr_os_rel. 
  eapply ledger_preserved_impl_invariant_preserved; eauto. 

  (* Act_cli_drop_prop cli_id = act *)
  rename H6 into H_act.
  rewrite <- H_act in H_step.
  assert (H_lgr_os_rel: same_ep_ledger_in_peers peers peers' /\ ord_blks_ext os os'). 
  { eapply cli_drop_prop_preservation; eauto. }
  inversion H_lgr_os_rel.
  eapply ledger_preserved_impl_invariant_preserved; eauto.

  (* Act_ord_crt_blk = act *)
  rename H10 into H_act.
  rewrite <- H_act in H_step.
  assert (H_lgr_os_rel: same_ep_ledger_in_peers peers peers' /\ ord_blks_ext os os').
  { eapply os_crt_preservation; eauto. }
  inversion H_lgr_os_rel.
  eapply ledger_preserved_impl_invariant_preserved; eauto.

  (* Act_peer_add_blk peer_id = act *) 
  rename H9 into H_act.
  rewrite <- H_act in H_step.
  
  unfold cl.
  introv. 

  rename H7 into H_peers'.
  
  assert (H_peer_id: peer_id = pid1 \/ peer_id = pid2 \/
                     peer_id <> pid1 /\ peer_id <> pid2).
  {
    destruct (beq_peer_id_dec peer_id pid1);
      destruct (beq_peer_id_dec peer_id pid2).
    left; intuition. left; auto. right; left; auto.
    right; right; intuition. 
  }

  inversion H_peer_id.
  
  (* peer_id = pid1 -- the step is taken by the first peer *) 
  rename H7 into H_peer_id_eq_pid1.
  intros H_pid_neq H_peers'_pid1 H_peers'_pid2.

  assert (H_same_ep_after_step:
            ep_of_epcc pn.(peer_ep_cc) = ep_of_epcc pn1.(peer_ep_cc)).
  { eapply step_preserves_peer_ep_cc; eauto. congruence. }
  rewrite <- H_same_ep_after_step.
  assert (H_pid2_same_pn: peers' pid2 = peers pid2).
  { eapply blk_step_peer_intact; eauto. congruence. }
  assert (H_peers_pid2: peers pid2 = Some pn2)
    by congruence. 
  unfold cl in H_cl.
  specialize (H_cl pid1 pid2 pn pn2 H_pid_neq).
  assert (H_peers_pid1: peers pid1 = Some pn) by congruence. 
  specialize (H_cl H_peers_pid1 H_peers_pid2).
  inversion H_cl as [H_eq_ep_cc H_forall]. split. auto.
  clear H_cl. 
  rename H_forall into H_cl. 

  introv. 
  intros H_ledger_pn1 H_ledger_pn2 H_len_blks_le.
  rename pn1 into pn1'. rename pn2 into pn2'.
  rename blks1 into blks1'. rename blks2 into blks2'.
  rename wsc1 into wsc1'. rename wsc2 into wsc2'. 

  rewrite H_peer_id_eq_pid1 in *.

  assert (H_blks_extend: exists new_blk, blks1' = List.app blks (new_blk :: nil)).
  { eapply blk_step_extends_bc; eauto. }
  inversion H_blks_extend as [blk' H_blks1'_blks]; clear H_blks_extend.
    
  rename pn into pn1. rename blks into blks1. rename wsc into wsc1. 
  
  assert (H_orig_lst_len_le: List.length blks1 <= List.length blks2').
  {
    rewrite H_blks1'_blks in H_len_blks_le.
    autorewrite with list in H_len_blks_le.
    lia. 
  }

  specialize (H_cl blks1 blks2' wsc1 wsc2').
  specialize (H_cl H2 H_ledger_pn2). 
  specialize (H_cl H_orig_lst_len_le).
  inversion H_cl as [H_blks1_firstn H_ex]; clear H_cl.
  inversion H_ex as [peers'' [clients'' [os'' [pn1'' H_body]]]]; clear H_ex. 
  inversion H_body as [H_k_step_orig [H_peers''_pid1 H_peer_ledger_pn1'']];
    clear H_body.
  
  assert (H_len_diff_pre_post:
            List.length blks2' - List.length blks1 =
            S (List.length blks2' - List.length blks1')).
  {
    rewrite H_blks1'_blks. autorewrite with list.
    assert (List.length blks2' >= (List.length blks1 + 1)).
    { rewrite H_blks1'_blks in H_len_blks_le.
      autorewrite with list in H_len_blks_le. simpl in H_len_blks_le.
      auto with arith. }
    simpl. lia.
  }
  rewrite H_len_diff_pre_post in H_k_step_orig. 
  inversion H_k_step_orig.
  clear H11. (* x = (clients, (peers, os)) *)
  clear H12. (* x' = (clients'', (peers'', os'')) *)
  rename H9 into H_step_rel_act.
  rename H10 into H_k_R.
  fold (k_step_peer_add_blk hf pid1) in H_k_R.
  assert (H_step_rel_act_0:
            step_rel_act hf (Act_peer_add_blk pid1)
                         (clients, (peers, os)) (clients', (peers', os'))).
  { unfold step_rel_act. repeat eexists; eauto. }
  
  assert (H_post_eq: x'' = (clients', (peers', os'))).
  {
    destruct x''. destruct p.
    assert (m = clients' /\ m0 = peers' /\ o = os'). 
    { eapply peer_blk_step_deterministic; eauto. }
    inversion H9 as [H_eq1 [H_eq2 H_eq3]]; clear H9.
    congruence. 
  }
  rewrite H_post_eq in *.

  assert (H_ex_blks'':
            exists blks'',
             (List.length blks'' = (Datatypes.length blks2' - Datatypes.length blks1')
              /\ List.app blks1' blks'' = blks2')). 
  {
    rewrite H_ledger_pn2 in H_peer_ledger_pn1''.
    eapply peer_add_blks_ext_bc; eauto.
  }
  inversion H_ex_blks'' as [blks'' [H_len_blks'' H_blks2'_blks1']]; clear H_ex_blks''.
  split.
  (*  blks1' = firstn (Datatypes.length blks1') blks2' *)
  specialize (firstn_app (List.length blks1') blks1' blks'').
  intro H_pre_firstn_eq.
  rewrite H_blks2'_blks1' in H_pre_firstn_eq.
  rewrite H_pre_firstn_eq.
  asserts_rewrite (List.length blks1' - List.length blks1' = 0). lia. 
  simpl. autorewrite with list.
  symmetry. apply firstn_all.
  (* ability to catch up *)
  exists peers''. exists clients''. exists os''.
  exists pn1''.
  split; auto. 
  
  inversion H7.
  (* peer_id = pid2 -- the step is taken by the second peer *)
  
  intros H_pid_neq H_peers'_pid1 H_peers'_pid2.

  assert (H_pid1_same_pn: peers' pid1 = peers pid1). 
  { eapply blk_step_peer_intact; eauto. congruence. }
  assert (H_peers_pid1: peers pid1 = Some pn1)
    by congruence.
  
  assert (H_same_ep_after_step:
            ep_of_epcc pn.(peer_ep_cc) = ep_of_epcc pn2.(peer_ep_cc)).
  { eapply step_preserves_peer_ep_cc; eauto. congruence. }
  rewrite <- H_same_ep_after_step.

  assert (H_peers_pid2: peers pid2 = Some pn) by congruence.

  remember H_cl as H_lgr_agreement.
  clear HeqH_lgr_agreement. 
  unfold cl in H_lgr_agreement. 
  specialize (H_lgr_agreement pid1 pid2 pn1 pn H_pid_neq). 
  specialize (H_lgr_agreement H_peers_pid1 H_peers_pid2).
  inversion H_lgr_agreement as [H_eq_ep_cc H_forall]. split. auto.
  clear H_lgr_agreement. clear H_forall. 

  introv. 
  intros H_ledger_pn1 H_ledger_pn2 H_len_blks_le. 
  rename pn1 into pn1'. rename pn2 into pn2'.
  rename blks1 into blks1'. rename blks2 into blks2'.
  rename wsc1 into wsc1'. rename wsc2 into wsc2'.
  
  rename H9 into H_peer_id_eq_pid2. 
  rewrite H_peer_id_eq_pid2 in *.

  rename pn into pn2.
  rename blks into blks2.
  rename wsc into wsc2.

  assert (H_blks_extend: exists new_blk, blks2' = List.app blks2 (new_blk :: nil)).
  { eapply blk_step_extends_bc; eauto. }
  inversion H_blks_extend as [blk' H_blks2'_blks2]; clear H_blks_extend.

  assert (H_orig_blks_len_cases:
            List.length blks1' > List.length blks2 \/
            List.length blks1' <= List.length blks2) by lia.          
  inversion H_orig_blks_len_cases.
  
  (* original blockchain for pid1 longer than original blockchain for pid2 *)
  rename H9 into H_len_blks1'_gt_blks2.

  specialize (H_cl pid2 pid1 pn2 pn1'). 
  assert (H_pid2_neq_pid1:  pid2 <> pid1) by auto with arith.
  specialize (H_cl H_pid2_neq_pid1).
  specialize (H_cl H H_peers_pid1).
  inversion H_cl as [H_eq_ep H_forall]; clear H_cl.
  rename H_forall into H_cl. 
  specialize (H_cl blks2 blks1' wsc2 wsc1').
  specialize (H_cl H2 H_ledger_pn1).
  assert (H_len_le: List.length blks2 <= List.length blks1') by auto with arith. 
  specialize (H_cl H_len_le). 
  inversion H_cl as [H_blks2_firstn_blks1' H_ex]; clear H_cl.
  inversion H_ex as [peers'' [clients'' [os'' [pn'' H_body]]]]; clear H_ex.
  inversion H_body as [H_k_step_peer_add_blk [H_peers''_pid2 H_peer_ledger_pn'']];
    clear H_body.
  
  assert (H_len_diff: Datatypes.length blks1' - Datatypes.length blks2 = 1).
  {
    rewrite H_blks2'_blks2 in H_len_blks_le.
    autorewrite with list in H_len_blks_le. 
    simpl in H_len_blks_le.
    lia. 
  }

  rewrite H_len_diff in H_k_step_peer_add_blk.
  inversion H_k_step_peer_add_blk. clear H12. clear H13. 
  inversion H11. rewrite H14 in *. clear H14. 
  rename H10 into H_step_rel_act_2.
  assert (H_step_rel_act_1:
            step_rel_act hf (Act_peer_add_blk pid2)
                         (clients, (peers, os)) (clients', (peers', os'))).
  { econstructor. repeat eexists; eauto. }
  assert (H_eq_3: clients' = clients'' /\ peers' = peers'' /\ os' = os'').
  { eapply peer_blk_step_deterministic; eauto. }
  inversion H_eq_3 as [H_eq_clients [H_eq_peers H_eq_os]]; clear H_eq_3.   
  
  rewrite <- H_eq_clients in *.
  rewrite <- H_eq_peers in *.
  rewrite <- H_eq_os in *.
  assert (H_lgr_eq: pn1'.(peer_ledger) = pn2'.(peer_ledger))
    by congruence. 
  assert (H_blks_eq: blks1' = blks2') by congruence. 
  split.
  rewrite H_blks_eq. symmetry. apply firstn_all.
  
  exists peers'. exists clients'. exists os'. exists pn1'.
  asserts_rewrite (List.length blks2' - List.length blks1' = 0).
  { rewrite H_blks_eq. auto with arith. }
  split.
  econstructor; eauto. 
  split; auto.

  rename H9 into H_len_blks1'_le_blks2. 

  unfold cl in H_cl.
  
  specialize (H_cl pid1 pid2 pn1' pn2).
  specialize (H_cl H_pid_neq).
  specialize (H_cl H_peers_pid1 H).
  inversion H_cl as [H_eq_ep H_forall]; clear H_cl.
  rename H_forall into H_cl.
  specialize (H_cl blks1' blks2).
  specialize (H_cl wsc1' wsc2).
  specialize (H_cl H_ledger_pn1 H2).
  specialize (H_cl H_len_blks1'_le_blks2).
  inversion H_cl as [H_firstn_blks H_ex]; clear H_cl.
  inversion H_ex as [peers'' [clients'' [os'' [pn1'' H_body]]]]; clear H_ex.
  inversion H_body as [H_k_step [H_peers''_pid1 H_lgr_eq'']]; clear H_body.

  assert (H_same_eplgr_ext:
            same_ep_ledger_in_peers_ext peers peers' pid1 pid1 /\ os = os'). 
  { eapply peer_add_blk_preservation; eauto. }
  inversion H_same_eplgr_ext as [H_same_eplgr_in_peers_ext H_eq_os_os'];
    clear H_same_eplgr_ext.
  
  assert (H_ord_blks_ext: ord_blks_ext os os').
  { rewrite H_eq_os_os'. apply os_blks_ext_refl. }

  assert (H''': 
    exists clients''' peers''' os''',
      (
        k_step_peer_add_blk hf pid1 (List.length blks2 - List.length blks1') 
                            (clients', (peers', os')) (clients''', (peers''', os''')) /\
        same_ep_ledger_in_peers_ext peers'' peers''' pid1 pid1 /\
        ord_blks_ext os'' os''')
  ).
  { eapply peer_add_blk_simulate_k_steps_ext; eauto. }
  
  inversion H''' as
      [clients'''
         [peers'''
            [os''' [H_k_step_peer_add_blk''' [H_same_eplgr''' H_ord_blks_ext''']]]]];
    clear H'''.

  assert (H_same_eplgr__''': same_ep_ledger_in_peers_ext peers peers''' pid2 pid1).
  {
    unfold same_ep_ledger_in_peers_ext.
    unfold same_ep_ledger_in_peers_ext in H_same_eplgr'''.
    inversion H_same_eplgr''' as
        [H_peers''_peers'''_pid1_same_nn H_same_eplgr_ext_''_'''_pid1];
      clear H_same_eplgr'''.
    assert (H_ex_pn''': exists pn''', peers''' pid1 = Some pn''').
    { eapply peer_add_blks_preserve_pn_emptiness; eauto. }
    inversion H_ex_pn'''. 
    assert (H_peers'''_pid1_nn: peers''' pid1 <> None).
    { eapply some_implies_nn; eauto. }
    assert (H_peers_pid2_nn: peers pid2 <> None).
    { eapply some_implies_nn; eauto. }
    split.
    split; intro; auto.
    unfold same_ep_ledger_ext.
    intros pn20 pn1'''0. intros H_peers_pid2_res H_peers'''_pid1_res.
    rewrite H in H_peers_pid2_res.
    inversion H_peers_pid2_res. rewrite <- H11 in *.
    unfold same_ep_ledger_ext in H_same_eplgr_ext_''_'''_pid1.
    rewrite <- H_lgr_eq''.
    specialize (H_same_eplgr_ext_''_'''_pid1 pn1'' pn1'''0).
    specialize (H_same_eplgr_ext_''_'''_pid1 H_peers''_pid1 H_peers'''_pid1_res).
    inversion H_same_eplgr_ext_''_'''_pid1 as [H_ep_eq_''_''' H_lgr_eq_''_'''];
      clear H_same_eplgr_ext_''_'''_pid1.
    split; auto.
    rewrite <- H_eq_ep.
    eapply steps_preserve_peer_ep_cc; eauto. 
  }
  assert (H_ord_blks_ext__''': ord_blks_ext os os'''). 
  {
    assert (os' = os''').
    { eapply peer_add_blks_preserves_os; eauto. }
    assert (os = os''') by congruence.
    rewrite <- H10. 
    apply os_blks_ext_refl. 
  }
  assert (H'''':
            exists clients'''' peers'''' os'''',
             step_rel_act hf (Act_peer_add_blk pid1)
                          (clients''', (peers''', os'''))
                          (clients'''', (peers'''', os'''')) /\
             same_ep_ledger_in_peers_ext peers' peers'''' pid2 pid1 /\
             ord_blks_ext os' os'''').
  {
    eapply peer_add_blk_simulate_ext; eauto. 
    econstructor. repeat eexists. eauto.
  }
  inversion H'''' as
      [clients_4
         [peers_4
            [os_4
               [H_step_rel_4 [H_same_eplgr_4 H_ord_blks_4]]]]]; clear H''''.

  split.
  
  rewrite H_blks2'_blks2.
  rewrite firstn_app.
  asserts_rewrite (Datatypes.length blks1' - Datatypes.length blks2 = 0). 
  { lia. } 
  simpl. autorewrite with list. auto.

  unfold same_ep_ledger_in_peers_ext in H_same_eplgr_4.
  inversion H_same_eplgr_4.  
  assert (peers' pid2 <> None) by (eapply some_implies_nn; eauto).
  assert (peers_4 pid1 <> None) by intuition.
  apply nn_implies_some in H12.
  inversion H12 as [pn_4 H_peers_4_pid1]; clear H12. 

  exists peers_4. exists clients_4. exists os_4.
  exists pn_4.
  split.

  assert (H_lst_len_suc:
            List.length blks2' - List.length blks1' =
            S (List.length blks2 - List.length blks1')).
  {
    rewrite H_blks2'_blks2.
    autorewrite with list. simpl. 
    lia.
  }
  rewrite H_lst_len_suc.  
  eapply k_back; eauto.

  split. auto.

  unfold same_ep_ledger_ext in H10.
  specialize (H10 pn2' pn_4 H_peers'_pid2 H_peers_4_pid1).
  inversion H10. congruence.

  (* peer_id <> pid1 /\ peer_id <> pid2 *)

  inversion H9 as [H_peer_id_ne_pid1 H_peer_id_ne_pid2]; clear H9. 

  assert (peers pid1 = peers' pid1).
  { eapply peer_add_blk_local; eauto. }
  assert (peers pid2 = peers' pid2).
  { eapply peer_add_blk_local; eauto. }

  intros H_neq_pid1_pid2 H_peers'_pid1 H_peers'_pid2.

  assert (H_peers_pid1: peers pid1 = Some pn1) by congruence.
  assert (H_peers_pid2: peers pid2 = Some pn2) by congruence. 
  
  unfold cl in H_cl.
  specialize (H_cl pid1 pid2 pn1 pn2 H_neq_pid1_pid2).
  specialize (H_cl H_peers_pid1 H_peers_pid2).

  inversion H_cl as [H_eq_ep H_forall]; clear H_cl.
  split. auto. 
  intros. 
  specialize (H_forall blks1 blks2 wsc1 wsc2 H11 H12 H13).
  inversion H_forall as [H_firstn H_ex]; clear H_forall.
  split. auto.
  inversion H_ex as
      [peers''
         [clients''
            [os''
               [pn1'' [H_k_step_orig [H_peers''_pid1 H_peer_lgr_orig]]]]]];
    clear H_ex.  
  
  eapply peer_add_blk_simulate_k_steps_ext
    with (clients2 := clients') (peers2 := peers') (os2 := os')
         (pid1 := pid1) (pid2 := pid1) 
    in H_k_step_orig.
  inversion H_k_step_orig as
      [clients''' [peers''' [os''' [H_k_step' [H_same_ep_lgr' H_ord_blks']]]]];
    clear H_k_step_orig.
  exists peers'''. exists clients'''. exists os'''. 
  unfold same_ep_ledger_in_peers in H_same_ep_lgr'.
  inversion H_same_ep_lgr'.
  assert (peers'' pid1 <> None) by (eapply some_implies_nn; eauto).
  assert (peers''' pid1 <> None) by intuition.
  assert (H_ex: exists pn1''', peers''' pid1 = Some pn1''')
    by (eapply nn_implies_some; eauto).
  inversion H_ex as [pn1''' H_peers'''_pid1]; clear H_ex.
  exists pn1'''.
  split. auto.
  split. auto.
  rewrite <- H_peer_lgr_orig.
  unfold same_ep_ledger_in_peers_ext in H_same_ep_lgr'.
  inversion H_same_ep_lgr'.
  unfold same_ep_ledger_ext in H19. 
  specialize (H19 pn1'' pn1''' H_peers''_pid1 H_peers'''_pid1).
  inversion H19; symmetry; auto.

  unfold same_ep_ledger_in_peers_ext.
  rewrite <- H9. 
  split. intuition.
  unfold same_ep_ledger_ext.
  intros.
  asserts_rewrite (pn0 = pn1). congruence.
  asserts_rewrite (pn3 = pn1). congruence.
  split; auto.

  inverts H_step. apply os_blks_ext_refl.

Qed. 
                  

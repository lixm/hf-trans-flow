
(* Example transaction flow for duduction on the price of a car *) 

Require Import List.
Require Import Lia.
Require Import Logic.FunctionalExtensionality.

Require Import SfLib.
Require Import LibTactics.
Require Import MyUtils. 
Require Import Entities.
Require Import TransFlow.


Definition emp `(key_tp : Type) `(val_tp : Type) : mp_tp key_tp val_tp :=
  fun k => None. 

Definition car1 := Key 1.
Definition car2 := Key 2. 

Definition cp_ws : world_state :=
  mp_upd key (prod val ver) beq_key_dec 
         (mp_upd key (prod val ver) beq_key_dec (emp key (prod val ver))
                 car1 (PrimVal 200, Ver 1))
         car2 (PrimVal 300, Ver 1). 

Definition cp_chaincode_id : chaincode_id := CcId 1.

Definition cp_rset0 : read_set := emp key ver.
Definition cp_wset0 : write_set := emp key val_or_del. 

Definition cp_rset11 : read_set := emp key ver.
Definition cp_wset11 : write_set :=
  mp_upd key val_or_del beq_key_dec (emp key val_or_del)
         car1 (Val_or_del1 (PrimVal 200)).

Definition cp_rset12 : read_set := emp key ver.
Definition cp_wset12 : write_set :=
  mp_upd key val_or_del beq_key_dec (emp key val_or_del)
         car2 (Val_or_del1 (PrimVal 300)).

Definition cp_rset21 : read_set := 
  mp_upd key ver beq_key_dec (emp key ver) car1 (Ver 1). 
Definition cp_wset21 : write_set :=
  mp_upd key val_or_del beq_key_dec (emp key val_or_del)
         car1 (Val_or_del1 (PrimVal 180)).

Definition cp_rset22 : read_set :=
  mp_upd key ver beq_key_dec (emp key ver) car2 (Ver 1).
Definition cp_wset22 : write_set :=
    mp_upd key val_or_del beq_key_dec (emp key val_or_del)
         car2 (Val_or_del1 (PrimVal 270)). 

Eval compute in (Nat.div (100 * 4) 5). 

Theorem beq_op_dec : forall (op1 op2 : operation), {op1 = op2} + {op1 <> op2}.
Proof. repeat decide equality. Qed. 
  
Definition cp_upd_op1 : operation := Oper 1.
Definition cp_upd_op2 : operation := Oper 2.
Definition cp_dc_op1 : operation := Oper 3. 
Definition cp_dc_op2 : operation := Oper 4. 

(* peer_interp_oper : operation -> world_state -> (prod read_set write_set) *)
Definition cp_op_interp : operation -> world_state -> (prod read_set write_set) :=
  func_upd _ _ beq_op_dec
           (func_upd _ _ beq_op_dec
                     ((func_upd _ _ beq_op_dec 
                                (func_upd _ _ beq_op_dec
                                          (fun op => fun ws => (cp_rset0, cp_wset0))
                                          cp_upd_op1 (fun ws => (cp_rset11, cp_wset11))))
                        cp_upd_op2 (fun ws => (cp_rset12, cp_wset12)))
                     cp_dc_op1
                     (fun ws => match ws car1 with
                                  Some (PrimVal n, Ver i) => (
                                    (mp_upd _ _ beq_key_dec (emp key ver) car1 (Ver i)), 
                                    (mp_upd _ _ beq_key_dec (emp key val_or_del)
                                            car1 (Val_or_del1 (PrimVal (Nat.div (n * 9) 10))))
                                  )
                                | _ => (cp_rset0, cp_wset0)
                                end))
           cp_dc_op2
           (fun ws => match ws car2 with
                        Some (PrimVal n, Ver i) => (
                          (mp_upd _ _ beq_key_dec (emp key ver) car2 (Ver i)), 
                          (mp_upd _ _ beq_key_dec (emp key val_or_del)
                                  car2 (Val_or_del1 (PrimVal (Nat.div (n * 9) 10)))))
                      | _ => (cp_rset0, cp_wset0)
                      end). 
           
Variable hf : hash_func. 

Definition cp_cli_id : client_id := ClId 1. 
Definition cp_peer1_id : peer_id := PrId 1.
Definition cp_peer2_id : peer_id := PrId 2.

Definition cp_ep : endorsement_pol :=
  fun sigs =>
    andb
      (List.existsb (fun s => match s with Sig (PubK 1) _ => true | _ => false end) sigs)
      (List.existsb (fun s => match s with Sig (PubK 2) _ => true | _ => false end) sigs).

Check (andb). 

Definition cp_epcc : chaincode_id -> option (prod endorsement_pol chaincode) :=
  mp_upd _ _ beq_cc_id_dec
         (emp chaincode_id (prod endorsement_pol chaincode))
         cp_chaincode_id
         (cp_ep, Chaincode [cp_upd_op1; cp_upd_op2; cp_dc_op1; cp_dc_op2]).

Definition cp_txp11_1 : tx_proposal_field :=
  TxProposal cp_peer1_id
             (hf tx_field (TxField cp_cli_id cp_chaincode_id cp_upd_op1 (TS 1)))
             cp_chaincode_id cp_upd_op1 cp_rset11 cp_wset11.

(* endorsement for transaction 1 in block 1 by peer 1 *)
Definition cp_ed11_1 : trans_endorsed_msg :=
   Trans_endorsed_msg cp_txp11_1
                      (Sig (PubK 1) (hf tx_proposal_field cp_txp11_1)).

Definition cp_txp11_2 : tx_proposal_field :=
  TxProposal cp_peer2_id
             (hf tx_field (TxField cp_cli_id cp_chaincode_id cp_upd_op1 (TS 1)))
             cp_chaincode_id cp_upd_op1 cp_rset11 cp_wset11. 

(* endorsement for transaction 1 in block 1 by peer 2 *)
Definition cp_ed11_2 : trans_endorsed_msg :=
  Trans_endorsed_msg cp_txp11_2
                     (Sig (PubK 2) (hf tx_proposal_field cp_txp11_2)). 
      
(* transaction 1 in block 1 *)
Definition cp_tx11 : transaction :=
  Trans cp_chaincode_id cp_upd_op1 (cp_rset11, cp_wset11) (cp_ed11_1 :: cp_ed11_2 :: nil).

Definition cp_txp12_1 : tx_proposal_field :=
  TxProposal cp_peer1_id
             (hf tx_field (TxField cp_cli_id cp_chaincode_id cp_upd_op2 (TS 2)))
             cp_chaincode_id cp_upd_op2 cp_rset12 cp_wset12. 

(* endorsement for transaction 2 in block 1 by peer 1 *)
Definition cp_ed12_1 : trans_endorsed_msg :=
   Trans_endorsed_msg cp_txp12_1
                      (Sig (PubK 1) (hf tx_proposal_field cp_txp12_1)).

Definition cp_txp12_2 : tx_proposal_field :=
  TxProposal cp_peer2_id
             (hf tx_field (TxField cp_cli_id cp_chaincode_id cp_upd_op2 (TS 2))) 
             cp_chaincode_id cp_upd_op2 cp_rset12 cp_wset12.

(* endorsement for transaction 2 in block 1 by peer 2 *)
Definition cp_ed12_2 : trans_endorsed_msg :=
  Trans_endorsed_msg cp_txp12_2
                     (Sig (PubK 2) (hf tx_proposal_field cp_txp12_2)). 

(* transaction 2 in block 1 *)
Definition cp_tx12 : transaction :=
  Trans cp_chaincode_id cp_upd_op2 (cp_rset12, cp_wset12) (cp_ed12_1 :: cp_ed12_2 :: nil). 

Definition cp_blk1 : block :=
  Blk
    (Blk_header 1
                (hf (list transaction) (cp_tx11 :: cp_tx12 :: nil))
                (hf (list transaction) nil)) 
    (cp_tx11 :: cp_tx12 :: nil)
    (true :: true :: nil).

Definition wsc :=
  mp_upd chaincode_id world_state beq_cc_id_dec (emp chaincode_id world_state)
         cp_chaincode_id cp_ws. 

Definition cp_txp21_1 : tx_proposal_field :=
  TxProposal cp_peer1_id
             (hf tx_field (TxField cp_cli_id cp_chaincode_id cp_dc_op1 (TS 3)))
             cp_chaincode_id cp_dc_op1 cp_rset21 cp_wset21. 

(* endorsement for transaction 1 in block 2 by peer 1 *)
Definition cp_ed21_1 : trans_endorsed_msg :=
   Trans_endorsed_msg cp_txp21_1
                      (Sig (PubK 1) (hf tx_proposal_field cp_txp21_1)).

Definition cp_txp21_2 : tx_proposal_field :=
  TxProposal cp_peer2_id
             (hf tx_field (TxField cp_cli_id cp_chaincode_id cp_dc_op1 (TS 3)))
             cp_chaincode_id cp_dc_op1 cp_rset21 cp_wset21. 

(* endorsement for transaction 2 in block 1 by peer 2 *)
Definition cp_ed21_2 : trans_endorsed_msg :=
  Trans_endorsed_msg cp_txp21_2
                     (Sig (PubK 2) (hf tx_proposal_field cp_txp21_2)). 

(* transaction 1 in block 2 -- not yet in the block in the beginning *)
Definition cp_tx21 : transaction :=
  Trans cp_chaincode_id cp_dc_op1 (cp_rset21, cp_wset21) (cp_ed21_1 :: cp_ed21_2 :: nil).


Definition cp_txp22_1 : tx_proposal_field :=
  TxProposal cp_peer1_id
             (hf tx_field (TxField cp_cli_id cp_chaincode_id cp_dc_op2 (TS 4)))
             cp_chaincode_id cp_dc_op2 cp_rset22 cp_wset22.

(* endorsement for transaction 2 in block 2 by peer 1 *)
Definition cp_ed22_1 : trans_endorsed_msg :=
   Trans_endorsed_msg cp_txp22_1
                      (Sig (PubK 1) (hf tx_proposal_field cp_txp22_1)).

Definition cp_txp22_2 : tx_proposal_field :=
  TxProposal cp_peer2_id
             (hf tx_field (TxField cp_cli_id cp_chaincode_id cp_dc_op2 (TS 4)))
             cp_chaincode_id cp_dc_op2 cp_rset22 cp_wset22.

(* endorsement for transaction 2 in block 2 by peer 2 *)
Definition cp_ed22_2 : trans_endorsed_msg :=
   Trans_endorsed_msg cp_txp22_2
                      (Sig (PubK 2) (hf tx_proposal_field cp_txp22_2)).

(* transaction 2 in block 2 -- not yet in the block in the beginning *)
Definition cp_tx22 : transaction :=
  Trans cp_chaincode_id cp_dc_op2 (cp_rset22, cp_wset22) (cp_ed22_1 :: cp_ed22_2 :: nil).

Definition cp_peer1 : peer_node :=
  {| peer_public_key := PubK 1;
     peer_ep_cc := cp_epcc;
     peer_ledger := (Ledger (BC (cp_blk1 :: nil)) wsc);
     peer_pmsgs := nil; 
     peer_interp_oper := cp_op_interp |}.

Definition cp_peer2 : peer_node :=
  {| peer_public_key := PubK 2; 
     peer_ep_cc := cp_epcc;
     peer_ledger := (Ledger (BC (cp_blk1 :: nil)) wsc); 
     peer_pmsgs := nil; 
     peer_interp_oper := cp_op_interp |}.

Definition cp_cli : client :=
  {| cli_timestamp := TS 4;
     cli_pending_proposals := nil;
     cli_received_eds := fun hs => nil 
  |}. 

Definition cp_os : ordering_service :=
  {| os_blk_size := 2;
     os_last_blk_num := 1; 
     os_last_blk_hash := (hf (list transaction) (cp_tx11 :: cp_tx12 :: nil)); 
     os_pending_trans := (cp_tx21 :: nil); 
     os_blks_created := (fun n => match n with 1 => Some cp_blk1 | _ => None end)
  |}.

Definition cp_blk2 : block :=
  Blk
    (Blk_header 2
                (hf (list transaction) (cp_tx21 :: cp_tx22 :: nil))
                (hf (list transaction) (cp_tx11 :: cp_tx12 :: nil))) 
    (cp_tx21 :: cp_tx22 :: nil)
    (true :: true :: nil).

Definition cp_ws' :=
  mp_upd key (prod val ver) beq_key_dec 
         (mp_upd key (prod val ver) beq_key_dec (emp key (prod val ver))
                 car1 (PrimVal 180, Ver 2))
         car2 (PrimVal 270, Ver 2). 
  
Definition wsc' :=
  mp_upd chaincode_id world_state beq_cc_id_dec (emp chaincode_id world_state)
         cp_chaincode_id cp_ws'. 

Definition cp_peer1' : peer_node :=
  {| peer_public_key := PubK 1; 
     peer_ep_cc := cp_epcc;
     peer_ledger := (Ledger (BC (cp_blk1 :: cp_blk2 :: nil)) wsc');
     peer_pmsgs := nil; 
     peer_interp_oper := cp_op_interp |}.

Definition cp_peer2' : peer_node :=
  {| peer_public_key := PubK 2;
     peer_ep_cc := cp_epcc;
     peer_ledger := (Ledger (BC (cp_blk1 :: cp_blk2 :: nil)) wsc');
     peer_pmsgs := nil;  
     peer_interp_oper := cp_op_interp |}.

Definition cp_cli' : client :=
  {| cli_timestamp := TS 5;
     cli_pending_proposals := nil;
     cli_received_eds := fun hs => nil 
  |}.

Definition cp_blk20 : block :=
  Blk
    (Blk_header 2
                (hf (list transaction) (cp_tx21 :: cp_tx22 :: nil))
                (hf (list transaction) (cp_tx11 :: cp_tx12 :: nil))) 
    (cp_tx21 :: cp_tx22 :: nil)
    (nil).

Definition cp_os' : ordering_service :=
  {| os_blk_size := 2;
     os_last_blk_num := 2; 
     os_last_blk_hash := (hf (list transaction) (cp_tx21 :: cp_tx22 :: nil)); 
     os_pending_trans := nil; 
     os_blks_created := (fun n => match n with
                                    1 => Some cp_blk1 
                                  | 2 => Some cp_blk20 
                                  | _ => None
                                  end)
  |}.

Definition multi_step (hf : hash_func) :=
  multi (fun conf conf' => (exists act, (step_rel_act hf act conf conf'))). 

Definition cp_clients :=
  mp_upd client_id client beq_cli_id_dec (emp client_id client) 
         cp_cli_id cp_cli.

Definition cp_peers :=
  mp_upd peer_id peer_node beq_peer_id_dec 
         (mp_upd peer_id peer_node beq_peer_id_dec (emp peer_id peer_node)
                 cp_peer1_id cp_peer1)
         cp_peer2_id cp_peer2.

Definition cp_clients' :=
    mp_upd client_id client beq_cli_id_dec (emp client_id client) 
           cp_cli_id cp_cli'.

Definition cp_peers' :=
  mp_upd peer_id peer_node beq_peer_id_dec 
         (mp_upd peer_id peer_node beq_peer_id_dec (emp peer_id peer_node)
                 cp_peer1_id cp_peer1')
         cp_peer2_id cp_peer2'.

Lemma cp_peers_1 : cp_peers cp_peer1_id = Some cp_peer1.
Proof.
  unfold cp_peers.
  rewrite mp_upd_neq. rewrite mp_upd_eq. auto. 
  intro H. inversion H.
Qed.

Lemma cp_peers_2 : cp_peers cp_peer2_id = Some cp_peer2.
Proof.
  unfold cp_peers.
  rewrite mp_upd_eq.
  auto.
Qed.

Lemma same_rwsets21 :
  same_rwsets_lst
    [Trans_endorsed_msg cp_txp21_1 (Sig (PubK 1) (hf tx_proposal_field cp_txp21_1));
       Trans_endorsed_msg cp_txp21_2 (Sig (PubK 2) (hf tx_proposal_field cp_txp21_2))]
    cp_rset21 cp_wset21. 
Proof.
  unfold same_rwsets_lst.
  intros.
  destruct i.
  simpl in H1.
  inversion H1; subst.
  simpl. split; auto.
  destruct i.
  simpl in H1.
  inversion H1; subst.
  simpl. split; auto.
  simpl in H0.
  assert (~(S (S i) < 2)) by lia. apply ex_falso_quodlibet. 
  apply H2. auto.
Qed.

Lemma same_rwsets22 :
  same_rwsets_lst
    [Trans_endorsed_msg cp_txp22_1 (Sig (PubK 1) (hf tx_proposal_field cp_txp22_1));
       Trans_endorsed_msg cp_txp22_2 (Sig (PubK 2) (hf tx_proposal_field cp_txp22_2))]
    cp_rset22 cp_wset22.
Proof.
  unfold same_rwsets_lst.
  intros.
  destruct i.
  simpl in H1.
  inversion H1; subst.
  simpl. split; auto.
  destruct i.
  simpl in H1.
  inversion H1; subst.
  simpl. split; auto.
  simpl in H0.
  assert (~(S (S i) < 2)) by lia. apply ex_falso_quodlibet. 
  apply H2. auto.
Qed.

Lemma blk_integrate :
  mp_upd nat block beq_nat_dec
         (fun n : nat => match n with | 1 => Some cp_blk1 | _ => None end) 2
         (Blk
            (Blk_header 2 (hf (list transaction) [cp_tx21; cp_tx22])
                        (hf (list transaction) [cp_tx11; cp_tx12]))
            [cp_tx21; cp_tx22] [])
  = (fun n => (
      match n with
        1 => Some cp_blk1
      | 2 => Some (Blk
                     (Blk_header 2 (hf (list transaction) [cp_tx21; cp_tx22])
                                 (hf (list transaction) [cp_tx11; cp_tx12]))
                     [cp_tx21; cp_tx22] [])
      | _ => None
      end)). 
Proof.
  unfold mp_upd.
  unfold func_upd.
  apply functional_extensionality. intro j.
  destruct (beq_nat_dec j 2); simpl. 
  rewrite e; simpl; auto.
  destruct j; auto. 
  destruct j; auto.
  assert (j > 0). lia.
  assert (exists j', j = S j').
  { destruct j. lia. exists j. auto. }
  inversion H0; subst.
  auto.
Qed.

Lemma trans_validate_res :
  trans_lst_validate [cp_tx21; cp_tx22]
    (fun ccid : chaincode_id =>
     match cp_epcc ccid with
     | Some (a, _) => Some a
     | None => None
     end) wsc wsc' [true; true].
Proof.
  eapply Trans_lst_val_inc with
      (ws' := mp_upd key (prod val ver) beq_key_dec 
                     (mp_upd key (prod val ver) beq_key_dec (emp key (prod val ver))
                             car1 (PrimVal 180, Ver 2))
                     car2 (PrimVal 300, Ver 1)).
  eauto.
  unfold cp_epcc. unfold cp_tx21; simpl.
  rewrite mp_upd_eq.
  auto.
  unfold cp_tx21; simpl.
  unfold wsc. rewrite mp_upd_eq. auto.
  
  (* first trans *)
  econstructor. 
  unfold cp_tx21. auto.
  unfold cp_ed21_1. unfold cp_ed21_2.
  apply same_rwsets21. 
  unfold cp_ed21_1. unfold cp_ed21_2.
  simpl. unfold cp_ep. simpl. auto.
  unfold cp_rset21; simpl. intros.
  destruct (beq_key_dec k car1).
  rewrite e. unfold cp_ws; simpl.
  rewrite mp_upd_neq. rewrite mp_upd_eq.
  rewrite e in H. rewrite mp_upd_eq in H.
  inverts H. exists (PrimVal 200). auto.
  discriminate. 
  rewrite mp_upd_neq in H. unfold emp in H; simpl in H.
  inversion H. auto.
  intros.
  destruct (beq_key_dec k car1). 
  right. left.
  repeat eexists.
  unfold cp_wset21. rewrite e. rewrite mp_upd_eq. auto.
  rewrite e. unfold cp_ws. rewrite mp_upd_neq. rewrite mp_upd_eq. auto.
  discriminate. 
  rewrite e. rewrite mp_upd_neq. rewrite mp_upd_eq. auto.
  discriminate. 
  left.
  destruct (beq_key_dec k car2).
  rewrite e. rewrite mp_upd_eq.
  split. unfold cp_wset21. rewrite mp_upd_neq. unfold emp. auto.
  discriminate. 
  unfold cp_ws. rewrite mp_upd_eq. auto.
  split.
  unfold cp_wset21. rewrite mp_upd_neq.
  unfold emp. auto. auto.
  rewrite mp_upd_neq. rewrite mp_upd_neq. unfold emp.
  unfold cp_ws. rewrite mp_upd_neq. rewrite mp_upd_neq.
  unfold emp. auto.
  auto. auto. auto. auto.

  eapply Trans_lst_val_inc with
      (ws' := mp_upd key (prod val ver) beq_key_dec 
                     (mp_upd key (prod val ver) beq_key_dec (emp key (prod val ver))
                             car1 (PrimVal 180, Ver 2))
                     car2 (PrimVal 270, Ver 2)).
  auto.
  unfold cp_tx22. simpl. unfold cp_epcc. rewrite mp_upd_eq.
  auto.
  unfold cp_tx22. simpl. rewrite mp_upd_eq. auto.

  (* second trans *)
  econstructor.
  unfold cp_tx22. auto.
  unfold cp_ed22_1. unfold cp_ed22_2.
  apply same_rwsets22.
  simpl. unfold cp_ep. auto.
  intros.
  destruct (beq_key_dec k car2).
  exists (PrimVal 300).
  rewrite e. 
  rewrite mp_upd_eq.
  rewrite e in H. unfold cp_rset22 in H. rewrite mp_upd_eq in H.
  inverts H. auto.
  unfold cp_rset22 in H. rewrite mp_upd_neq in H.
  unfold emp in H. inversion H. auto.
  intros.
  destruct (beq_key_dec k car2).
  right. left.
  repeat eexists.
  unfold cp_wset22. subst. rewrite mp_upd_eq. auto.
  subst. rewrite mp_upd_eq. auto.
  subst. rewrite mp_upd_eq. auto.
  left.
  destruct (beq_key_dec k car1).
  subst. rewrite mp_upd_neq. rewrite mp_upd_eq. unfold cp_wset22.
  rewrite mp_upd_neq. unfold emp.
  split. auto. rewrite mp_upd_neq. rewrite mp_upd_eq. auto.
  auto.
  auto.
  auto.
  unfold cp_wset22. repeat (rewrite mp_upd_neq; auto).
  
  (* finalization *)
  unfold cp_epcc. simpl. rewrite mp_upd_mp_upd_eq.
  fold cp_ws'. unfold wsc. rewrite mp_upd_mp_upd_eq. fold wsc'. 
  apply Trans_lst_val_empty. 
Qed.   

Theorem cp_trans_flow :
  multi_step hf
             (cp_clients, (cp_peers, cp_os))
             (cp_clients', (cp_peers', cp_os')).
Proof.
  unfold multi_step.
  remember
    (mp_upd client_id client beq_cli_id_dec cp_clients cp_cli_id
            (inc_cli_timestamp 
               (cli_add_pending_propose_msg
                  cp_cli
                  (ProposeMsg (TxField cp_cli_id cp_chaincode_id cp_dc_op2
                                       (cli_timestamp cp_cli)))))) as cp_clients1.
  remember
    (add_pmsg_for_peers
       (ProposeMsg (TxField cp_cli_id cp_chaincode_id cp_dc_op2
                            (cli_timestamp cp_cli)))
       cp_peers [cp_peer1_id; cp_peer2_id]) as cp_peers1.

  apply Multi_step with (y := (cp_clients1, (cp_peers1, cp_os))). 
  exists (Act_cli_prop cp_cli_id (cp_peer1_id :: cp_peer2_id :: nil)). 
  unfold step_rel_act.
  exists cp_clients. exists cp_peers. exists cp_os.
  exists cp_clients1. exists cp_peers1. exists cp_os. 

  split; auto. 
  split; auto. 

  econstructor.
  (* dig into the first step -- cli prop *)
  unfold cp_clients. rewrite mp_upd_eq. auto. 
  intro idx. intro H_idx_in_pid12.
  inversion H_idx_in_pid12. 
  exists cp_peer1. rewrite <- H. apply cp_peers_1.
  exists cp_peer2.
  inversion H. rewrite <- H0. apply cp_peers_2. 
  inversion H0. 
  auto.

  eauto.
  eauto.
  auto.
  
  (* simp of the clients after the first step *)
  unfold cli_add_pending_propose_msg in Heqcp_clients1.
  unfold cli_pending_proposals in Heqcp_clients1. simpl in Heqcp_clients1.
  unfold upd_cli_pending_proposals in Heqcp_clients1. simpl in Heqcp_clients1. 
  unfold inc_cli_timestamp in Heqcp_clients1. simpl in Heqcp_clients1. 

  (* simp of the peers after the first step *)
  unfold add_pmsg_for_peers in Heqcp_peers1.
  unfold fold_left in Heqcp_peers1.
  rewrite cp_peers_1 in *. simpl in Heqcp_peers1.
  unfold peer_add_trans_propose_msg in Heqcp_peers1.
  simpl in Heqcp_peers1.
  rewrite func_upd_neq in Heqcp_peers1; auto. 
  2: { intro H_neq; inversion H_neq. }
  rewrite cp_peers_2 in Heqcp_peers1.
  unfold cp_peer2 in Heqcp_peers1.
  simpl in Heqcp_peers1.
  unfold upd_peer_pmsgs in Heqcp_peers1; simpl in Heqcp_peers1.

  remember
    (mp_upd
       client_id client beq_cli_id_dec cp_clients1 cp_cli_id
       {| cli_timestamp := TS 5;
          cli_pending_proposals := [ProposeMsg
                                      (TxField cp_cli_id cp_chaincode_id
                                               cp_dc_op2 (TS 4))];
          cli_received_eds :=
            func_upd hash (list trans_endorsed_msg) beq_hash_dec (fun tid => [])
                     (hf tx_field
                         (TxField cp_cli_id cp_chaincode_id cp_dc_op2 (TS 4)))
                     [Trans_endorsed_msg
                       cp_txp22_1 (Sig (PubK 1) (hf tx_proposal_field cp_txp22_1))] 
       |}) as cp_clients2.

  remember
    (mp_upd peer_id peer_node beq_peer_id_dec cp_peers1 cp_peer1_id
            {| peer_public_key := PubK 1;
               peer_ep_cc := cp_epcc;
               peer_ledger := (Ledger (BC [cp_blk1]) wsc);
               peer_pmsgs := nil; 
               peer_interp_oper := cp_op_interp |})
    as cp_peers2.

  apply Multi_step with (y :=  (cp_clients2, (cp_peers2, cp_os))). 
  exists (Act_peer_resp cp_peer1_id cp_cli_id).
  unfold step_rel_act.
  exists cp_clients1. exists cp_peers1. exists cp_os.
  exists cp_clients2. exists cp_peers2. exists cp_os. 
  
  split; auto. 
  split; auto. 

  eapply Step_peer_resp with (pmsg_idx := 0). 
  rewrite Heqcp_peers1. rewrite func_upd_neq. rewrite func_upd_eq. auto.
  intro H_neq; inversion H_neq. 
  simpl. 
  auto.
  unfold peer_pmsgs. simpl. auto. 
  auto.
  auto. (* ?tid = ... *)
  unfold cp_epcc. simpl. 
  rewrite mp_upd_eq. auto. (* cp_epcc _ = Some (?ep, _) *)
  simpl. right. right. right. left. auto. 
  unfold wsc. rewrite mp_upd_eq. auto.
  unfold peer_interp_oper.
  unfold cp_op_interp.
  rewrite func_upd_eq. unfold cp_ws. rewrite mp_upd_eq. 
  auto. 
  auto. 
  simpl. auto. (* ?epsig *)
  auto.

  rewrite Heqcp_clients1. rewrite mp_upd_eq. eauto.
  simpl. fold cp_rset22. fold cp_wset22. fold cp_txp22_1.
  unfold cli_add_endorsed_msg. simpl.
  unfold upd_cli_received_eds. simpl. 
  eauto. (* ?clients *)
  unfold upd_peer_pmsgs. simpl. 
  eauto. (* ?peers *)
  eauto.

  (* simp of the clients map after the second step *)
  rewrite Heqcp_clients1 in Heqcp_clients2.
  rewrite mp_upd_mp_upd_eq in Heqcp_clients2.
  
  (* simp of the peers map after the second step *)
  rewrite Heqcp_peers1 in Heqcp_peers2. 
  rewrite func_upd_switch in Heqcp_peers2.
  2: { intro H_neq; inversion H_neq. }
  rewrite mp_upd_func_upd_eq in Heqcp_peers2.
  unfold mp_upd in Heqcp_peers2.
  rewrite func_upd_switch in Heqcp_peers2.
  2: { intro H_neq; inversion H_neq. }
  
  clear Heqcp_clients1; clear Heqcp_peers1.

  remember
    (mp_upd
       client_id client beq_cli_id_dec cp_clients2 cp_cli_id
       {| cli_timestamp := TS 5;
          cli_pending_proposals :=
            [ProposeMsg (TxField cp_cli_id cp_chaincode_id cp_dc_op2 (TS 4))];
          cli_received_eds :=
            func_upd hash (list trans_endorsed_msg) beq_hash_dec
                     (fun _ : hash => [])
                     (hf tx_field
                         (TxField cp_cli_id cp_chaincode_id cp_dc_op2 (TS 4)))
                     ([Trans_endorsed_msg
                         cp_txp22_1 (Sig (PubK 1) (hf tx_proposal_field cp_txp22_1))]
                        ++
                        [Trans_endorsed_msg
                           cp_txp22_2 (Sig (PubK 2) (hf tx_proposal_field cp_txp22_2))]
                        
                     )%list |})
    as cp_clients3.

  remember
    (mp_upd
       peer_id peer_node beq_peer_id_dec cp_peers2 cp_peer2_id
       {| peer_public_key := PubK 2;
          peer_ep_cc := cp_epcc;
          peer_ledger := (Ledger (BC [cp_blk1]) wsc);
          peer_pmsgs := nil;  
          peer_interp_oper := cp_op_interp |})
    as cp_peers3. 
  
  apply Multi_step with (y := (cp_clients3, (cp_peers3, cp_os))). 
  exists (Act_peer_resp cp_peer2_id cp_cli_id).

  unfold step_rel_act.
  exists cp_clients2. exists cp_peers2. exists cp_os.
  exists cp_clients3. exists cp_peers3. exists cp_os.
  
  split; auto. 
  split; auto. 

  (* look into the third step *)
  eapply Step_peer_resp with (pmsg_idx := 0). 
  rewrite Heqcp_peers2. rewrite func_upd_eq. auto. 
  simpl. auto. 
  unfold peer_pmsgs; simpl.
  auto. 
  auto. (* TxField ... *)
  auto. 
  unfold cp_epcc. apply mp_upd_eq.
  simpl. right. right. right. left. auto. (* List.In cp_dc_op [...] *)
  unfold wsc. rewrite mp_upd_eq. 
  auto.
  unfold peer_interp_oper. unfold cp_op_interp.
  rewrite func_upd_eq.
  unfold cp_ws. rewrite mp_upd_eq. auto. (* (?rset, ?wset) *)
  auto.
  auto. 
  auto.
  rewrite Heqcp_clients2. rewrite mp_upd_eq. auto.

  simpl. fold cp_rset22. fold cp_wset22. fold cp_txp22_2.
  unfold cli_add_endorsed_msg. simpl.
  unfold upd_cli_received_eds. simpl. 
  rewrite func_upd_eq. rewrite func_upd_func_upd_eq.
  auto. (* ?clients *)

  unfold upd_peer_pmsgs. simpl.
  auto.
  auto.

  (* simp of the clients map after the third step *)
  rewrite Heqcp_clients2 in Heqcp_clients3.
  rewrite mp_upd_mp_upd_eq in Heqcp_clients3.

  (* simp of the peers map after the third step *)
  rewrite Heqcp_peers2 in Heqcp_peers3.
  rewrite mp_upd_func_upd_eq in Heqcp_peers3.
  unfold mp_upd in Heqcp_peers3.

  clear Heqcp_clients2. clear Heqcp_peers2. 

  remember
    (mp_upd
       client_id client beq_cli_id_dec cp_clients3 cp_cli_id
       {| cli_timestamp := TS 5;
          cli_pending_proposals := [];
          cli_received_eds :=
            func_upd hash (list trans_endorsed_msg) beq_hash_dec
                     (fun _ : hash => [])
                     (hf tx_field
                         (TxField cp_cli_id cp_chaincode_id cp_dc_op2 (TS 4)))
                     [] |})
    as cp_clients4.

  remember
    ({| os_blk_size := 2;
        os_last_blk_num := 1; 
        os_last_blk_hash := (hf (list transaction) [cp_tx11; cp_tx12]);
        os_pending_trans :=
          ([cp_tx21]
             ++
             [Trans cp_chaincode_id cp_dc_op2 (cp_rset22, cp_wset22)
                    [Trans_endorsed_msg
                       cp_txp22_1 (Sig (PubK 1) (hf tx_proposal_field cp_txp22_1));
                     Trans_endorsed_msg
                       cp_txp22_2 (Sig (PubK 2) (hf tx_proposal_field cp_txp22_2))]])%list;
        os_blks_created := (fun n : nat => match n with
                                           | 1 => Some cp_blk1
                                           | _ => None
                                           end) |})
    as cp_os4. 
  
  apply Multi_step with (y := (cp_clients4, (cp_peers3, cp_os4))). 
  exists (Act_cli_send_trans cp_cli_id). 

  unfold step_rel_act.
  exists cp_clients3. exists cp_peers3. exists cp_os.
  exists cp_clients4. exists cp_peers3. exists cp_os4.
  
  split; auto. 
  split; auto. 

  (* look into the fourth step *)
  eapply Step_client_send_trans with (prop_idx := 0) (pn1_id := cp_peer1_id). 
  (* econstructor. *)
  rewrite Heqcp_clients3. rewrite mp_upd_eq. auto.
  rewrite Heqcp_peers3; simpl.
  rewrite func_upd_neq; auto. 
  rewrite func_upd_eq. eauto.
  discriminate.
  
  unfold upd_cli_pending_proposals. simpl. auto.
  unfold ccid_of_txfield. auto.
  unfold peer_ep_cc. unfold cp_epcc. rewrite mp_upd_eq. auto. 
  auto. auto. auto.
  unfold cp_ep. simpl.
  rewrite func_upd_eq. simpl. auto.
  
  simpl. rewrite func_upd_eq. 
  exists cp_rset22. exists cp_wset22.
  split. 
  apply same_rwsets22.
  auto. 

  simpl.
  auto.  (* ?cli_no_prop *)
  unfold client_clear_emsgs. simpl.
  unfold upd_cli_received_eds. simpl.
  rewrite func_upd_func_upd_eq. 
  auto. (* ?clients' *)
  auto. (* ?peers' *)
  unfold upd_os_pending_trans. simpl. 
  auto. (* ?os' *)

  rewrite Heqcp_clients3 in Heqcp_clients4. 
  simpl in Heqcp_clients4. rewrite mp_upd_mp_upd_eq in Heqcp_clients4.

  clear Heqcp_clients3.

  remember
    ({| os_blk_size := 2;
        os_last_blk_num := 2; 
        os_last_blk_hash := (hf (list transaction) [cp_tx21; cp_tx22]);
        os_pending_trans := nil; 
        os_blks_created :=
          (fun n : nat =>
             match n with
             | 1 => Some cp_blk1
             | 2 => Some
                      (Blk (Blk_header 2 (hf (list transaction) [cp_tx21; cp_tx22])
                                       (hf (list transaction) [cp_tx11; cp_tx12]))
                           [cp_tx21; cp_tx22] [])
             | _ => None
             end) |})
    as cp_os5.

  apply Multi_step with (y := (cp_clients4, (cp_peers3, cp_os5))). 
  exists (Act_ord_crt_blk). 
  unfold step_rel_act.

  exists cp_clients4. exists cp_peers3. exists cp_os4.
  exists cp_clients4. exists cp_peers3. exists cp_os5.
  
  split; auto. 
  split; auto. 

  (* look into the fifth step *)
  econstructor. 

  rewrite Heqcp_os4; simpl.
  auto. 
  simpl. rewrite Heqcp_os4. auto. 
  rewrite Heqcp_os4. simpl. auto.
  auto.
  rewrite Heqcp_os4. simpl. auto. 
  rewrite Heqcp_os4; simpl.
  auto.
  rewrite Heqcp_os4; simpl.
  auto.
  
  auto. (* ?clients' *)
  auto. 
  rewrite Heqcp_os4; simpl.
  unfold upd_os_pending_trans. simpl.
  auto.
  unfold inc_os_blk_num; simpl.
  unfold upd_os_last_blk_hash; simpl.
  unfold os_record_new_blk; simpl.
  unfold blk_no; simpl.
  unfold upd_os_blks_created; simpl.
  fold cp_ed22_1. fold cp_ed22_2.
  fold cp_tx22.
  rewrite blk_integrate. 
  auto. (* ?os' *)

  clear Heqcp_os4. 
  
  (* peer2 integrates the new block *)

  remember
    (mp_upd
       peer_id peer_node beq_peer_id_dec cp_peers3 cp_peer2_id
       {|
         peer_public_key := PubK 2;
         peer_ep_cc := cp_epcc;
         peer_ledger := (Ledger (BC [cp_blk1; cp_blk2]) wsc');
         peer_pmsgs := nil; 
         peer_interp_oper := cp_op_interp |})
    as cp_peers6. 

  eapply Multi_step with (y := (cp_clients4, (cp_peers6, cp_os5))). 
  exists (Act_peer_add_blk cp_peer2_id). 
  unfold step_rel_act.
  exists cp_clients4. exists cp_peers3. exists cp_os5.
  exists cp_clients4. exists cp_peers6. exists cp_os5.
  
  split; auto. 
  split; auto. 

  (* look into the sixth step *)
  eapply Step_peer_add_block with
      (new_blk :=
         (Blk (Blk_header 2
                          (hf (list transaction) [cp_tx21; cp_tx22])
                          (hf (list transaction) [cp_tx11; cp_tx12]))
              [cp_tx21; cp_tx22] [])) (wsc' := wsc') (flags := [true; true]). 
  rewrite Heqcp_peers3. rewrite func_upd_eq. auto.
  rewrite Heqcp_os5. unfold blk_no; simpl. auto. 
  auto. (* Blk ?new_hdr ?new_trans_lst ?new_valid_lst *)
  simpl. auto.
  split. intro H_len_blks_zero. inversion H_len_blks_zero. 
  intro H_len_gt_zero.
  intro last_blk. 
  intro H_last_blk_idx.
  simpl in H_last_blk_idx. 
  inversion H_last_blk_idx; subst.
  split; auto. 
  apply trans_validate_res.
  auto.
  auto.
  unfold peer_update_ledger. simpl.
  unfold upd_peer_ledger. simpl. 
  fold cp_blk2. auto. (* ?peers *)
  auto. (* ?os *) 

  (* simp of the peers after the sixth step *)
  rewrite Heqcp_peers3 in Heqcp_peers6.
  rewrite mp_upd_func_upd_eq in Heqcp_peers6.
  unfold mp_upd in Heqcp_peers6.
  clear Heqcp_peers3.

  (* peer1 integrates the new block *)

  remember
    (mp_upd
       peer_id peer_node beq_peer_id_dec cp_peers6 cp_peer1_id
       {|
         peer_public_key := PubK 1;
         peer_ep_cc := cp_epcc;
         peer_ledger := (Ledger (BC [cp_blk1; cp_blk2]) wsc');
         peer_pmsgs := nil;  
         peer_interp_oper := cp_op_interp |})
    as cp_peers7.   

  eapply Multi_step with (y := (cp_clients4, (cp_peers7, cp_os5))). 
  exists (Act_peer_add_blk cp_peer1_id). 
  unfold step_rel_act.
  exists cp_clients4. exists cp_peers6. exists cp_os5.
  exists cp_clients4. exists cp_peers7. exists cp_os5.
  
  split; auto. 
  split; auto. 

  (* look into the seventh step *)
  eapply Step_peer_add_block with
      (new_blk :=
         (Blk (Blk_header 2
                          (hf (list transaction) [cp_tx21; cp_tx22])
                          (hf (list transaction) [cp_tx11; cp_tx12]))
              [cp_tx21; cp_tx22] [])) (wsc' := wsc') (flags := [true; true]).
  rewrite Heqcp_peers6. rewrite func_upd_neq.
  rewrite func_upd_eq. auto.
  discriminate.
  rewrite Heqcp_os5. simpl. auto. 
  auto.
  simpl. auto.
  split. intro H_len_blks_zero. inversion H_len_blks_zero.
  intro H_len_gt_zero.
  intro H_last_blk. 
  intro H_last_blk_idx.
  simpl in H_last_blk_idx. 
  inversion H_last_blk_idx; subst.
  split; auto. 
  apply trans_validate_res.
  auto.
  auto. (* ?clients *)
  auto.
  auto.

  rewrite Heqcp_peers6 in Heqcp_peers7.
  rewrite func_upd_switch in Heqcp_peers7.
  2:{ intro H_neq; inversion H_neq. }
  rewrite mp_upd_func_upd_eq in Heqcp_peers7.
  unfold mp_upd in Heqcp_peers7.
  rewrite func_upd_switch in Heqcp_peers7.
  2:{ intro H_neq; inversion H_neq. }
  clear Heqcp_peers6.
  
  fold cp_peer1' in Heqcp_peers7.
  fold cp_peer2' in Heqcp_peers7.
  asserts_rewrite  (cp_peers7 = cp_peers').
  {
    rewrite Heqcp_peers7. unfold cp_peers'. unfold mp_upd.
    unfold emp. unfold cp_peers.
    repeat unfold mp_upd. 
    rewrite func_upd_switch. rewrite func_upd_func_upd_eq.
    rewrite func_upd_switch. rewrite func_upd_func_upd_eq.
    auto.
    discriminate. discriminate. 
  }
  clear Heqcp_peers7.
  
  asserts_rewrite (
      func_upd hash (list trans_endorsed_msg) beq_hash_dec
               (fun _ : hash => [])
               (hf tx_field
                   (TxField cp_cli_id cp_chaincode_id cp_dc_op2 (TS 4))) []
      = fun hs => nil) in Heqcp_clients4.
  {
    apply functional_extensionality.
    intro hs.
    unfold func_upd.
    destruct
      (beq_hash_dec
         hs (hf tx_field (TxField cp_cli_id cp_chaincode_id cp_dc_op2 (TS 4))));
      auto. 
  }
  fold cp_cli' in Heqcp_clients4.
  asserts_rewrite (cp_clients4 = cp_clients').
  {
    unfold cp_clients'.
    rewrite Heqcp_clients4.
    unfold cp_clients. rewrite mp_upd_mp_upd_eq. auto. 
  }
  clear Heqcp_clients4. 

  fold cp_blk1 in Heqcp_os5.
  fold cp_blk20 in Heqcp_os5.
  asserts_rewrite (cp_os5 = cp_os').
  {
    unfold cp_os'; auto. 
  }

  apply Multi_refl.

Qed.

  

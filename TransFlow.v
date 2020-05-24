
(* Formalization of Hyperledger Fabric transaction flow as a transition system *) 

Require Import Entities.
Require Import List.
Require Import MyUtils. 
  
Inductive same_val : val -> val -> Prop :=
  Same_PrimVal :
    forall (n : nat), same_val (PrimVal n) (PrimVal n) | 
  Same_CompVal :
    forall mp1 mp2, mp1 = mp2 -> same_val (CompVal mp1) (CompVal mp2). 
       
Definition peer_add_trans_propose_msg 
           (pn : peer_node) (pmsg : trans_propose_msg) : peer_node
  := upd_peer_pmsgs pn (pn.(peer_pmsgs) ++ (pmsg :: nil)).

Definition cli_add_pending_propose_msg
           (cli : client) (pmsg : trans_propose_msg) : client 
  :=
    upd_cli_pending_proposals cli
                              (cli.(cli_pending_proposals) ++ (pmsg :: nil)).

Definition add_pmsg_for_peers
           (pmsg : trans_propose_msg) (peer_mp : mp_tp peer_id peer_node)
           (pn_ids : list peer_id) 
  : mp_tp peer_id peer_node := 
  fold_left
    (fun cur_peers idx =>
       func_upd peer_id (option peer_node) beq_peer_id_dec cur_peers idx
                (match cur_peers idx with
                   Some pr =>
                   Some (peer_add_trans_propose_msg pr pmsg)
                 | None => None
                 end))
    pn_ids peer_mp.

Definition cli_add_endorsed_msg cli emsg tid :=
  upd_cli_received_eds
    cli (func_upd hash (list trans_endorsed_msg) beq_hash_dec cli.(cli_received_eds)
                  tid (cli.(cli_received_eds) tid ++ (emsg :: nil))). 

Definition rset_of_emsg emsg : read_set :=
  match emsg with
    Trans_endorsed_msg (TxProposal _ _ _ _ rs _) _ => rs
  end. 

Definition wset_of_emsg emsg : write_set :=
  match emsg with
    Trans_endorsed_msg (TxProposal _ _ _ _ _ ws) _ => ws 
  end.

Definition same_rwsets_lst
           (emsgs : list trans_endorsed_msg) rs ws : Prop :=
  forall i emsg,
    0 <= i -> i < length emsgs ->
    nth_error emsgs i = Some emsg ->
    (rset_of_emsg emsg = rs /\ wset_of_emsg emsg = ws). 

Definition client_clear_emsgs (cli : client) (tid : hash) : client :=
  upd_cli_received_eds
    cli
    (func_upd hash (list trans_endorsed_msg) beq_hash_dec cli.(cli_received_eds)
              tid nil).

Definition ccid_of_txfield tx : chaincode_id :=
  match tx with TxField _ cc_id _ _ => cc_id end. 

Definition oper_of_txfield tx : operation :=
  match tx with TxField _ _ op _ => op end.

Definition os_record_new_blk os blk :=
  upd_os_blks_created os 
    match os.(os_blks_created) with
      blks_mp => mp_upd nat block beq_nat_dec blks_mp (blk_no blk) blk
    end.

(* update the ledger by appending the new block blk 
   and updating the world states for chaincodes by wsc *) 
Definition peer_update_ledger
           pn blk (wsc : chaincode_id -> option world_state) : peer_node
  := upd_peer_ledger 
       pn
       (match pn.(peer_ledger) with 
          (Ledger (BC blks) _) =>
          (Ledger (BC (blks ++ (blk :: nil))) wsc)
        end). 

(* processing of a single transaction that updates the world state 
   and generates a validity flag *) 
Inductive trans_validate : 
  transaction -> endorsement_pol -> world_state -> world_state -> bool -> Prop :=
  
  Trans_valid : 
    forall trans cc_id op ed_pol rset wset ws emsgs ws',
      trans = Trans cc_id op (rset, wset) emsgs ->
      (* the endorsements contain the same read and write sets *)
      same_rwsets_lst emsgs rset wset -> 
      (* the endorsement policy is satisfied *) 
      ed_pol
        (map (fun emsg => match emsg with Trans_endorsed_msg _ sig => sig end) emsgs)
      = true -> 
      (* the versions for key according to the read set agree with those 
         according to the world state *) 
      (forall k vr, rset k = Some vr -> (exists vl, ws k = Some (vl, vr))) ->
      (* update the world state ws to ws' *)
      (forall k, (wset k = None /\ ws' k = ws k) \/
                 (exists vl vl' vr, (wset k = Some (Val_or_del1 vl') /\
                                     ws k = Some (vl, Ver vr) /\
                                     ws' k = Some (vl', Ver (S vr)))) \/
                 (exists vl vr, (wset k = Some Val_or_del2 /\
                                 ws k = Some (vl, Ver vr) /\
                                 ws' k = None))) ->  
      trans_validate trans ed_pol ws ws' true |
  
  Trans_invalid :
    forall trans cc_id op ed_pol rset wset ws emsgs,
      trans = Trans cc_id op (rset, wset) emsgs -> 
      (~same_rwsets_lst emsgs rset wset \/
       ed_pol
         (map (fun emsg => match emsg with Trans_endorsed_msg _ sig => sig end) emsgs)
         = false \/
       (exists k vr, rset k = Some vr /\ (forall vl, ws k <> Some (vl, vr))) 
      ) ->
      trans_validate trans ed_pol ws ws false.


(* processing of a list of transactions that 
   updates the world states for the chaincodes and 
   generates a list of validity flags for the processed transactions *)    
Inductive trans_lst_validate :
  list transaction ->
  (mp_tp chaincode_id endorsement_pol) ->
  (mp_tp chaincode_id world_state) -> 
  (mp_tp chaincode_id world_state) ->  
  list bool -> Prop :=
  Trans_lst_val_empty :
    forall ep_mp wsc, 
      trans_lst_validate nil ep_mp wsc wsc nil |
  Trans_lst_val_inc :
    forall ep_mp wsc wsc' flg flgs tx txs ws ws' cc_id ed_pol,
      cc_id = tx_ccid tx ->
      ep_mp cc_id = Some ed_pol ->
      wsc cc_id = Some ws -> 
      trans_validate tx ed_pol ws ws' flg -> 
      trans_lst_validate
        txs ep_mp
        (mp_upd chaincode_id world_state beq_cc_id_dec wsc cc_id ws') wsc' flgs ->
      trans_lst_validate (tx :: txs) ep_mp wsc wsc' (flg :: flgs). 

Inductive action : Type :=
  Act_cli_prop: client_id -> list peer_id -> action |
  Act_peer_resp: peer_id -> client_id -> action |
  Act_peer_drop_prop: peer_id -> action |
  Act_cli_send_trans: client_id -> action |
  Act_cli_drop_prop: client_id -> action |
  Act_ord_crt_blk: action |
  Act_peer_add_blk: peer_id -> action.  

Inductive step
          (h : hash_func) 
          (clients : mp_tp client_id client) (peers : mp_tp peer_id peer_node) 
          (os : ordering_service) 
          (clients' : mp_tp client_id client) (peers' : mp_tp peer_id peer_node)
          (os' : ordering_service)
  : action -> Prop :=
  
  (* a client sends a transaction proposal to a number of peers *)
  Step_cli_prop :
    forall cli_id cli (target_pn_idxs : list peer_id) ccode_id pmsg
           (op : operation),
      (* the client is on the channel for the transaction proposal *) 
      clients cli_id = Some cli ->
      (* target_pn_idxs contains the indicies of a subset of peers 
         on the channel identified by ch_id *)
      (forall idx, List.In idx target_pn_idxs -> (exists p, (peers idx = Some p))) -> 
      (* build the transaction proposal message pmsg *) 
      pmsg = ProposeMsg (TxField cli_id ccode_id op (cli.(cli_timestamp))) ->
      (* add pmsg to the pending transaction proposals for the client cli *) 
      clients' = mp_upd client_id client beq_cli_id_dec clients cli_id 
                        (inc_cli_timestamp (cli_add_pending_propose_msg cli pmsg)) -> 
      (* add pmsg to the pending trans proposals for all peers with indices in 
         target_pn_idxs *) 
      peers' = add_pmsg_for_peers pmsg peers target_pn_idxs -> 
      os' = os ->
      step h clients peers os clients' peers' os'
           (Act_cli_prop cli_id target_pn_idxs) |  
  
  (* a peer sends a transaction proposal response to the client 
     with the corresponding proposal *) 
  Step_peer_resp :
    forall peer_id cli_id emsg (tid : hash) epsig pn pmsg_idx
           tx ccode_id ts prop rset wset cli bc wsmp ws op ep op_lst,
      (* peer pn has "ProposeMsg tx" from client cli_id for channel chan_id *) 
      peers peer_id = Some pn ->
      pn.(peer_ledger) = Ledger bc wsmp ->
      (* select a transaction proposal in the pending list to be processed *) 
      nth_error pn.(peer_pmsgs) pmsg_idx = Some (ProposeMsg tx) -> 
      tx = TxField cli_id ccode_id op ts ->
      (* create hash tid of the transaction proposal 
         as a unique identifier of the proposal *)
      tid = h tx_field tx ->
      (* the operation invoked exists (in a smart contract) on the channel *)
      (pn.(peer_ep_cc)) ccode_id = Some (ep, Chaincode op_lst) -> 
      List.In op op_lst -> 
      (* evaluate the operation invoked to generate the rwset *) 
      wsmp ccode_id = Some ws ->
      (rset, wset) = pn.(peer_interp_oper) op ws -> 
      prop = TxProposal peer_id tid ccode_id op rset wset ->
      (* create endorsement *)
      epsig = Sig (pn.(peer_public_key)) (h tx_proposal_field prop) -> 
      emsg = Trans_endorsed_msg prop epsig -> 
      clients cli_id = Some cli ->
      (* add endorsement to the originating client for the transaction with hash tid *)
      clients' = mp_upd client_id client beq_cli_id_dec clients cli_id
                        (cli_add_endorsed_msg cli emsg tid) -> 
      (* remove the transaction proposal that has been handled from the peer *) 
      peers' = mp_upd (Entities.peer_id) peer_node beq_peer_id_dec peers peer_id
                      (upd_peer_pmsgs
                         pn
                         ((firstn pmsg_idx pn.(peer_pmsgs))
                            ++ (skipn (S pmsg_idx) pn.(peer_pmsgs)))) -> 
      os' = os -> 
      step h clients peers os clients' peers' os' (Act_peer_resp peer_id cli_id) | 

  (* a peer drops the proposal because it is unable to endorse it *) 
  Step_peer_drop_prop :
    forall peer_id pn pmsg pmsg_idx,
      peers peer_id = Some pn ->
      nth_error pn.(peer_pmsgs) pmsg_idx = Some pmsg ->
      peers' = mp_upd Entities.peer_id peer_node beq_peer_id_dec peers peer_id
                      (upd_peer_pmsgs
                         pn
                         ((firstn pmsg_idx pn.(peer_pmsgs))
                            ++ (skipn (S pmsg_idx) pn.(peer_pmsgs)))) -> 
      clients' = clients ->
      os' = os -> 
      step h clients peers os clients' peers' os' (Act_peer_drop_prop peer_id) | 

  (* a client sends a transaction to the ordering service after having collected 
     sufficient endorsements on a transaction proposal *)  
  Step_client_send_trans :
    forall cli_id cli pn1_id pn1 ed_pol ccode ccode_id prop_idx tx tid
           emsgs epsigs cli_no_prop trans, 
      clients cli_id = Some cli ->
      peers pn1_id = Some pn1 -> 
      (* the transaction proposal on which endorsement is checked is ProposeMsg tx *)
      nth_error cli.(cli_pending_proposals) prop_idx = Some (ProposeMsg tx) -> 
      (* the chaincode id of tx is ccode_id *) 
      ccid_of_txfield tx = ccode_id ->
      (* the endorsement policy of the chaincode is ed_pol *)
      (pn1.(peer_ep_cc)) ccode_id = Some (ed_pol, ccode) ->
      (* the transaction identifier obtained by hashing tx is tid *)
      h tx_field tx = tid -> 
      cli.(cli_received_eds) tid = emsgs ->          
      (* obtain the list of signatures on the endorsement messages and 
         verify the endorsement policy using the chan     nel config and the signatures *)
      epsigs = map (fun emsg => match emsg with Trans_endorsed_msg _ sig => sig end)
                   emsgs ->
      ed_pol epsigs = true ->
      (exists rs ws, 
          (* the currently received endorsements on the transaction proposal 
             have the same readsets and writesets *)  
          same_rwsets_lst emsgs rs ws /\
          (* form the transaction *) 
          trans = Trans ccode_id (oper_of_txfield tx) (rs, ws) emsgs 
      ) ->
      (* update the client by inc the timestamp, removing the transaction proposal 
         already handled, and clearing the list of endorsements for that proposal *)
      cli_no_prop = upd_cli_pending_proposals cli
                      (firstn prop_idx cli.(cli_pending_proposals) ++
                       skipn (prop_idx + 1) cli.(cli_pending_proposals)) -> 
      clients' = mp_upd client_id client beq_cli_id_dec clients cli_id
                        (client_clear_emsgs cli_no_prop tid) -> 
      peers' = peers ->
      (* send the transaction to the ordering service *)
      os' = upd_os_pending_trans os (os.(os_pending_trans) ++ (trans :: nil)) -> 
      step h clients peers os clients' peers' os' (Act_cli_send_trans cli_id) | 

  (* a client drops a transaction proposal *) 
  Step_client_drop_prop : 
    forall cli_id cli prop_idx tx tid cli_no_prop, 
      clients cli_id = Some cli ->
      (* the transaction proposal on which endorsement is checked is ProposeMsg tx *)
      nth_error cli.(cli_pending_proposals) prop_idx = Some (ProposeMsg tx) ->
      h tx_field tx = tid ->
      cli_no_prop = upd_cli_pending_proposals cli
                      (firstn prop_idx cli.(cli_pending_proposals) ++
                       skipn (prop_idx+1) cli.(cli_pending_proposals)) ->
      clients' = mp_upd client_id client beq_cli_id_dec clients cli_id
                        (client_clear_emsgs cli_no_prop tid) -> 
      peers' = peers ->
      os' = os ->  
      step h clients peers os clients' peers' os' (Act_cli_drop_prop cli_id) |  

  (* the ordering service creates a new block for a channel *)
  Step_orderers_create_blk :
    forall blk ord_trans hdr cur_blk_hash os'' last_blk_no,
      ord_trans = os.(os_pending_trans) ->
      (* there are enough pending transactions to be grouped into a block *) 
      length ord_trans >= os.(os_blk_size) ->
      (* collect the transactions and compute the hash for the new block *)
      cur_blk_hash = (h (list transaction) (firstn os.(os_blk_size) ord_trans)) ->
      os.(os_last_blk_num) = last_blk_no ->
      os.(os_blks_created) (S last_blk_no) = None ->
      (* construct the header of the new block *)
      hdr = Blk_header (S last_blk_no) cur_blk_hash (os.(os_last_blk_hash)) ->
      (* construct the new block *) 
      blk = Blk hdr (firstn os.(os_blk_size) ord_trans) nil -> 
      clients' = clients ->
      peers' = peers -> 
      (* remove the transactions that have been assembled in a block 
         from the list of pending transactions *)
      os'' = upd_os_pending_trans os (skipn os.(os_blk_size) ord_trans) -> 
      (* update the sequence number and hash of the last block as recorded 
         in the orderers, and add the new block into the list of newly created blocks *)
      os' = os_record_new_blk 
              (upd_os_last_blk_hash (inc_os_blk_num os'') cur_blk_hash) blk -> 
      step h clients peers os clients' peers' os' (Act_ord_crt_blk) | 

  (* a peer validate a block and each transaction in the block, and
     add the validated block to the ledger *) 
  Step_peer_add_block :
    forall peer_id pn new_blk new_hdr new_trans_lst new_valid_lst
           blks wsc wsc' flags new_blk', 
      peers peer_id = Some pn ->
      (* new_blk is a pending block for validation *)  
      (os.(os_blks_created)) (blk_no new_blk) = Some new_blk ->
      new_blk = Blk new_hdr new_trans_lst new_valid_lst -> 
      (* blks is the list of blocks in the current blockchain in pn for chan_id *)
      pn.(peer_ledger) = Ledger (BC blks) wsc ->
      ((length blks = 0 -> blk_no new_blk = 0) 
       /\
       (length blks > 0 ->
        forall last_blk,
          (* last_blk is currently the last block in the blockchain *) 
          (nth_error blks ((length blks) - 1) = Some last_blk ->
           (* the new block has matching header information to the current last block *)
           (blk_no new_blk = S (blk_no last_blk) /\ 
            blk_prev_hash new_blk = blk_hash last_blk)))
      ) ->
      (* the individual transactions in the new block are validated, 
         with the validity flags set, and 
         the world states for chaincodes updated correspodingly *)
      trans_lst_validate
        new_trans_lst
        (fun ccid => match (pn.(peer_ep_cc) ccid) with
                       Some (a, b) => Some a | _ => None end)
        wsc wsc' flags -> 
      (* update the validity flags of the new block to be appended to the ledger *)
      new_blk' = Blk new_hdr new_trans_lst flags ->
      clients' = clients -> 
      peers' = mp_upd Entities.peer_id peer_node beq_peer_id_dec peers peer_id
                      (peer_update_ledger pn new_blk' wsc') -> 
      os' = os -> 
      step h clients peers os clients' peers' os' (Act_peer_add_blk peer_id). 

Hint Constructors step.

Require Import SfLib. 

Tactic Notation "step_cases" tactic(first) ident(c) := 
  first;
  [ Case_aux c "STEP_CLI_PROP" | Case_aux c "STEP_PEER_RESPONSE" |
    Case_aux c "STEP_PEER_DROP" | Case_aux c "STEP_CLI_TRANS" | 
    Case_aux c "STEP_CLI_DROP" | Case_aux c "STEP_ORD_BLK" |
    Case_aux c "STEP_PEER_BLK"  
  ].

Definition config := prod (mp_tp client_id client)
                          (prod (mp_tp peer_id peer_node) ordering_service).

Definition step_rel_act (hf : hash_func) : action -> config -> config -> Prop :=
  fun act (conf conf' : config) => (
      exists clients peers os clients' peers' os', 
        conf = (clients, (peers, os)) /\
        conf' = (clients', (peers', os')) /\
        step hf clients peers os clients' peers' os' act
    ). 


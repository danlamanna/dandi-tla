---------------------- MODULE asset_lifecycle ----------------------
(*
This models the lifecycle of assets throughout the system.

This is up to date with DANDI as of 4aaac16e6.
*)
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS ASSETS, NUM_ACTORS, NULL, MAX_ADDS, MAX_REMOVES

ASSUME Cardinality(ASSETS) > 0
ASSUME NUM_ACTORS > 0
ASSUME MAX_ADDS > 0
ASSUME MAX_REMOVES > 0
ASSUME MAX_ADDS > MAX_REMOVES \* has to be more otherwise things wouldn't finalize

VARIABLES
    pc,
    db_assets,
    loaded_asset,
    validate_queue,
    version_status,
    bounded_actions

AssetStates == {"none", "pending", "valid", "invalid"}
--------------------------------------------------------------
vars == <<pc, db_assets, bounded_actions, loaded_asset, validate_queue, version_status>>
---------------------------------------------------------------

RECURSIVE SeqFromSet(_)
SeqFromSet(S) ==
  IF S = {} THEN << >>
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  << x >> \o SeqFromSet(S \ {x})

AssetChangesIncreaseRevision(asset) ==
    /\ asset.status # asset'.status => asset'.rev = asset.rev + 1

RevisionFieldIsMonotonicallyIncreasing(record) ==
    /\ record'.rev = record.rev \/ record'.rev = record.rev + 1

TypeInvariant ==
    /\ \A aid \in ASSETS:
        /\ db_assets[aid].status \in AssetStates
        /\ db_assets[aid].rev \in Nat
        /\ db_assets[aid].rev >= 0

AssetStateTransitions == [][
    \A aid \in ASSETS:
        /\ RevisionFieldIsMonotonicallyIncreasing(db_assets[aid])
        /\ AssetChangesIncreaseRevision(db_assets[aid])

        /\ db_assets[aid].status = "none" => db_assets[aid]'.status \in {"none", "pending"}
        /\ db_assets[aid].status = "pending" => db_assets[aid]'.status \in {"pending", "invalid", "valid", "none"}
        /\ db_assets[aid].status = "valid" => db_assets[aid]'.status \in {"valid", "invalid"}
        /\ db_assets[aid].status = "invalid" => db_assets[aid]'.status \in {"invalid", "valid"}
]_db_assets

AssetsProcessed == \A aid \in ASSETS:
                       db_assets[aid].status = "pending" ~> db_assets[aid].status \in {"invalid", "valid"}
------------------------------------------------------------------

AddAssetToVersion(t, aid) ==
    /\ pc[t] = ""
    /\ db_assets[aid].status = "none"
    /\ bounded_actions.adds > 0
    /\ db_assets' = [db_assets EXCEPT ![aid]["status"] = "pending",
                                      ![aid]["rev"] = @ + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT !.adds = @ - 1]
    /\ UNCHANGED <<validate_queue, pc, loaded_asset, version_status>>



RemoveAssetFromVersion(t, aid) ==
    /\ pc[t] = ""
    /\ db_assets[aid].status # "none"
    /\ bounded_actions.removes > 0
    /\ db_assets' = [db_assets EXCEPT ![aid]["status"] = "none",
                                      ![aid]["rev"] = @ + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT !.removes = @ - 1]
    /\ UNCHANGED <<validate_queue, pc, loaded_asset, version_status>>

\* I don't think ChangeAsset is needed since it's effectively just a stutter step

LoadAssetForValidation(t) ==
    LET
        message == Head(validate_queue)
        asset == db_assets[message]
        status == db_assets[message].status
    IN
    /\ pc[t] = ""
    /\ Len(validate_queue) > 0
    \* if status is pending, then we can load it, otherwise the task gets no-oped
    /\ loaded_asset' = [loaded_asset EXCEPT ![t] = IF status = "pending" THEN asset ELSE NULL]
    /\ validate_queue' = Tail(validate_queue)
    /\ pc' = [pc EXCEPT ![t] = IF status = "pending" THEN "LoadAssetForValidation" ELSE ""]
    /\ UNCHANGED <<bounded_actions, db_assets, version_status>>

ValidateAssetMetadata(t) ==
    LET
        asset == loaded_asset[t]
    IN
    /\ pc[t] = "LoadAssetForValidation"
    /\ db_assets[asset.id].status = "pending" \* optimistic locking
    \* this is awkward and enforces optimistic locking in an even stricter way than we do.
    \* otherwise the same asset can be removed and re-added in between the two steps, violating
    \* the invariant that ensures that the rev is monotonically increasing.
    /\ db_assets[asset.id].rev = asset.rev
    /\ \/ db_assets' = [db_assets EXCEPT ![asset.id]["status"] = "valid",
                                         ![asset.id]["rev"] = asset.rev + 1]
       \/ db_assets' = [db_assets EXCEPT ![asset.id]["status"] = "invalid",
                                         ![asset.id]["rev"] = asset.rev + 1]
    /\ pc' = [pc EXCEPT ![t] = ""]
    /\ loaded_asset' = [loaded_asset EXCEPT ![t] = NULL]
    /\ UNCHANGED <<version_status, validate_queue, bounded_actions>>

ValidateAssetMetadataCron ==
    /\ Len(validate_queue) < 50  \* bound to prevent infinite growth
    /\ LET pending_assets == {a \in DOMAIN db_assets: db_assets[a].status = "pending"}
       IN validate_queue' = validate_queue \o SeqFromSet(pending_assets)
    /\ UNCHANGED <<loaded_asset, db_assets, version_status, bounded_actions, pc>>

---------------------------------------------------------------------------------
Init == /\ pc = [t \in 1..NUM_ACTORS |-> ""]
        /\ loaded_asset = [t \in 1..NUM_ACTORS |-> NULL]
        /\ bounded_actions = [adds |-> MAX_ADDS, removes |-> MAX_REMOVES]
        /\ db_assets = [aid \in ASSETS |-> [status |-> "none",
                                            rev |-> 0,
                                            id |-> aid]]
        /\ validate_queue = <<>>
	/\ version_status = "pending"


Next == \/ \E t \in 1..NUM_ACTORS:
              \/ ValidateAssetMetadataCron
              \/ \E aid \in ASSETS:
                    \/ AddAssetToVersion(t, aid)
                    (* modeling removes makes verifying stuckness difficult *)
                    \*\/ RemoveAssetFromVersion(t, aid)
              \/ LoadAssetForValidation(t)
              \/ ValidateAssetMetadata(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=====================================================

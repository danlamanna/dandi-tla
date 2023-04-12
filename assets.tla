---------------------- MODULE assets ----------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS ASSETS, NUM_ACTORS, NULL

ASSUME Cardinality(ASSETS) > 0
ASSUME NUM_ACTORS > 0

VARIABLES
    pc,
    db_assets,
    loaded_asset,
    validate_queue,
    \* keep the model running in a reasonable time
    bounded_actions

AssetStates == {"none", "pending", "valid", "invalid"}
--------------------------------------------------------------
vars == <<pc, db_assets, bounded_actions, loaded_asset, validate_queue>>
---------------------------------------------------------------
AssetChangesIncreaseRevision(asset) ==
    /\ (\/ asset.status # asset'.status
        \/ asset.sha256 # asset'.sha256) => asset'.rev = asset.rev + 1

RevisionFieldIsMonotonicallyIncreasing(record) ==
    /\ record'.rev = record.rev \/ record'.rev = record.rev + 1

TypeInvariant ==
    /\ \A aid \in ASSETS:
        /\ db_assets[aid].status \in AssetStates
        /\ db_assets[aid].rev \in Nat
        /\ db_assets[aid].rev >= 0
    /\ \A t \in DOMAIN bounded_actions:
          \A b \in DOMAIN bounded_actions[t]:
            /\ bounded_actions[t][b] \in Nat
            /\ bounded_actions[t][b] >= 0

AssetStateTransitions == [][
    \A aid \in ASSETS:
        /\ RevisionFieldIsMonotonicallyIncreasing(db_assets[aid])
        /\ AssetChangesIncreaseRevision(db_assets[aid])

        /\ db_assets[aid].status = "none" => db_assets[aid]'.status \in {"none", "pending"}
        /\ db_assets[aid].status = "pending" => db_assets[aid]'.status \in {"pending", "invalid", "valid"}
        /\ db_assets[aid].status = "valid" => db_assets[aid]'.status \in {"valid", "invalid"}
        /\ db_assets[aid].status = "invalid" => db_assets[aid]'.status \in {"invalid", "valid"}
]_db_assets

AssetsProcessed == <>[](\A aid \in DOMAIN db_assets:
                            db_assets[aid].status \in {"invalid", "valid"})
------------------------------------------------------------------

LoadAsset(t, aid) ==
    /\ pc[t] = ""
    /\ loaded_asset[t] = NULL
    /\ db_assets[aid].status # "none"
    /\ loaded_asset' = [loaded_asset EXCEPT ![t] = <<aid, db_assets[aid]>>]
    /\ UNCHANGED <<pc, db_assets, bounded_actions, validate_queue>>

AddAssetToVersion(t, aid) ==
    /\ pc[t] = ""
    /\ db_assets[aid].status = "none"
    /\ db_assets' = [db_assets EXCEPT ![aid]["status"] = "pending",
                                      ![aid]["rev"] = @ + 1]
    /\ loaded_asset' = [loaded_asset EXCEPT ![t] = <<aid, db_assets'[aid]>>]
    /\ UNCHANGED <<bounded_actions, validate_queue, pc>>

CalculateSha256(t, aid) ==
    \* can be called repeatedly (if other identical blobs were to get uploaded)
    /\ db_assets[aid].sha256 = NULL
    /\ bounded_actions[t].checksums > 0
    /\ pc[t] = ""
    /\ db_assets[aid].status # "none"
    /\ db_assets' = [db_assets EXCEPT ![aid]["sha256"] = "1",
    \* cheat because this can't override asset stuff because the blob is stored
    \* in a separate table
                                      ![aid]["rev"] = db_assets[aid].rev + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT ![t]["checksums"] = @ - 1]
    /\ UNCHANGED <<loaded_asset, pc, validate_queue>>

\* this can happen at any time since blob upload triggers it for every asset
\* that blob maps to.
ValidateAssetMetadata(t, aid) ==
    LET
        asset == ASSETS[aid]
    IN
    /\ pc[t] = ""
    /\ aid \in validate_queue
    \* TODO: simulate this no-oping because of optimistic lock?
    /\ bounded_actions[t].asset_validations > 0
    /\ db_assets' = [db_assets EXCEPT ![aid]["status"] = IF asset.sha256 # NULL THEN "valid" ELSE "invalid",
                                      ![aid]["rev"] = asset.rev + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT ![t]["asset_validations"] = @ - 1]
    /\ validate_queue' = validate_queue \ {aid}
    /\ UNCHANGED <<pc, loaded_asset>>

ValidateAssetMetadataCron(t, aid) ==
    LET
        asset == db_assets[aid]
    IN
    /\ pc[t] = ""
    /\ asset.status = "pending"
    \* TODO: simulate this no-oping because of optimistic lock?
    /\ bounded_actions[t].asset_validations > 0
    /\ db_assets' = [db_assets EXCEPT ![aid]["status"] = IF asset.sha256 # NULL THEN "valid" ELSE "invalid",
                                      ![aid]["rev"] = asset.rev + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT ![t]["asset_validations"] = @ - 1]
    /\ UNCHANGED <<pc, loaded_asset, validate_queue>>

---------------------------------------------------------------------------------
Init == /\ pc = [t \in 1..NUM_ACTORS |-> ""]
        /\ loaded_asset = [t \in 1..NUM_ACTORS |-> NULL]
        /\ bounded_actions = [t \in 1..NUM_ACTORS |-> [asset_validations |-> 2, checksums |-> 2]]
        /\ db_assets = [aid \in ASSETS |-> [status |-> "none",
                                            rev |-> 0,
                                            sha256 |-> NULL,
                                            blob |-> NULL]]
        /\ validate_queue = {}


Next == \/ \E t \in 1..NUM_ACTORS:
              \/ \E aid \in ASSETS:
                    \/ AddAssetToVersion(t, aid)
                    \/ CalculateSha256(t, aid)
                    \* cron
                    \/ ValidateAssetMetadataCron(t, aid)
              \/ \E aid \in validate_queue:
                    \/ ValidateAssetMetadata(t, aid)
\* request

\* add workflow
\* AddAssetToVersion - add pending asset to version
\* takes that in memory asset and
\* ValidateAssetMetadata if sha256 is set on the blob

\* probably not worth modeling change workflow
\* change workflow
\* lock asset
\* remove, then add

\* remove workflow
\* RemoveAssetFromVersion locks asset, removes it, and sets version to pending

\* worker

\* calculate_sha256 workflow
\* save asset 256
\* queue up validateassetmetadata on asset_id


Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=====================================================

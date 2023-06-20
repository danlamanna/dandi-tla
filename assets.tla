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
    validatable_assets,
    \* keep the model running in a reasonable time
    bounded_actions

AssetStates == {"none", "pending", "valid", "invalid"}
--------------------------------------------------------------
vars == <<pc, db_assets, bounded_actions, loaded_asset, validate_queue, validatable_assets>>
---------------------------------------------------------------
AssetChangesIncreaseRevision(asset) ==
    /\ asset.status # asset'.status => asset'.rev = asset.rev + 1

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
    /\ UNCHANGED <<bounded_actions, validate_queue, pc, loaded_asset, validatable_assets>>

ValidateAssetMetadata(t, aid) ==
    LET
        asset == db_assets[aid]
    IN
    /\ pc[t] = ""
    /\ aid \in validate_queue
    /\ bounded_actions[t].asset_validations > 0
    \* TODO or INVALID
    /\ db_assets' = [db_assets EXCEPT ![aid]["status"] = "valid",
                                      ![aid]["rev"] = asset.rev + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT ![t]["asset_validations"] = @ - 1]
    /\ validate_queue' = validate_queue \ {aid}
    /\ UNCHANGED <<pc, loaded_asset, validatable_assets>>

ValidateAssetMetadataCronPart1(t) ==
    /\ pc[t] = ""
    /\ bounded_actions[t].cron_ticks > 0
    /\ validatable_assets' = [validatable_assets EXCEPT ![t] = {a \in DOMAIN db_assets: db_assets[a].status = "pending"}]
    /\ bounded_actions' = [bounded_actions EXCEPT ![t]["cron_ticks"] = @ - 1]
    /\ pc' = [pc EXCEPT ![t] = "ValidateAssetMetadataCronPart1"]
    /\ UNCHANGED <<loaded_asset, validate_queue, db_assets>>

ValidateAssetMetadataCronPart2(t) ==
    /\ pc[t] = "ValidateAssetMetadataCronPart1"
    /\ validate_queue' = validate_queue \union validatable_assets[t]
    /\ pc' = [pc EXCEPT ![t] = ""]
    /\ UNCHANGED <<loaded_asset, validatable_assets, db_assets, bounded_actions>>

---------------------------------------------------------------------------------
Init == /\ pc = [t \in 1..NUM_ACTORS |-> ""]
        /\ loaded_asset = [t \in 1..NUM_ACTORS |-> NULL]
        /\ validatable_assets = [t \in 1..NUM_ACTORS |-> {}]
        /\ bounded_actions = [t \in 1..NUM_ACTORS |-> [asset_validations |-> 2,
                                                       cron_ticks |-> 3]]
        /\ db_assets = [aid \in ASSETS |-> [status |-> "none",
                                            rev |-> 0]]
        /\ validate_queue = {}


Next == \/ \E t \in 1..NUM_ACTORS:
              \* cron
              \/ ValidateAssetMetadataCronPart1(t)
              \/ ValidateAssetMetadataCronPart2(t)
              \/ \E aid \in ASSETS:
                    \/ AddAssetToVersion(t, aid)
              \/ \E aid \in validate_queue:
                    \/ ValidateAssetMetadata(t, aid)

\* add workflow
\* AddAssetToVersion - add pending asset to version

\* remove workflow (worth modeling? it only impacts the version really)
\* RemoveAssetFromVersion locks asset, removes it, and sets version to pending

\* sha256 workflow (does this even need to exist? nothing refs it but validation and that's opaque to us)
\* save asset 256

\* validate workflow
\* 1. load an asset that's pending and has a sha256
\* 2. check if loaded asset is not published
\* 3. set loaded asset to valid or invalid

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=====================================================

---------------------- MODULE dandi ----------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS ASSETS, MAX_CHANGES_ALLOWED, MAX_DELETES_ALLOWED, NUM_ACTORS, NULL

ASSUME Cardinality(ASSETS) > 0
ASSUME MAX_CHANGES_ALLOWED > 0
ASSUME MAX_DELETES_ALLOWED > 0
ASSUME NUM_ACTORS > 0

VARIABLES
    db,
    pc,
    db_assets,
    loaded_asset,
    loaded_version,
    \* keep the model running in a reasonable time
    bounded_actions

\* none is used as a state to indicate a value that hasn't been created yet
AssetStates == {"none", "pending", "valid", "invalid"}
VersionStates == {"none", "pending", "valid", "invalid", "publishing", "published"}
--------------------------------------------------------------
vars == <<db, db_assets, bounded_actions, loaded_asset, loaded_version, pc>>

VersionHasOnlyValidAssets(version) == \A a \in version.assets:
                                         db_assets[a].status = "valid"

DraftVersionHasAsset(aid) == aid \in db.draft_version.assets
---------------------------------------------------------------
VersionChangesIncreaseRevision(version) ==
    /\ (\/ version.status # version'.status
        \/ version.size # version'.size
        \/ version.assets # version'.assets) => version'.rev = version.rev + 1

AssetChangesIncreaseRevision(asset) ==
    /\ (\/ asset.status # asset'.status
        \/ asset.published # asset'.published) => asset'.rev = asset.rev + 1

RevisionFieldIsMonotonicallyIncreasing(record) ==
    /\ record'.rev = record.rev \/ record'.rev = record.rev + 1

TypeInvariant ==
     /\ \A version \in {db.draft_version} \union {db.publish_version}:
             /\ version.status \in VersionStates
             /\ version.rev \in Nat
             /\ version.rev >= 0
             /\ version.size \in Nat
             /\ version.size >= 0
             \* a version with assets must be created
             /\ Cardinality(version.assets) > 0 => version.status # "none"
             /\ \A aid \in version.assets:
                 \* created assets aren't none
                 /\ db_assets[aid].status # "none"
         /\ \A aid \in ASSETS:
             /\ db_assets[aid].status \in AssetStates
             /\ db_assets[aid].rev \in Nat
             /\ db_assets[aid].rev >= 0
         /\ \A b \in DOMAIN bounded_actions:
             /\ bounded_actions[b] \in Nat
             /\ bounded_actions[b] >= 0

AssetStateTransitions == [][
    \A aid \in ASSETS:
        \* published assets stay published
        /\ db_assets[aid].published => db_assets[aid]'.published
        /\ RevisionFieldIsMonotonicallyIncreasing(db_assets[aid])
        /\ AssetChangesIncreaseRevision(db_assets[aid])

        /\ db_assets[aid].status = "none" => db_assets[aid]'.status \in {"none", "pending"}
        /\ db_assets[aid].status = "valid" => db_assets[aid]'.status \in {"valid", "invalid"}
        /\ db_assets[aid].status = "invalid" => db_assets[aid]'.status \in {"invalid", "valid"}
]_db_assets

VersionStateTransitions == [][
    LET
        dv == db.draft_version
        pv == db.publish_version
    IN
    /\ VersionChangesIncreaseRevision(dv)
    /\ VersionChangesIncreaseRevision(pv)
    /\ RevisionFieldIsMonotonicallyIncreasing(dv)
    /\ RevisionFieldIsMonotonicallyIncreasing(pv)
    \* the draft field never changes
    /\ dv.draft = dv'.draft
    /\ pv.draft = pv'.draft

    \* published versions are immutable
    /\ pv.status # "none" => pv = pv'
    /\ pv.status \in {"none", "valid"}

    \* draft versions transition these ways
    /\ dv.status = "none" => dv'.status \in {"none", "pending"}
    /\ dv.status = "pending" => dv'.status \in {"pending", "valid", "invalid"}
    /\ dv.status = "valid" => dv'.status \in {"pending", "valid", "publishing"}
    /\ dv.status = "invalid" => dv'.status \in {"invalid", "pending"}
    /\ dv.status = "publishing" => dv'.status \in {"publishing", "published"}
    /\ dv.status = "published" => dv'.status \in {"published", "pending"}
]_db

\* TODO: how to model this?
VersionsProcessed == <>[](
    /\ db.draft_version.status = "pending" ~> db.draft_version.status \in {"valid", "invalid"}
)

\* TODO: how to model this?
VersionsAggregated == <>[](
    /\ db.draft_version.size = Cardinality(db.draft_version.assets)
)

PublishedVersionsAggregated == [](
    /\ db.publish_version.status # "none" => db.publish_version.size = Cardinality(db.publish_version.assets)
)

VersionsPublished == <>[](
       /\ db.draft_version.status = "publishing" ~> db.draft_version.status = "published"
       /\ db.draft_version.status \in {"publishing", "published"} => VersionHasOnlyValidAssets(db.draft_version)
       /\ db.publish_version.status = "valid" => VersionHasOnlyValidAssets(db.publish_version)
)
------------------------------------------------------------------
LoadDraftVersion(t, version) ==
    /\ pc[t] = NULL
    /\ loaded_version[t] = NULL
    /\ version.draft
    /\ loaded_version' = [loaded_version EXCEPT ![t] = version]
    /\ UNCHANGED <<db, db_assets, bounded_actions, loaded_asset, pc>>

ChangeVersionMetadata(t) ==
    LET version == loaded_version[t] IN
    /\ pc[t] = NULL
    /\ loaded_version[t] # NULL
    /\ bounded_actions.changes > 0
    /\ version.draft
    \* optimistic lock
    /\ db.draft_version.status # "publishing"
    /\ db' = [db EXCEPT !["draft_version"]["status"] = "pending",
    \* cheat. this would only fail because we're changing the status and the rev isn't increasing,
    \* but we optimistically update the status so it can only go from non-publishing statuses
    \* back to pending.
                        !["draft_version"]["rev"] = db.draft_version.rev + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT !.changes = @ - 1]
    /\ UNCHANGED <<db_assets, loaded_asset, loaded_version, pc>>

ValidateDraftVersionMetadata(t) ==
    /\ pc[t] = NULL
    /\ db.draft_version.draft
    /\ db.draft_version.status = "pending"
    /\ \/ db' = [db EXCEPT !["draft_version"]["status"] = "valid",
                           !["draft_version"]["rev"] = db.draft_version.rev + 1]
       \/ db' = [db EXCEPT !["draft_version"]["status"] = "invalid",
                           !["draft_version"]["rev"] = db.draft_version.rev + 1]
    /\ UNCHANGED <<db_assets, bounded_actions, loaded_asset, loaded_version, pc>>

VersionAggregateAssetsSummary(t) ==
    LET version == loaded_version[t] IN
    /\ pc[t] = NULL
    /\ loaded_version[t] # NULL
    /\ bounded_actions.aggregates > 0
    /\ version.draft
    \* pending versions are put into the queue to agg summary, so only run this action
    \* when the loaded version is pending
    \* /\ version.status = "pending"
    \* optimistic update
    /\ version = db.draft_version
    /\ db' = [db EXCEPT !["draft_version"]["size"] = Cardinality(db.draft_version.assets),
                        !["draft_version"]["rev"] = version.rev + 1]
    /\ loaded_version' = [loaded_version EXCEPT ![t] = NULL]
    /\ bounded_actions' = [bounded_actions EXCEPT !.aggregates = @ - 1]
    /\ UNCHANGED <<db_assets, loaded_asset, pc>>


PublishVersionInit(t) ==
    /\ pc[t] = NULL
    \* can only publish if there's spot for it
    /\ db.publish_version.status = "none"
    /\ db.draft_version.draft
    /\ db.draft_version.status = "valid"
    /\ \A a \in db.draft_version.assets: db_assets[a].status = "valid"
    /\ db' = [db EXCEPT !["draft_version"]["status"] = "publishing",
                        !["draft_version"]["rev"] = db.draft_version.rev + 1]
    /\ pc' = [pc EXCEPT ![t] = "publishpart2"]
    /\ UNCHANGED <<db_assets, loaded_asset, bounded_actions, loaded_version>>

PublishVersionFinalize(t) ==
    /\ pc[t] = "publishpart2"
    /\ db.draft_version.status = "publishing"
    \* can only publish if there's spot for it
    /\ db.publish_version.status = "none"
    /\ db' = [db EXCEPT !["draft_version"]["status"] = "published",
                        !["draft_version"]["rev"] = db.draft_version.rev + 1,
                        !["publish_version"]["status"] = "valid",
                        !["publish_version"]["assets"] = db.draft_version.assets,
                        !["publish_version"]["size"] = Cardinality(db.draft_version.assets),
                        !["publish_version"]["rev"] = 1]
    \* technically assets aren't mutated in one time step like this, but assertion errors rollback
    \* the entire state, so i'm cheating a bit here.
    /\ db_assets' = [aid \in DOMAIN db_assets |-> IF DraftVersionHasAsset(aid) THEN
                                                    [db_assets[aid] EXCEPT !.published = TRUE,
                                                                           !.rev = @ + 1]
                                                  ELSE
                                                    db_assets[aid]]
    /\ pc' = [pc EXCEPT ![t] = NULL]
    /\ UNCHANGED <<bounded_actions, loaded_asset, loaded_version>>

\* asset = Asset.objects.get()

\* asset.fsdfsd
LoadAsset(t, aid) ==
    /\ loaded_asset[t] = NULL
    /\ db_assets[aid].status # "none"
    /\ loaded_asset' = [loaded_asset EXCEPT ![t] = <<aid, db_assets[aid]>>]
    /\ UNCHANGED <<db, db_assets, bounded_actions, loaded_version, pc>>

AddAssetToVersion(t, aid) ==
    LET version == loaded_version[t] IN
    /\ loaded_version[t] # NULL
    /\ version.draft
    /\ db_assets[aid].status = "none"
    \* optimistic lock on publishing, otherwise we don't care if we reset the version status
    \* back to pending.
    /\ db.draft_version.status # "publishing"
    /\ db' = [db EXCEPT !["draft_version"]["status"] = "pending",
                        !["draft_version"]["assets"] = version.assets \union {aid},
                        \* cheat and use the real revision id, because we don't care about the
                        \* violation in this particular state change (since in the real code it's
                        \* actually adding a new row instead of just doing a mutation).
                        !["draft_version"]["rev"] = db.draft_version.rev + 1]
    /\ db_assets' = [db_assets EXCEPT ![aid]["status"] = "pending",
                                      ![aid]["rev"] = @ + 1]
    /\ loaded_version' = [loaded_version EXCEPT ![t] = NULL]
    \* TODO validate
    /\ UNCHANGED <<loaded_asset, bounded_actions, pc>>


RemoveAssetFromVersion(t, aid) ==
    LET version == loaded_version[t] IN
    /\ loaded_version[t] # NULL
    /\ version.draft
    /\ db_assets[aid].status = "none"
    \* since we do m2m remove, this can simulate checking if it's in the real database
    /\ aid \in db.draft_version.assets
    /\ db' = [db EXCEPT !["draft_version"]["status"] = "pending",
                        !["draft_version"]["assets"] = version.assets \ {aid},
                        !["draft_version"]["rev"] = version.rev + 1]
    /\ loaded_version' = [loaded_version EXCEPT ![t] = NULL]
    /\ UNCHANGED <<loaded_asset, bounded_actions, db_assets, pc>>



\* this can happen at any time since blob upload triggers it for every asset
\* that blob maps to.
ValidateAssetMetadata(t) ==
    LET
        aid == loaded_asset[t][1]
        asset == loaded_asset[t][2]
    IN
    /\ loaded_asset[t] # NULL
    /\ bounded_actions.asset_validations > 0
    \* TODO IN APP CODE
    \* OPTIMISTIC LOCK AGAINST ENTIRE ROWVERSION OF ASSET IN CASE THIS RACES WITH ITSELF
    /\ asset = db_assets[aid]
    \* optimistic
    /\ ~db_assets[aid].published
    \* optimistically lock against mutating assets when the version is "publishing"
    /\ db.draft_version.status # "publishing"
    /\ \/ db_assets' = [db_assets EXCEPT ![aid]["status"] = "valid",
                                         ![aid]["rev"] = asset.rev + 1]
       \/ db_assets' = [db_assets EXCEPT ![aid]["status"] = "invalid",
                                         ![aid]["rev"] = asset.rev + 1]
    /\ loaded_asset' = [loaded_asset EXCEPT ![t] = NULL]
    /\ bounded_actions' = [bounded_actions EXCEPT !["asset_validations"] = @ - 1]
    /\ UNCHANGED <<loaded_version, db, pc>>


---------------------------------------------------------------------------------
Init == /\ loaded_asset = [t \in 1..NUM_ACTORS |-> NULL]
        /\ loaded_version = [t \in 1..NUM_ACTORS |-> NULL]
        /\ pc = [t \in 1..NUM_ACTORS |-> NULL]
        /\ bounded_actions = [
               asset_validations |-> 2,
               changes |-> MAX_CHANGES_ALLOWED,
               deletes |-> MAX_DELETES_ALLOWED,
               aggregates |-> 2]
        /\ db = [
               draft_version |-> [status |-> "pending",
                                  rev |-> 0,
                                  size |-> 0,
                                  assets |-> {},
                                  draft |-> TRUE],
               publish_version |-> [status |-> "none",
                                        rev |-> 0,
                                        size |-> 0,
                                        assets |-> {},
                                        draft |-> FALSE]]
        /\ db_assets = [aid \in ASSETS |-> [status |-> "none",
                                            rev |-> 0,
                                            published |-> FALSE]]

Next == \/ \E t \in 1..NUM_ACTORS:
              \/ LoadDraftVersion(t, db.draft_version)
              \/ ChangeVersionMetadata(t)
              \/ ValidateDraftVersionMetadata(t)
              \/ VersionAggregateAssetsSummary(t)
              \/ PublishVersionInit(t)
              \/ PublishVersionFinalize(t)
              \/ \E aid \in ASSETS:
                    \/ LoadAsset(t, aid)
                    \/ AddAssetToVersion(t, aid)
                    \/ ValidateAssetMetadata(t)
                    \/ RemoveAssetFromVersion(t, aid)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=====================================================

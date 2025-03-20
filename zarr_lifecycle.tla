---------------------- MODULE zarr_lifecycle ----------------------
(*
This models the lifecycle of zarr archives throughout the system.

Complete archives can be reset back to the pending state. The usage of "force ingestion"
allows a user to manually trigger ingestion of an archive which means that state transitions are
a bit more complex. Anywhere "ingesting" is mentioned it needs to also include "force_ingesting"
since that's just a special case of ingestion. It has to be structured this way because we still want
to maintain the ZarrStateTransitions invariant, only allowing odd transitions when the ingestion
is forced.

This is up to date with DANDI as of 4aaac16e6.
*)
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS ZARRS, NUM_ACTORS, NULL, MAX_CHANGES_ALLOWED, MAX_FORCE_INGESTS_ALLOWED

ASSUME Cardinality(ZARRS) > 0
ASSUME NUM_ACTORS > 0
ASSUME MAX_CHANGES_ALLOWED > 0
ASSUME MAX_FORCE_INGESTS_ALLOWED > 0

VARIABLES
    zarrs,
    ram,
    pc,
    bounded_actions

ZarrStates == {"none", "pending", "uploaded", "ingesting", "force_ingesting", "complete"}
--------------------------------------------------------------
vars == <<zarrs, bounded_actions, ram, pc>>
---------------------------------------------------------------
RevisionFieldIsMonotonicallyIncreasing(record) ==
    /\ record'.rev = record.rev \/ record'.rev = record.rev + 1

TypeInvariant ==
    /\ \A zid \in ZARRS:
        /\ zarrs[zid].status \in ZarrStates
        /\ zarrs[zid].rev \in Nat
        /\ zarrs[zid].rev >= 0

ZarrStateTransitions == [][
    \A zid \in ZARRS:
        /\ RevisionFieldIsMonotonicallyIncreasing(zarrs[zid])
        /\ zarrs[zid].status # zarrs[zid]'.status => zarrs[zid]'.rev = zarrs[zid].rev + 1

        /\ zarrs[zid].status = "none" => zarrs[zid]'.status \in {"none", "pending", "force_ingesting"}
        /\ zarrs[zid].status = "pending" => zarrs[zid]'.status \in {"pending", "uploaded", "force_ingesting"}
        /\ zarrs[zid].status = "uploaded" => zarrs[zid]'.status \in {"uploaded", "ingesting", "force_ingesting"}
        /\ zarrs[zid].status = "ingesting" => zarrs[zid]'.status \in {"ingesting", "force_ingesting", "complete"}
        /\ zarrs[zid].status = "complete" => zarrs[zid]'.status \in {"pending", "force_ingesting", "complete"}
        /\ zarrs[zid].status = "force_ingesting" => zarrs[zid]'.status \in {"force_ingesting", "complete"}
]_zarrs

ZarrProcessed == <>[](\A zid \in ZARRS:
                        zarrs[zid].status # "none")

\* note this ensures that it becomes complete at some point, but it can also go back to pending
FinalizedZarrsAlwaysComplete == \A zid \in ZARRS:
                                   /\ zarrs[zid].status = "uploaded" ~> zarrs[zid].status = "complete"

------------------------------------------------------------------
CreateZarrArchive(zid) ==
    /\ zarrs[zid].status = "none"
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "pending",
                              ![zid]["rev"] = @ + 1]
    /\ UNCHANGED <<ram, bounded_actions, pc>>

\* this represents either requesting signed urls or deleting files
ChangeZarrArchive(zid) ==
    /\ ~zarrs[zid].status \in {"none", "uploaded", "ingesting", "force_ingesting"}
    /\ bounded_actions.changes > 0
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "pending",
                              ![zid]["rev"] = @ + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT !.changes = @ - 1]
    /\ UNCHANGED <<ram, pc>>

FinalizeZarrArchive(zid) ==
    /\ zarrs[zid].status = "pending"
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "uploaded",
                              ![zid]["rev"] = @ + 1]
    /\ UNCHANGED <<ram, bounded_actions, pc>>

IngestZarrArchivePart1(t, zid, force) ==
    /\ zarrs[zid].status # "none"
    /\ pc[t] = NULL
    /\ \/ zarrs[zid].status = "uploaded"
       \/ (force /\ bounded_actions.force_ingests > 0)
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = IF force THEN "force_ingesting" ELSE "ingesting",
                              ![zid]["rev"] = @ + 1]
    /\ pc' = [pc EXCEPT ![t] = "part2"]
    /\ bounded_actions' = [bounded_actions EXCEPT !.force_ingests = IF force THEN @ - 1 ELSE @]
    /\ ram' = [ram EXCEPT ![t] = zid]

IngestZarrArchivePart2(t) ==
    /\ pc[t] = "part2"
    /\ zarrs[ram[t]].status \in {"ingesting", "force_ingesting"}
    /\ zarrs' = [zarrs EXCEPT ![ram[t]]["status"] = "complete",
                              ![ram[t]]["rev"] = @ + 1]
    /\ ram' = [ram EXCEPT ![t] = NULL]
    /\ pc' = [pc EXCEPT ![t] = NULL]
    /\ UNCHANGED <<bounded_actions>>

AllZarrsComplete ==
    /\ \A zid \in ZARRS: zarrs[zid].status = "complete"
    /\ UNCHANGED <<zarrs, bounded_actions, ram, pc>>

---------------------------------------------------------------------------------
Init == /\ ram = [t \in 1..NUM_ACTORS |-> NULL]
        /\ pc = [t \in 1..NUM_ACTORS |-> NULL]
        /\ bounded_actions = [changes |-> MAX_CHANGES_ALLOWED, force_ingests |-> MAX_FORCE_INGESTS_ALLOWED]
        /\ zarrs = [zid \in ZARRS |-> [status |-> "none", rev |-> 0]]

Next == \/ \E t \in 1..NUM_ACTORS:
              \E zid \in ZARRS:
                 \/ CreateZarrArchive(zid)
                 \/ ChangeZarrArchive(zid)
                 \/ FinalizeZarrArchive(zid)
                 \/ \E force \in BOOLEAN:
                    /\ IngestZarrArchivePart1(t, zid, force)
                 \/ IngestZarrArchivePart2(t)
        \/ AllZarrsComplete

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=====================================================

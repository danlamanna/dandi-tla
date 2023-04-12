---------------------- MODULE zarr ----------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS ZARRS, NUM_ACTORS, NULL

ASSUME Cardinality(ZARRS) > 0
ASSUME NUM_ACTORS > 0

VARIABLES
    zarrs,
    ram,
    pc,
    \* keep the model running in a reasonable time
    bounded_actions

ZarrStates == {"none", "pending", "ingesting", "complete"}
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

        /\ zarrs[zid].status = "none" => zarrs[zid]'.status \in {"none", "pending"}
        /\ zarrs[zid].status = "pending" => zarrs[zid]'.status \in {"pending", "ingesting"}
        /\ zarrs[zid].status = "ingesting" => zarrs[zid]'.status \in {"ingesting", "complete"}
        \* can only go to ingesting because of force ingestion
        \* TODO - better way of representing this?
        /\ zarrs[zid].status = "complete" => zarrs[zid]'.status \in {"complete", "pending", "ingesting"}
]_zarrs

ZarrProcessed == <>[](\A zid \in ZARRS:
                        zarrs[zid].status # "none")
------------------------------------------------------------------
CreateZarrArchive(zid) ==
    /\ zarrs[zid].status = "none"
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "pending",
                              ![zid]["rev"] = @ + 1]
    /\ UNCHANGED <<ram, bounded_actions, pc>>

RequestSignedUrls(zid) ==
    /\ ~zarrs[zid].status \in {"none", "ingesting"}
    /\ bounded_actions.request_urls > 0
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "pending",
                              ![zid]["rev"] = @ + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT !.request_urls = @ - 1]
    /\ UNCHANGED <<ram, pc>>

DeleteZarrFiles(zid) ==
    /\ ~zarrs[zid].status \in {"none", "ingesting"}
    /\ bounded_actions.deletes > 0
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "pending",
                              ![zid]["rev"] = @ + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT !.deletes = @ - 1]
    /\ UNCHANGED <<ram, pc>>

IngestZarrArchivePart1(t, zid, force) ==
    /\ zarrs[zid].status # "none"
    /\ pc[t] = NULL
    /\ zarrs[zid].status = "pending" \/ force
    /\ bounded_actions.ingests > 0
    /\ zarrs' = [zarrs EXCEPT ![zid]["status"] = "ingesting",
                              ![zid]["rev"] = @ + 1]
    /\ pc' = [pc EXCEPT ![t] = "part2"]
    /\ bounded_actions' = [bounded_actions EXCEPT !.ingests = @ - 1]
    /\ ram' = [ram EXCEPT ![t] = zid]

IngestZarrArchivePart2(t) ==
    /\ pc[t] = "part2"
    \* this is equivalent to just adding:
    \* asset zarr.status == ZarrArchiveStatus.INGESTING in part 2 of ingest_zarr_archive
    \* TODO
    /\ zarrs[ram[t]].status = "ingesting"
    /\ bounded_actions.ingests_two > 0
    /\ zarrs' = [zarrs EXCEPT ![ram[t]]["status"] = "complete",
                              ![ram[t]]["rev"] = @ + 1]
    /\ bounded_actions' = [bounded_actions EXCEPT !.ingests_two = @ - 1]
    /\ ram' = [ram EXCEPT ![t] = NULL]
    /\ pc' = [pc EXCEPT ![t] = NULL]
---------------------------------------------------------------------------------
Init == /\ ram = [t \in 1..NUM_ACTORS |-> NULL]
        /\ pc = [t \in 1..NUM_ACTORS |-> NULL]
        /\ bounded_actions = [request_urls |-> 4, ingests |-> 4, ingests_two |-> 4, deletes |-> 4]
        /\ zarrs = [zid \in ZARRS |-> [status |-> "none", rev |-> 0]]

Next == \/ \E t \in 1..NUM_ACTORS:
              \E zid \in ZARRS:
                 \/ CreateZarrArchive(zid)
                 \/ RequestSignedUrls(zid)
                 \* Note that Finalize isn't modeled. All it does is kick off ingestion and doesn't mutate
                 \* state so there's nothing that can really break from it.
                 \/ DeleteZarrFiles(zid)
                 \/ \E force \in BOOLEAN:
                     \/ IngestZarrArchivePart1(t, zid, force)
                 \/ IngestZarrArchivePart2(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
=====================================================

# PUBLICATION_RUNBOOK — steps for the session in which the author authorises publication (not before)

Nothing in this file has been executed. No repository, draft, DOI reservation or deposit exists. The steps are run
only after the author's explicit instruction, all in one session, in this order. Two services are involved; they do not
form one technical transaction, so each step is checked before the next.

## 0. Preconditions (local, no external action)
1. `python3 release/verify_published.py` → `PUBLISHED_CHECK=PASS`.
2. `release/CURRENT_STATE.json`: finite checks PASS, blueprint gate PASS, portable Lean release check PASS (or the
   author accepts a stated exception), author send gate settled for what is published (COI, AI wording, read-through
   concern the journal submission, not this deposit; the author decides whether to wait for them).
3. The author names: the repository name and visibility, the release tag (`v1.0.0` proposed), whether the paper is a
   separate Zenodo record (proposed: yes, `publication/preprint`, CC BY 4.0) next to the software record (MIT for code
   and machine-readable files, CC BY 4.0 for prose).

## Rights each record must show at the end (from `release/metadata/zenodo_*.json`, `_private.final_rights`)

| record | licences shown | scope (as printed in the description) |
|---|---|---|
| software | MIT **and** CC BY 4.0 (two licences, each for a part of the files; not alternatives) | MIT: code and machine-readable files; CC BY 4.0: prose by the author (paper sources and PDFs, blueprint, Markdown). Per file: `release/DISTRIBUTION_FILES.tsv` |
| paper | CC BY 4.0 | the whole record (paper text and PDFs) |

The legacy deposit API has a single licence field (`metadata.license`: `mit` for software, `cc-by-4.0` for the paper);
it is stated to apply to all files of a deposition. Zenodo's web form supports declaring several licences for one
record ("mixed license uploads", Zenodo help, Licenses and rights). The second licence of the software record is
therefore added in the web form (step 3.3), after the last metadata update; no API format for several licences is
assumed. `CITATION.cff` has no top-level `license` (CFF 1.2.0 reads a list as alternatives); its preferred citation
(the paper) carries CC-BY-4.0.

## 1. Identifiers first
1. Zenodo: create the two drafts (software, paper). Send only the object `metadata` of
   `release/metadata/zenodo_software.json` and `release/metadata/zenodo_paper.json` (`{"metadata": record["metadata"]}`);
   the object `_private` is a local record and is never sent. Reserve both DOIs. Record for each draft its deposition
   ID, its reserved version DOI (`metadata.prereserve_doi.doi`) and its concept record ID (`conceptrecid`); the concept
   DOI is written as `10.5281/zenodo.<conceptrecid>` (Zenodo's numbering; not verified on a draft here, it is checked
   to resolve at step 4.3). These two drafts are used to the end; no further draft is created.
2. GitHub: create the repository (empty), record its URL. The Zenodo–GitHub integration stays OFF for this
   repository: if it were on, the GitHub release of step 4.1 would create a further Zenodo record with its own DOI.

## 2. Insert the identifiers and rebuild — one command (local, no external action)
This package is the output of this step and is never edited by hand. The command runs in the author's development
folder, where the private tools `papers/tools/prepare_publication.py` and `papers/tools/build_release_tree.py` live
(they read the author's canonical sources and are not part of this package).
1. Write `IDS.json` outside the tree (null for anything not issued):
   ```
   {"state": "release", "release_date": "YYYY-MM-DD", "repository_code": "https://github.com/OWNER/NAME",
    "git_tag": "v1.0.0", "software_version_doi": "10.5281/zenodo.N1", "software_concept_doi": "10.5281/zenodo.N2",
    "paper_version_doi": "10.5281/zenodo.N3", "paper_concept_doi": "10.5281/zenodo.N4"}
   ```
2. Run (the reference run of the finite checks and the portable Lean records are those named in
   `release/CURRENT_STATE.json`; `TAG` is a new backup tag, `LOGDIR` a new directory):
   ```
   python3 papers/tools/prepare_publication.py --ids IDS.json --tag TAG --run REFERENCE_RUN \
     --portable-logs portable_R11_stage2=PORTABLE_STAGE2 --portable-logs portable_R12_stage3=PORTABLE_STAGE3 \
     --log LOGDIR
   ```
   Expected last line `PREPARE_PUBLICATION=PASS`, exit 0; `LOGDIR/RESULT.json` lists every step with its exit code.
   The fixed order: (1) the identifiers go into the canonical `release/metadata_source.json` (the single source);
   (2) the Data-availability sentence of the paper gets the software version DOI; (3) amsart PDF; (4) elsarticle
   version and PDF; (5) blueprint (with `BUILD_RECORD.json` and its gate); (6) the private folder manifest;
   (7) the distribution tree: copies, `checks/LABELS.md` from the new paper numbering, `CITATION.cff`, both Zenodo
   records and the README/CHANGELOG blocks generated from the source, `release/CURRENT_STATE.json`,
   `release/DISTRIBUTION_FILES.tsv`, `release/verify_published.py`; (8) a copy of the tree in a new directory
   (`LOGDIR/pkg`) passes `verify_published.py`, `gen_metadata.py --check` (bytes and meaning: HTML paragraph texts,
   licence fields, rights), both map checks, the blueprint gate, the three test suites and an identifier check (every
   identifier of the source is in `CITATION.cff`, the Zenodo records, `README.md` and both paper sources; the software
   version DOI is in the text of both paper PDFs).
3. The set of (path, licence, category, role) cannot change silently: the builder compares it with the previous
   candidate and stops unless `--accept-set-change REASON` is given for a change the author approved. Inserting
   identifiers changes hashes and sizes only.
4. Regenerating cannot lose an identifier: every identifier-bearing file is generated from the source, and a hand edit
   of a generated file fails `gen_metadata.py --check`. Test identifiers (`10.99999/…`, `example.invalid`) are refused
   unless `--allow-test-ids` is given, which only the offline rehearsal uses.
5. Make the archive from the verified tree; record its SHA-256 outside the tree (no self-reference).

## 3. Put the final metadata on the same two drafts (before any publish)
Uploading files does not change a draft's metadata: the records generated in step 2 differ from the ones the drafts
were created with in `description` (status sentence), `publication_date` and `related_identifiers` (the pair
relations and the repository link). They are saved to the SAME drafts of step 1.
1. For each record, update its draft with the generated `metadata` object only: legacy deposit API
   `PUT /api/deposit/depositions/<deposition ID>` with body `{"metadata": final["metadata"]}` where `final` is
   `LOGDIR/pkg/release/metadata/zenodo_<record>.json` (never `_private`); or the same values in the web form.
   Do not create a new draft.
2. Read back each draft (`GET /api/deposit/depositions/<deposition ID>`, saved to a file outside the tree) and compare:
   `python3 tools/gen_metadata.py --readback software SAVED_SOFTWARE.json` and
   `python3 tools/gen_metadata.py --readback paper SAVED_PAPER.json` (run in `LOGDIR/pkg`) → `READBACK_<RECORD>=PASS`.
   Compared: every reserved-DOI field of the copy against the version DOI in the package, the concept DOI against
   `10.5281/zenodo.<conceptrecid>`, title, version, publication_date, upload and publication type, access right,
   creators (all fields), keywords, the paragraph texts of the description (HTML parsed; whitespace normalised, so
   server-side formatting does not matter; anything outside the paragraphs fails), the related identifiers
   (identifier, relation, scheme; DOI prefixes removed) and the single licence field (`mit` / `cc-by-4.0`). Metadata
   fields the generator does not write are listed, not failed; other server-managed fields (IDs, links, state) are
   not compared. A FAIL here stops the session before step 3.3.
3. Software record only, as the LAST metadata change: in the Zenodo web form of the draft, add CC BY 4.0 next to MIT
   (Licenses; mixed licence uploads) and save. Paper record: nothing to add (CC BY 4.0 from the API field).
   No metadata PUT is sent after this point: a PUT carries the single licence field again and could remove CC BY 4.0.
   If a metadata correction is needed after this point, make it in the web form, or repeat 3.1–3.3 in this order.
   Then GET the software draft again and run `python3 tools/gen_metadata.py --readback software SAVED.json
   --after-web-form` → PASS (the web-form save must not have changed the description or any other compared field; the
   licence field must contain `mit` and nothing outside MIT and CC BY 4.0). How the legacy API reports two licences is
   not known here: if the licence field is absent or in another format, the result is `READBACK_SOFTWARE=UNDECIDED`
   (exit 3, never PASS) and the preview of step 3.4 decides; any FAIL stops the session.
4. Preview each draft and check — a hard stop: if the software record does not show both licences, do not publish
   (its description says the files are distributed under two licences). Check: the licences shown equal the table above (software: exactly MIT and CC BY 4.0;
   paper: exactly CC BY 4.0); the description shows the abstract in full (including `sum_{i<r}`) and the licence
   paragraph with both scopes; the related identifiers and their directions.

## 4. Publish (one pass, each step checked)
1. Push the tree to GitHub; tag `v1.0.0`; create the release with the archive; compare the release archive with the
   verified tree.
2. Upload the same archive to the Zenodo software draft and the paper PDFs (amsart; optionally elsarticle and the
   blueprint) to the paper draft; check the files' SHA-256 on Zenodo against the local values; recheck the preview
   of step 3.4 (rights still as in the table); publish both.
3. Check that both version DOIs and both concept DOIs resolve (the concept DOIs to the concept records), that the
   published records show the rights of the table and the full description, that the GitHub README and
   `CITATION.cff` show the DOIs, that no further Zenodo record was created from GitHub, and that nothing else changed.

## 5. Afterwards
Record the public identifiers in the author's records; the journal submission (FFTA) cites the software version DOI in
Data availability. The cited earlier paper (IT-26-1499) is related by citation only; it is not a version of this
package. A later version gets new version DOIs (the concept DOIs stay) through the same command, and steps 3.1–3.4
again for its drafts.

## Not verified here
No Zenodo or GitHub account API has been called. The readback compares a saved JSON offline; the field names follow
the legacy deposit API documentation (developers.zenodo.org). How the legacy API reports a record that carries two
licences after the web-form step is not known here, which is why rights are checked in the preview (step 3.4), not
by the readback command after that step. Not verified either: that `10.5281/zenodo.<conceptrecid>` is the concept
DOI of a draft before its first publication (checked at step 4.3), and the exact behaviour of the Zenodo–GitHub
integration (kept off, step 1.2).

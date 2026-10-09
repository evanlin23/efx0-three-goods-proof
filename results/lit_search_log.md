# Literature search log (proof/lit-search)

Search for prior work on TARGET, conjecture D and their methods; the verdict is in `proofs/novelty.md`. Every query and source is listed with its date, so the search can be repeated. Read levels used everywhere: **full** (full text read), **section** (named pages or sections read), **grep** (full text searched by pattern, matches read in context), **abstract**, **snippet** (search-result snippet or metadata only).

All searches: 2026-09-25, from the cloud container (branch `proof/lit-search`), by `curl` and the session's web-search and web-fetch tools. No PDF or paper text is committed; the repository holds only paraphrases with page or section numbers.

## 1. Access from the container (2026-09-25)
| Source | Access | Used for |
|---|---|---|
| arxiv.org HTML search (`https://arxiv.org/search/?query=Q&searchtype=all&abstracts=show&size=200`) | works | 92 queries (§2); titles, authors, abstracts |
| arxiv.org PDFs (`https://arxiv.org/pdf/ID`) | works | 118 full texts (§4) |
| export.arxiv.org API | HTTP 406, refused | – |
| OpenAlex API | 1 search worked, then HTTP 429 "free daily budget ... used up" (shared IP); single-record lookup still worked | record of Viswanathan–Mehta (W7124246012, DOI 10.65109/osos1146): cited_by_count 0 |
| Semantic Scholar API (direct and via web fetch) | HTTP 429 on every try (5 retries with backoff) | – |
| DBLP API | bot wall ("Making sure you're not a bot") | – |
| Crossref API | works | Viswanathan–Mehta (DOI 10.65109/osos1146): is-referenced-by-count 0; metadata and abstract of Brams–Kilgour–Klamler (DOI 10.3390/g17010004) |
| Google Scholar | `curl`: HTTP 429; web-fetch tool: works | title search for Viswanathan–Mehta: 1 result, "All 7 versions", **no "Cited by" link** (i.e. 0 citations indexed) |
| par.nsf.gov | works | two records of Viswanathan–Mehta (PAR 10511105, 10572377) with full text |
| rutamehta.cs.illinois.edu | works | Ruta Mehta's CV (2026 version) |
| ec26.sigecom.org | works | EC 2026 accepted-papers list |
| isa-afp.org | works | Isabelle AFP topic "Games and economics" |
| cs.ox.ac.uk | works | author PDF of Christodoulou–Fiat–Koutsoupias–Sgouritsa |
| courses.grainger.illinois.edu | works | CS 580 Fall 2023 student slides on EFX |
| mdpi.com | HTTP 403 | (abstract taken from Crossref instead) |
| gargnikhil.com/EconCSLib | redirect page only | – |

GitHub repositories other than this one were not opened (session scope), so EconCSLib's code was not inspected; what it contains is taken from its two papers.

## 2. arXiv queries (2026-09-25)
Hits = total results reported by arXiv; all results were listed (page size 200) and their titles scanned (290 distinct papers). All 290 abstracts were also searched for `picky|limited|at most (two|three|four|k) (goods|items)|few goods|values at most|positively value|EFX_0|zero-tolerant|strong EFX|zero marginal|zero-valued|support`, and the matches read. Abstracts were read in full for the papers listed with read level "abstract" or better in `proofs/novelty.md` §3.

| # | Query (arXiv search, field "all") | Hits |
|---|---|---|
| 1 | `EFX` | 160 |
| 2 | `EFX0` | 0 |
| 3 | `EFX_0` | 1 |
| 4 | `strong EFX` | 14 |
| 5 | `zero-tolerant EFX` | 2 |
| 6 | `envy-free up to any good` | 56 |
| 7 | `envy-freeness up to any good` | 86 |
| 8 | `EFX picky` | 0 |
| 9 | `EFX k-limited` | 1 |
| 10 | `EFX few goods` | 9 |
| 11 | `EFX three goods` | 35 |
| 12 | `EFX at most three goods` | 18 |
| 13 | `EFX restricted` | 25 |
| 14 | `EFX sparse` | 0 |
| 15 | `EFX graphical valuations` | 5 |
| 16 | `EFX graph` | 25 |
| 17 | `EFX hypergraph` | 2 |
| 18 | `EFX multigraph` | 11 |
| 19 | `EFX non-differentiative` | 0 |
| 20 | `EFX binary valuations` | 14 |
| 21 | `EFX bi-valued` | 8 |
| 22 | `EFX existence` | 122 |
| 23 | `EFX survey` | 2 |
| 24 | `EFX tri-valued` | 2 |
| 25 | `EFX degree` | 2 |
| 26 | `EFX bounded` | 44 |
| 27 | `EFX support` | 7 |
| 28 | `EFX orientation` | 11 |
| 29 | `EFX zero marginal` | 7 |
| 30 | `EFX zero-valued goods` | 8 |
| 31 | `EFX lexicographic` | 6 |
| 32 | `EFX ordinal` | 7 |
| 33 | `EFX Lean` | 2 |
| 34 | `fair division Lean formalization` | 1 |
| 35 | `fair division formal verification` | 0 |
| 36 | `envy-free Isabelle` | 0 |
| 37 | `EFX serial dictatorship` | 1 |
| 38 | `EFX local search` | 2 |
| 39 | `EFX relevant goods` | 3 |
| 40 | `EFX interval` | 1 |
| 41 | `EFX leximin` | 4 |
| 42 | `envy-free up to any item` | 40 |
| 43 | `envy-freeness up to any item` | 60 |
| 44 | `EFX allocations` | 153 |
| 45 | `EFX allocation existence additive` | 84 |
| 46 | `fair allocation hypergraph` | 8 |
| 47 | `fair division hypergraph` | 4 |
| 48 | `picky agents` | 1 |
| 49 | `limited liking fair division` | 2 |
| 50 | `EFX restricted additive` | 19 |
| 51 | `EFX unit demand` | 5 |
| 52 | `pair-demand valuations` | 12 |
| 53 | `EFX zero values` | 9 |
| 54 | `EFX valued by at most` | 27 |
| 55 | `EFX small support` | 0 |
| 56 | `EFX matching` | 10 |
| 57 | `EFX envy graph source` | 0 |
| 58 | `fair division proof assistant` | 1 |
| 59 | `fair division Coq` | 0 |
| 60 | `fair allocation formally verified` | 4 |
| 61 | `social choice Lean` | 17 |
| 62 | `Lean 4 formalization economics` | 11 |
| 63 | `envy-freeness formalization` | 11 |
| 64 | `EFX SAT solving` | 1 |
| 65 | `EFX computer-assisted` | 1 |
| 66 | `EFX four agents` | 14 |
| 67 | `EFX additive open problem` | 26 |
| 68 | `EFX goods each agent` | 36 |
| 69 | `strongly EFX` | 3 |
| 70 | `EFX with charity` | 7 |
| 71 | `EFX partial allocation` | 14 |
| 72 | `EFX chores few` | 1 |
| 73 | `EFX graphical` | 6 |
| 74 | `EFX cancelable` | 9 |
| 75 | `EFX multi-graph` | 6 |
| 76 | `EFX girth` | 4 |
| 77 | `EFX orientations` | 11 |
| 78 | `fair division sparse valuations` | 1 |
| 79 | `fair division bounded number of goods per agent` | 2 |
| 80 | `indivisible goods each agent values few goods` | 2 |
| 81 | `EFX identical ordering` | 6 |
| 82 | `EFX ordinal rankings` | 1 |
| 83 | `EFX hitting set` | 0 |
| 84 | `EFX rotation` | 0 |
| 85 | `envy cycle elimination EFX source` | 0 |
| 86 | `EFX potential function Pareto improvement` | 0 |
| 87 | `EFX picking sequence` | 0 |
| 88 | `EFX round robin` | 2 |
| 89 | `EFX peeling` | 0 |
| 90 | `EFX reduction core` | 0 |
| 91 | `EFX champion` | 0 |
| 92 | `Formal Conjectures Lean benchmark` | 5 |

Four more queries first failed because of an invalid page size and were rerun with size 25: `Osterhaus` (4 hits, none on fair division), `strong EFX two goods` (7), `lexicographic preferences EFX` (5), `Mastrakouis` (0), `Sotiriou EFX` (5).

## 3. Web searches (session web-search tool, 2026-09-25)
| # | Query | Relevant results |
|---|---|---|
| 1 | `"On the existence of EFX under picky or non-differentiative agents"` | ACM DL (10.5555/3635637.3663218), experts.illinois.edu, IFAAMAS PDF, NSF PAR, Mehta CV; no arXiv or journal version |
| 2 | `Viswanathan Mehta "picky" EFX "4 goods" OR "four goods" OR "four items" cited` | same records only; no citing paper |
| 3 | `EFX "at most three" goods each agent values strong EFX zero-valued goods existence` | known papers only (three types of agents, 2508.15380, 2604.18216, ...) |
| 4 | `"EFX" "k-limited" OR "3-limited" OR "4-limited" fair division agents value few goods` | no result on few relevant goods; only k-valued and few-types papers |
| 5 | `"strong EFX" OR "EFX0" OR "zero-tolerant EFX" existence each agent positively values few goods` | evanlin23/mrd-efx and this repository (ours); 2608.08590; Brams–Kilgour–Klamler (Games 2026) |
| 6 | `EFX existence Lean OR Isabelle OR Coq formalization machine-checked proof envy-free up to any good` | evanlin23/mrd-efx and this repository (ours) only |
| 7 | `EFX allocations hypergraph each agent values at most three goods 2026` | 2606.18665, 2606.26948, 2608.03171 (AAAI version), CFKS |
| 8 | `"Viswanathan and Mehta" EFX` | Mehta pages, this repository's PRs; no citing paper |
| 9 | `"picky" agents EFX "at most four" goods existence envy-free up to any good 2025 OR 2026` | no citing paper |
| 10 | `EFX existence "relevant goods" OR "relevant items" agent values few items additive valuations` | known papers only |
| 11 | `"envy-free up to any good" "each good is valued by at most" agents bounded degree existence` | (p, q)-bounded instances: 2506.09288, 2407.05139 (each good valued by ≤ 2 agents) |
| 12 | `EFX survey 2025 2026 existence open problems restricted valuations graphs "few goods"` | known papers only |
| 13 | `thesis "EFX" existence "strong EFX" OR "EFX0" dissertation 2025 OR 2026 fair division indivisible goods` | Hsu thesis (2510.12158); Akrami thesis (Saarland; not read) |
| 14 | `"Maya Viswanathan" EFX OR "fair division" OR "envy-free"` | no other paper by this author |
| 15 | `EFX "limited" agents like at most four items ternary valuations "0, a, b" full version journal` | no full version; CS 580 Fall 2023 slides (read, irrelevant) |
| 16 | `AAMAS 2026 OR IJCAI 2026 OR "EC 2026" EFX existence accepted papers envy-free up to any good` | EC 2026 list: "EFX allocations on multigraphs" (Christodoulou, Mastrakouis, Sgouritsa, Sotiriou), not on arXiv, not read |
| 17 | `"EFX" "sparse" valuations existence agents each value few goods hypergraph dual "bounded degree"` | known multigraph/hypergraph papers only |
| 18 | `EFX allocations envy-free up to any good preprint 2026` (ResearchGate only) | known arXiv papers and RG mirrors; a July 2026 preprint noting additive EFX is open = Sivashankar, arXiv 2607.27455 (swept) |
| 19 | `EFX envy-free up to any good indivisible goods allocation existence` (SSRN only) | no SSRN record; arXiv papers only |
| 20 | `EFX allocation existence preprint 2026` (zenodo.org, osf.io, hal.science, preprints.org, techrxiv.org, optimization-online.org) | **Bratby, Zenodo 22665180**; otherwise known arXiv papers |
| 21 | `"complete" EFX allocation additive valuations preprint July 2026 every fair-division instance` (ResearchGate only) | nothing new |
| 22 | `Bratby EFX preprint "GPT-6" OR "AI" complete EFX allocations` | the Zenodo record only |

Rows 18–22 are second-pass searches (§6).

## 4. Full-text sweep of recent EFX papers (2026-09-25)
**What was swept (corrected in the second pass).** The arXiv queries of §2 return 165 distinct papers with identifier ≥ 2404, i.e. from after AAMAS 2024, where Viswanathan–Mehta appeared. All 165 were downloaded and text-searched, in two passes:
- *First pass:* 112 identifiers were queued, taken from the batch-1 queries only (§2 rows 1–41). Two of them, 2609.23577 and 2609.28333, were silently skipped by a bug: the download loop dropped the last line of a list file that had no trailing newline. So 110 were swept, plus 2606.16144 and 2606.13306 (EconCSLib, read separately). The first version of this log said 112; that was wrong.
- *Second pass, after the coordinator's review of PR #22:* the other 51 results with identifier ≥ 2404 (from §2 rows 42–92, most of them off-topic hits), plus the two skipped ones: 53 papers. The review had named 11 of them: 2410.15738, 2502.10516, 2507.12100, 2511.03629, 2601.13287, 2605.09930, 2605.31253, 2607.01059, 2608.16130, 2609.01580, 2609.08687.

Also downloaded for specific checks: 2002.05119, 2202.07551, 2208.08782. Text was extracted (PyMuPDF) and searched, case-insensitively, for:
- citation of Viswanathan–Mehta: `Viswanathan|Vishwanatha|picky|non-differentiative` (matches of Vignesh Viswanathan's papers discarded by hand);
- few relevant goods: `[k234]-limited|at most (two|three|four|2|3|4|k) (goods|items)|values? at most (two|three|four|3|4|k)|positively values? at most|likes at most`;
- EFX₀: `EFX *0|EFX₀|strong EFX|zero-tolerant|strongly EFX`;
- formalization: `Lean 4|Lean theorem prover|Isabelle|Coq|Rocq|proof assistant|machine-checked|formally verified|formaliz`;
- methods: `hitting set|serial dictatorship|need chain|rotat|local search|potential function|ordinal|top-heavy|strongly prefer` and envy-graph-source phrases.

Every match was read in context. Results:
- **No paper cites Viswanathan–Mehta** (both passes, 165 papers). Every `Viswanathan` match is a paper by an author printed as V. Viswanathan (Vignesh Viswanathan where the first name is given), e.g. Barman–Viswanathan, "Equitable colorings of vertex-weighted graphs" (arXiv 2605.09320), cited in 2607.01059. `picky` and `non-differentiative` never occur.
- **No existence result for few relevant goods per agent.** The "at most k goods" matches are about bundle sizes, hardness constructions, pair-demand valuations (2507.14957, PMMS), or EF1 round robin under "each agent values at most 3 goods and each good at most 3 agents" (2605.16791, a parallel-complexity statement, not existence). Second pass: the matches are about bundle values (2605.09930), an agent who "likes at most |G| items" in a weighted mixed-manna bound (2609.01580), and EFk definitions (2609.28333); no existence result for few relevant goods.
- **Formalization:** 2604.18216 §9 (Lean), 2608.10572 (Lean 4), EconCSLib 2606.16144 and 2606.13306; details in `proofs/novelty.md` §4. The second pass adds only Lean or formal-verification papers outside fair division: 2505.12840, 2506.07066, 2507.07052, 2512.07901, 2602.00101, 2606.18292 (economics); 2510.04520, 2605.29955, 2607.01544, 2608.11941 (autoformalization, mathematics); Formal Conjectures 2605.13171, which never mentions EFX.
- **Methods:** "need chain" occurs nowhere; "hitting set" only in hardness reductions (2608.30669) and communication bounds (2407.07641); "serial dictatorship" only in 2407.05891, 2410.06877, 2507.16209 (none about EFX existence).

First-pass identifiers (the 112 queued; 2609.23577 and 2609.28333 were swept only in the second pass): 2404.13527, 2404.18133, 2404.19740, 2405.14463, 2406.09744, 2406.10752, 2406.12413, 2406.13824, 2407.03318, 2407.05139, 2407.05891, 2407.07641, 2407.12461, 2409.01963, 2409.03594, 2409.06423, 2409.13616, 2410.02274, 2410.06877, 2410.08986, 2410.12039, 2410.13580, 2410.14272, 2410.14421, 2410.14593, 2410.17002, 2410.18655, 2410.23137, 2410.23979, 2411.19881, 2412.00254, 2412.00358, 2412.06513, 2501.04550, 2501.06506, 2501.13481, 2502.09777, 2503.01368, 2503.05695, 2504.03951, 2505.19961, 2505.22174, 2506.09288, 2506.15379, 2506.21727, 2507.09600, 2507.14957, 2507.16209, 2507.18251, 2507.19461, 2507.20899, 2508.03253, 2508.04779, 2508.15380, 2510.04915, 2510.05429, 2510.12158, 2511.04891, 2511.06218, 2512.21644, 2512.25033, 2601.03438, 2601.11372, 2601.12835, 2601.12849, 2601.16579, 2602.08714, 2602.11732, 2602.14668, 2602.15566, 2602.20929, 2603.17270, 2604.08345, 2604.18216, 2605.06451, 2605.10371, 2605.16791, 2605.19844, 2605.21448, 2606.02233, 2606.08872, 2606.11494, 2606.18665, 2606.18921, 2606.26948, 2607.10064, 2607.17224, 2607.17811, 2607.23367, 2607.27455, 2608.03171, 2608.04340, 2608.06325, 2608.08590, 2608.08864, 2608.08966, 2608.10397, 2608.10572, 2608.15159, 2608.16109, 2608.17295, 2608.24600, 2608.26410, 2608.29497, 2608.30203, 2608.30267, 2608.30669, 2609.10585, 2609.13970, 2609.15358, 2609.23577, 2609.28333.

Second-pass identifiers (53): 2406.03674, 2406.10895, 2409.16478, 2410.15738, 2410.17500, 2412.13622, 2502.10516, 2504.18489, 2505.12840, 2505.22862, 2506.01237, 2506.05379, 2506.07066, 2507.07052, 2507.12100, 2510.01689, 2510.04520, 2511.03629, 2512.07901, 2512.15401, 2601.01012, 2601.13287, 2602.00101, 2602.11330, 2602.12231, 2603.04885, 2603.20805, 2605.03581, 2605.09930, 2605.12537, 2605.13171, 2605.15750, 2605.29955, 2605.31253, 2606.04016, 2606.10472, 2606.16743, 2606.18292, 2606.21015, 2607.01059, 2607.01544, 2607.18139, 2607.28133, 2608.02911, 2608.08897, 2608.11941, 2608.16130, 2609.01580, 2609.08687, 2609.09621, 2609.19234, 2609.23577, 2609.28333.

## 5. Other sources checked (2026-09-25)
- Viswanathan–Mehta: IFAAMAS/ACM record (10.5555/3635637.3663218, pp. 2534–2536); NSF PAR 10511105 and 10572377 (both the same 3-page extended abstract, full text read; they differ only in the proceedings header); OpenAlex W7124246012; Crossref 10.65109/osos1146; Google Scholar (7 versions, no citations); arXiv (no version: queries `EFX picky`, `picky agents`, `EFX non-differentiative` give 0 or unrelated results).
- Ruta Mehta's CV (rutamehta.cs.illinois.edu/Mehta-CV.pdf, 2026 version; full): lists the paper only as conference paper C51 (AAMAS 2024); no journal version, no working paper on the topic; the mentoring section says Maya Viswanathan (2023–2024) is now an undergraduate at Yale.
- Isabelle AFP, topic "Mathematics/Games and economics" (isa-afp.org, 2026 listing): no entry on fair division, envy-freeness, or allocation.
- EC 2026 accepted papers (ec26.sigecom.org): EFX titles are #136 "EFX allocations on multigraphs" and #144 "EFX Allocations Exist on Multi-Graphs" (= 2606.18665).

## 6. Second pass after the coordinator's review of PR #22 (2026-09-25)
The review found a missed preprint: J. Bratby, "Complete EFX Allocations with Four More Goods than Agents", Zenodo, 2026-09-08, DOI 10.5281/zenodo.22665180. The first pass never searched general-purpose repositories. It is now read at section level (front matter, Theorem 1.1, §1.1–1.5; `proofs/novelty.md`, `proofs/citations.md`). Record: `https://zenodo.org/api/records/22665180`; PDF from `https://zenodo.org/api/records/22665180/files/EFX_EXCESS_FOUR_MANUSCRIPT.pdf/content` (149 pp.). The DOI landing page itself returns HTTP 403 to `curl`.

Zenodo API (`https://zenodo.org/api/records?q=Q&size=25&page=P`; anonymous page size is capped at 25; up to 4 pages per query):

| Query | Total | Fetched |
|---|---|---|
| `EFX` | 12 | 12 |
| `"envy-free up to any good"` | 0 | 0 |
| `"envy-freeness up to any good"` | 1 | 1 |
| `"envy-free up to any item"` | 0 | 0 |
| `"envy-freeness up to any item"` | 0 | 0 |
| `EFX0` | 0 | 0 |
| `"fair division" indivisible` | 789 | 100 |
| `"indivisible goods" envy` | 302 | 100 |
| `"fair allocation" indivisible` | 831 | 100 |
| `envy-free indivisible` | 46808 | 100 |
| `"maximin share" OR "EF1" allocation` | 27728 | 100 |
| `EFX allocation` | 27225 | 100 |

Of the 12 records matching `EFX`, two are fair division: Bratby (22665180) and Lin–Osterhaus, "Strong EFX allocations for 2-relevant agents: Lean 4 formalization" (22926398, 2026-09-24; the owner's evanlin23/mrd-efx, ours). The others are crystallography ("EF-X" data), paleontology figures, and an FX-markets lesson. The broad queries (unquoted terms, relevance-ranked) were scanned by title in their first 100 results. Fair-division records found: conference-paper mirrors by Aleksandrov, Walsh, Aziz et al. (2016–2019; online fair division, chores MMS); supplementary material of Sharma, "Exploring Relations among Fairness Notions in Discrete Fair Division" (arXiv 2502.02815); a 2024 class-style note on fair allocation with colluding agents. None is about EFX existence.

ResearchGate, SSRN and other repositories: web searches 18–22 (§3). Direct fetches with `curl` (2026-09-25) are refused with HTTP 403 by researchgate.net (`/search/publication?q=EFX`), papers.ssrn.com (`/sol3/results.cfm?txtKey_Words=EFX`) and mdpi.com, so these were searched only through the web-search tool.

Sweep correction: see §4.

## 7. (p, q)-bounded instances (workstream `proof/lit-pq`, 2026-09-25)
Task from the coordinator: read the (p, q)-bounded papers in full and relate them to this project. Result: `proofs/pq_bounded.md`; entries: `proofs/citations.md`, "Added 2026-09-25 by `proof/lit-pq`".

Queries:

| # | Source | Query | Hits / relevant results |
|---|---|---|---|
| 1 | arXiv | `"(p,q)-bounded"` | 7; relevant: 2506.09288, 2407.05139 (the others are physics) |
| 2 | arXiv | `bounded valuations EFX relevant agents` | 2: 2506.09288, 2407.05139 |
| 3 | arXiv | `Kaviani Seddighin Shahrezaei` | 5: 2606.26948, 2510.10423 (MMS, not relevant), 2506.09288, 2502.09777, 2407.05139 |
| 4 | arXiv | `restricted additive EFX` | 19; relevant: 2202.13676, 2407.05139, 2502.09777, 2512.21644, 2606.18665, 2608.08864 |
| 5 | web | `"(p,q)-bounded" OR "(p, q)-bounded" valuations EFX allocation each good relevant to at most p agents` | 2506.09288 and 2407.05139, with their Springer proceedings chapters (978-3-032-18660-7_26, 978-3-032-08560-3_15), 2502.09777; nothing new |
| 6 | local full texts (the 168 arXiv texts of §4: 165 results ≥ 2404 plus 2002.05119, 2202.07551, 2208.08782; and CFKS) | `\(p, ?q\)-bounded`, `Kaviani`, `\((2|∞), ?(1|∞)\)-bounded` | 21 papers mention them. Those with existence results in a bounded regime: CFKS; 2406.12413; 2407.05139; 2409.03594; 2502.09777; 2506.09288; 2512.21644; 2606.18665; 2606.26948; 2608.03171. The rest mention them only in related work |

Read for this task (levels in `proofs/pq_bounded.md` and `proofs/citations.md`):
- in full: 2407.05139v2 (32 pp.); 2506.09288v2 (18 pp.); CFKS (author PDF, 17 pp.; earlier only pp. 1–4); 2502.09777v1 (23 pp.);
- at section level: 2406.12413v3;
- re-checked: 2606.26948 and 2608.03171, for the (p, q) translation;
- abstracts: 2202.13676, 2008.08798;
- `k4/lb4.md` §5 (main) and `k4/c4.md` §7 (PR #33's branch `proof/k4-c4`), for the k = 4 comparison.

Structural checks, computed by `results/pq_structure.py` (log `results/pq_structure.log`; added after the review of PR #38; the first version of this log said they were not stored as scripts):
- **H_t of `k4/c4.md` §7, for t = 1..5:** n = 4t + 1, m = 10t + 3 (as stated), largest good degree p = 4 (the goods g_j), q = 1, a Berge 3-cycle in every H_t.
- **The 6 graphical all-P4 cores of K4.MC7 (`k4/MINCEX.md` §8):**

  | Core | Agent multigraph | Bipartite | Triangles |
  |---|---|---|---|
  | 1 | parallel pair (2,5) | no | yes |
  | 2 | parallel pairs (0,1), (3,4), (2,5); underlying girth 6 | yes | no |
  | 3 | parallel pairs (1,2), (4,5) | no | yes |
  | 4 | simple (prism) | no | yes |
  | 5 | simple (K₃,₃) | yes | no |
  | 6 | parallel pairs (0,1), (3,5) | yes | no |

  For cores 4 and 5, every agent's private good fits on a distinct non-adjacent pair (the complement is 2-regular), so each is a simple-graph (2, 1) instance and CFKS applies.

  Girth of the simple agent graph: 3, 6, 3, 3, 4, 4 for cores 1–6. Berge girth: 2 for the cores with parallel pairs (1, 2, 3, 6), and 3 and 4 for cores 4 and 5. The script reproduces the reviewer's independent table.

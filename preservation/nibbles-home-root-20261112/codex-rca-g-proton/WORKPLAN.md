# Live continuation notes

Goal: carry out BRIEF.md end-to-end for issue43 Chapters15–17. No deadline imposed. Do not falsely mark partial chapter complete or open PR before complete Chapter15 passes clean-slate+axioms. No merge/self-review. No installs/removals. User forbids touching other lanes/projects.

Repo: lane/formalize-everything. Book: books/rudin-real-and-complex-analysis. Branch rca-g-stage2-proton, base e1ba718. Exact pins unchanged. No code commit/push yet.

Agents:
- finite_product: exact15.3 and15.4 checked earlier; corrected15.8 checked within build2. JensenZeroGrowthCheck.lean full15.17/18/20 and BlaschkeNecessityWork.lean15.23 drafted, awaiting compiler. Now15.25/26/27.
- printed_inventory: inventory75 confirmed by visual ending-page rechecks. SpherePrescribedZerosWork.lean full15.11 draft ready. HolomorphicBezoutWork.lean15.15 includes component gluing, pair construction and finite induction; genuinely depends on forthcoming15.11/13 interfaces.
- mathlib_claims: corrected EntireLog helpers integrated; build2 one finite-fiber set syntax error now fixed. FactorizationWork15.10 integrated. MeromorphicPoleDataWork + MeromorphicQuotientAssemblyWork full15.12 drafted. MittagLefflerKernelWork + MittagLefflerSeriesWork actual normalized principal-part construction for15.13 drafted; global normalization/interpolation assembly ongoing.

Root build2 finished exit1 at18:32:45UTC. Exact frozen source/hash/log/audits in evidence/chapter15-build2.{lean,log,json}. One error in finite_fiber_of_hasSum_count: set preimage notation. Added `change Set.Finite {x | a x = z}` before simplification. Other47 of49 audits standard, two dependent failed declarations rejected. Integrated EntireProductWork and FactorizationWork into Chapter15 (~1247lines,56families). Build3 RUNNING root session79016 from18:36:02UTC, evidence/chapter15-build3.{lean,log,json}; root source frozen SHAe1090365012e060475e08e7011810eab1ada06275bc9abaa6ce590c9e9ea9651. Then sphere15.11, then Jensen15.17/18/20. Serialize one Lean process due to shared-host severe paging. No installs/removals or actions on other lanes.

Root authored EntireProductWork.lean draft15.9, NOT checked. Root also owns unverified BlaschkeWork.lean (full15.21 infinite, finite, empty, origin multiplicity), NevanlinnaWork.lean (15.22), HolomorphicIdealsWork.lean (15.14 definitions), and MeromorphicQuotientWork.lean (15.12 conditional helpers only); none is integrated. It imports Chapter15 and references future integrated `norm_one_sub_elementaryFactor_le` from15.8. First build Chapter15 olean before attempting. It has summable_primary_majorant_nat, primary_errors_locally_uniform, entire_primary_product with natural multiplicity counts. Need complete node15.9 testing after15.8 succeeds.

Integration: source scratch files have own namespace RudinRCA.Chapter15 except elementary nested ElementaryFactorWork. Merge imports/bodies/audits into single Chapter15.lean; remove duplicate definitions on elementary integration. Scratch files stay out of final commit (move to lane evidence/drafts, do not delete). Umbrella now imports RudinRCA.Chapter15 and preserves its original comment. Root integrated the corrected15.8 draft; next check is a lake build after EntireLog releases slot. Maintain PROGRESS counts already27/22/26 and Done0 meaning main.

Clean slate: brief says rm-rf.lake but also no removals. Prefer MOVE own book .lake to lane evidence/cache-before-clean-<timestamp>, cache get fresh, then build module/umbrella with exact pins and capture exit0/audits/hashes. Do not touch other directories. Do not do before code stable. Initial cache fetch exit0 at17:29.

15.10 printed statement assumes given zeros enumeration with multiplicities, then existence g,p; no separate enumeration-existence conclusion. Need faithful enumeration e.g HasSum of nat indicators=analyticOrderNatAt f z to avoid tsum default0 divergence loophole. Must derive escape infinity from discreteness+finite fibers, not silently assume. Finite/empty lists implicit product conventions deserve separate FinN variant. Root15.9 assumes escape as actually printed there.

STATUS.md and REPORT.md are live and explicitly incomplete. Evidence present. First PR only complete chapter with clean-slate and audit; normal PR via gh --body-file. Git SSH failed hostkey, HTTPS existing gh auth works; push can use git -c credential.helper='!gh auth git-credential'. No remote messages posted.

IMPORTANT inventory correction:15.27 Remark onp315 confirmed. INVENTORY/SCOPING/STATUS/REPORT/PROGRESS corrected to27/75;16endp332 and17endpp351–352 visually rechecked. Preserve15.27 in eventual chapter module.

Root later drafts: LogMeansWork.lean (~358lines) general Jensen posLog formula/monotonicity inclorigin, diskzero removal, angularAEzero/extendedlog bridge, exact negativeLogNorm angular integral, Fatou and boundarynonzero consequence. BlaschkeMeansWork.lean scalarlogradiusseries→0 and finiteboundarymodulus; analyticcirclemean identity remains. Printed agent now investigates actual radial-boundary existence needed15.19 via Fourier L2/Poisson/Lebesgue points, no existing theorem found. All these remain uncompiled.

import PoincareLib.Geometry.RicciFlow.Surgery.Global.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Global.Assembly

/-!
Adapted from Mapher `PoincareMT/Proofs/M52.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M52 checked global-certificate assembly

Natural-language theorem: construct one global surgery schedule and, for every
already given finite controlled flow on `[0,T)` satisfying the Definition 15.8
terminal event policy, source controls and schedule bounds, extend that same
flow to `[0,∞)` while preserving the
global controls. Separately, for every nonempty compact normalized initial
metric with no embedded projective plane of trivial normal bundle, and every
positive non-increasing control function bounded by that schedule, construct
a complete changing-carrier global surgery-flow certificate. The certificate
is identified with the M51 schedule's actual flow, schedule, and control
function, and retains the canonical, noncollapsing, pinching, admissibility,
volume, local-finiteness, and permanent-empty properties. Its retained M51
schedule and checked `terminalPolicy` adapter give the same-flow event policy.
Its surgery scale uses the source quantity `rho = delta * r`.

M51 owns the compatible finite/global construction and retains the selected
M49 loss certificate on its actual flow. The checked M52 assembly uses that
output for all four volume fields and passes through the same-flow extension
branch. M51's admitted global construction remains for later proof work.
The same schedule also retains the caller's positive bound on doubled setup
epsilon, chosen before the initial metric and control function.

Source: Morgan--Tian Theorem 15.9 and Corollary 15.10, printed pp. 363--366,
with the changing-carrier construction in Section 15.4 and finite-prefix
completion in Section 17.2, pp. 356--366 and 408--411 (arXiv V2 lines
16813--16849 and 18857--18957).  The corrected surgery-volume scaling from
M49 remains an upstream obligation.

This numbered entry is now a logical adapter with no admission. The substantive
Theorem 15.9 construction remains in M51, and volume evolution/loss in M49.
Earlier milestone files are read-only for later collaborators.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

theorem repairedGlobalFlow : RepairedGlobalFlowTheory.{u} := by
  refine ⟨?_⟩
  intro B28 E34 U35 S36 P44 L15 U43 S45 N46 C47 E48 P48 V49 F50 G51 epsilon_bound hpositive
  obtain ⟨K, schedule, hepsilon, extend, start⟩ :=
    G51.uniform_schedule B28 E34 U35 S36 P44 L15 U43 S45 N46 C47 E48 P48 V49 F50
      epsilon_bound hpositive
  refine ⟨K, schedule, hepsilon, extend, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ _ N hprojective delta hantitone hpositive hcutoff
  obtain ⟨G, hK, hschedule, hdelta⟩ :=
    start N hprojective delta hantitone hpositive hcutoff
  obtain ⟨R, hR⟩ := m52GlobalFlowDataFromSchedule G
  refine ⟨R, ?_, ?_, ?_⟩
  · rw [hR]
    exact hK
  · rw [hR]
    exact hschedule
  · rw [hR]
    exact hdelta

end PoincareMT

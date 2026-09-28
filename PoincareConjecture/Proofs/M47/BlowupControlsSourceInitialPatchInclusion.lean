import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialPatchHeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46

theorem source_initial_recent_patch_point_mem_older_carrier
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {S : MaximalStandardCapFlow F.standard_initial} {A eta Lambda L : ℝ}
    {J : Set ℝ} {V : Set (F.slice t).carrier} {U : Set StandardCapSpace}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J V)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J)
    (hbase : ∀ y ∈ V, HEq (e.forward 0 hzero y) y)
    (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 1000)
    (hLambda : 0 < Lambda) (hLambdaSmall : Lambda ≤ 1001 / 1000)
    (hbudget : 1 ≤ (1 - ((F.event t hT).necks i).neck.epsilon) * Lambda ^ 2)
    (hL : 1200 ≤ L) (hU : IsOpen U)
    (hsource : U ⊆ F.standard_initial.metric.ball 0 A)
    (havoid : ∀ x ∈ U, initial.chart x ∉ ((F.event t hT).caps i).carrier)
    {p : ℝ → StandardCapSpace}
    (hp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 p (Icc 0 1))
    (himage : MapsTo p (Icc (0 : ℝ) 1) U)
    (hlen : F.standard_initial.metric.pathELength p 0 1 <
      ENNReal.ofReal (6 + L / 3)) :
    let N := ((F.event t hT).necks i).neck
    let c := (N.coordinate_inverse (sourceInitialOldMap initial (p 0))).2
    sourceInitialOldMap initial (p 1) ∈ N.region (c - 2 * L / 3) (c + 2 * L / 3) := by
  let N := ((F.event t hT).necks i).neck
  let y0 := sourceInitialOldMap initial (p 0)
  let y1 := sourceInitialOldMap initial (p 1)
  let c := (N.coordinate_inverse y0).2
  have hp1 : p 1 ∈ U := himage ⟨zero_le_one, le_rfl⟩
  have hret1 := source_initial_chart_retention hT i initial (hsource hp1) (havoid (p 1) hp1)
  have hy1 : y1 ∈ N.region (-N.epsilon⁻¹) 0 := by
    exact hret1.2.2
  have hheight := source_initial_recent_patch_height_margin e initial comparison hzero hbase
    heta hetaSmall hLambda hLambdaSmall hbudget hL hU hsource havoid hp himage hlen
  have hheight' : |(N.coordinate_inverse y1).2 - c| < 2 * L / 3 := by
    simpa only [y0, y1, c] using hheight
  have hbounds := abs_lt.mp hheight'
  have hlow : c - 2 * L / 3 < (N.coordinate_inverse y1).2 := by
    linarith only [hbounds.1]
  have hhigh : (N.coordinate_inverse y1).2 < c + 2 * L / 3 := by
    linarith only [hbounds.2]
  exact ⟨hy1.1, hlow, hhigh⟩

end PoincareConjecture.M47

import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

open scoped Topology

namespace PoincareConjecture.M10

theorem lowerSemicontinuousAt_of_compact_lifts
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {l : X → ℝ} {x : X} {Q : Set X} (hQ : Q ∈ 𝓝 x)
    {K : Set Y} (hK : IsCompact K) {endpoint : Y → X} {cost : Y → ℝ}
    (hendpoint : ContinuousOn endpoint K) (hcost : ContinuousOn cost K)
    (hrealizes : ∀ z ∈ Q, ∃ w ∈ K, endpoint w = z ∧ cost w = l z)
    (hcomparison : ∀ w ∈ K, endpoint w = x → l x ≤ cost w) :
    LowerSemicontinuousAt l x := by
  intro c hc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set K := {w | cost w ≤ c}
  have hS : IsCompact S :=
    (isClosed_le hcost.domRestrict continuous_const).isCompact
  have hclosed : IsClosed ((fun w : K ↦ endpoint w) '' S) :=
    (hS.image hendpoint.domRestrict).isClosed
  have hx : x ∈ ((fun w : K ↦ endpoint w) '' S)ᶜ := by
    rintro ⟨w, hw, hwx⟩
    exact (not_le_of_gt hc) ((hcomparison w w.property hwx).trans hw)
  filter_upwards [hQ, hclosed.isOpen_compl.mem_nhds hx] with z hz hzoutside
  by_contra hzle
  obtain ⟨w, hw, hwz, hwl⟩ := hrealizes z hz
  apply hzoutside
  exact ⟨⟨w, hw⟩, by simpa only [S, Set.mem_ofPred_eq, hwl] using le_of_not_gt hzle, hwz⟩

end PoincareConjecture.M10

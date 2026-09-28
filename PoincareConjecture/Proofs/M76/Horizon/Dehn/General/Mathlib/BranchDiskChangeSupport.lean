import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Basic










set_option autoImplicit false

open Set Metric Topology

namespace Geometry

local notation "V3" => (Fin 3 → ℝ)


theorem branch_disk_change_support
    {X ι : Type*} [TopologicalSpace X]
    (T : OpenPartialHomeomorph X V3) (A : Set X) (J K P : Set V3)
    (ρ : ℝ) (hclosed : closedBall (0 : V3) ρ ⊆ interior J)
    (hJT : J ⊆ T.target)
    (hK : K = T '' (A ∩ T.source) ∩ J)
    (hP : P = K \ ball (0 : V3) ρ)
    (G : ι → X → X)
    (hout : ∀ u, EqOn (G u) id (T.symm '' J)ᶜ)
    (hprotected : ∀ u, EqOn (G u) id (T.symm '' P)) :
    IsCompact (T.symm '' closedBall (0 : V3) ρ) ∧
      T.symm '' closedBall (0 : V3) ρ ⊆ T.symm '' interior J ∧
      ∀ u, EqOn (G u) id (A \ T.symm '' closedBall (0 : V3) ρ) := by
  have hballTarget : closedBall (0 : V3) ρ ⊆ T.target :=
    hclosed.trans (interior_subset.trans hJT)
  refine ⟨(isCompact_closedBall (0 : V3) ρ).image_of_continuousOn
    (T.continuousOn_symm.mono hballTarget), image_mono hclosed, ?_⟩
  intro u x hx
  by_cases hxJ : x ∈ T.symm '' J
  · obtain ⟨z, hzJ, rfl⟩ := hxJ
    have hzT := hJT hzJ
    have hzK : z ∈ K := hK.symm.subset
      ⟨⟨T.symm z, ⟨hx.1, T.map_target hzT⟩, T.right_inv hzT⟩, hzJ⟩
    have hzOutside : z ∉ ball (0 : V3) ρ :=
      fun hz ↦ hx.2 ⟨z, ball_subset_closedBall hz, rfl⟩
    exact hprotected u ⟨z, hP.symm.subset ⟨hzK, hzOutside⟩, rfl⟩
  · exact hout u hxJ

end Geometry


import PoincareConjecture.Proofs.M76.Dehn.OriginalBranchCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.InjectiveRegionCharts










set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}




theorem Stage.plDomain_region (s : Stage e S f r C) {R : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) :
    PoincareConjecture.M76.PLDomain s.charts (s.projection ⁻¹' R) :=
  ⟨s.cover, s.compatible, he.closed.preimage s.projection.continuous,
    s.halfspace_boundary he.halfspace⟩




theorem Step.exists_original_region_branch_chart
    {s t : Stage e S f r C} (step : Step s t) {R : Set M}
    (he : PoincareConjecture.M76.PLDomain e R)
    {x : t.Carrier} (hxR : x ∈ t.projection ⁻¹' R)
    {W : Set t.Carrier} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ Q : OpenPartialHomeomorph t.Carrier V3,
      x ∈ Q.source ∧ Q.source ⊆ W ∧
      InjOn (step.projection ∘ step.inclusion) Q.source ∧
      (∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
      (Q.source ⊆ interior (t.projection ⁻¹' R) ∨
        ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ell (Q x) = 0 ∧
          (∀ y ∈ Q.source, y ∈ t.projection ⁻¹' R ↔ 0 ≤ ell (Q y)) ∧
          ∀ y ∈ Q.source, y ∈ frontier (t.projection ⁻¹' R) ↔ ell (Q y) = 0) :=
  (t.plDomain_region he).exists_injective_region_chart
    step.projectionInclusion_local.isLocallyInjective hxR hW hxW

end Geometry.OriginalPLTower

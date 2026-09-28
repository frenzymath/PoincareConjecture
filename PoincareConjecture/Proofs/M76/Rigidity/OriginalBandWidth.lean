import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.exists_prescribed_band_width
    (P : OriginalDiskProduct e R j) (hR : IsClosed R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹'
      (P.map '' (D ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))))
    (F : E → X) (hF : ContinuousOn F (Q ×ˢ I))
    (hfront : MapsTo F (Q ×ˢ I) (frontier R))
    (hcenter : ∀ z ∈ Q, F (z, 0) = j z) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧
      MapsTo F (Q ×ˢ Icc (-a) a)
        (P.map '' (D ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2))) := by
  let f : Q × I → R := fun z =>
    ⟨F ((z.1 : V2), (z.2 : ℝ)), hR.frontier_subset (hfront ⟨z.1.property, z.2.property⟩)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact hF.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨z.1.property, z.2.property⟩)
  have hzero (z : Q) : f (z, ⟨0, by norm_num⟩) ∈
      (Subtype.val : R → X) ⁻¹'
        (P.map '' (D ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2))) := by
    exact ⟨((z : V2), 0), ⟨sphere_subset_closedBall z.property, by norm_num⟩,
      (P.central z (sphere_subset_closedBall z.property)).trans (hcenter z z.property).symm⟩
  let : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V2) 1)
  obtain ⟨a, ha, hasmall, hband⟩ := hf.exists_closed_strip_subset hopen hzero
  refine ⟨a, ha, hasmall, ?_⟩
  intro z hz
  have ht : z.2 ∈ I := ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  exact hband ⟨z.1, hz.1⟩ ⟨z.2, ht⟩ (abs_le.mpr hz.2)

end PoincareConjecture.M76

import PoincareConjecture.Proofs.M76.Dehn.OriginalCompactPairModel
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDomination
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X}




theorem PLDomain.exists_le_pos_mul (he : PLDomain e R) (hR : IsCompact R)
    {f g : X → ℝ}
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hg : ∀ i, LocallyPiecewiseAffineOn (g ∘ (e i).symm) (e i).target)
    (hgnonneg : ∀ x ∈ R, 0 ≤ g x)
    (hzero : ∀ x ∈ R, g x = 0 → f x ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ R, f x ≤ C * g x := by
  classical
  by_cases hne : R.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨s, G, D, P, Z, H, _, hRD, hP, _, _, _, _, _, hH, _, hcharts⟩ :=
      OpenPartialHomeomorph.exists_compact_original_PL_pair_model e he.compatible
        he.cover he.closed hR (Subset.rfl : R ⊆ R) he.halfspace
    have hRD' : R ⊆ D := hRD.trans interior_subset
    let q : ((s → ℝ × V3) × ℝ) → X := fun z =>
      if hz : z ∈ P.space then (H.symm ⟨z, hz⟩ : X) else x₀
    have hq (z : P.space) : q z = (H.symm z : X) := dif_pos z.property
    have hqc : ContinuousOn q P.space := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      exact (continuous_subtype_val.comp H.symm.continuous).congr (fun z => (hq z).symm)
    have hqD : MapsTo q P.space D := by
      intro z hz
      rw [hq ⟨z, hz⟩]
      exact (H.symm ⟨z, hz⟩).property.1
    have hqR : MapsTo q P.space R := by
      intro z hz
      rw [hq ⟨z, hz⟩]
      exact (H.symm ⟨z, hz⟩).property.2
    have hGq : EqOn (G ∘ q) id P.space := by
      intro z hz
      change G (q z) = z
      rw [hq ⟨z, hz⟩, ← hH (H.symm ⟨z, hz⟩), H.apply_symm_apply]
    have hqPL : PolyhedralPLInCharts e q P.space :=
      polyhedralPLInCharts_of_affine_projections e G D hcharts P hP hqc hqD
        ((P.affineOnFaces_affine (ContinuousAffineMap.id ℝ _)).finitePiecewiseAffineOn hP) hGq
    have hfq := hqPL.finitePiecewiseAffineOn_comp P hP hf
    have hgq := hqPL.finitePiecewiseAffineOn_comp P hP hg
    obtain ⟨C, hC, hbound⟩ := hfq.exists_le_pos_mul hgq
      (fun z hz => hgnonneg (q z) (hqR hz))
      (fun z hz => hzero (q z) (hqR hz))
    refine ⟨C, hC, ?_⟩
    intro x hx
    let y : (D ∩ R : Set X) := ⟨x, hRD' hx, hx⟩
    have hqx : q (H y) = x := by rw [hq (H y), H.symm_apply_apply]
    simpa only [Function.comp_apply, hqx] using hbound (H y) (H y).property
  · exact ⟨1, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩

end PoincareConjecture.M76

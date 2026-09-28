import PoincareConjecture.Proofs.M76.Mathlib.TaperedSourceIncidence
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension










set_option autoImplicit false

open Set Geometry AffineMap

namespace TaperedStrip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_affine_segmentDomain_roof {q w : E} (hqw : q ≠ w)
    {β : ℝ} (hβ : 0 < β) :
    ∃ a : E →ᴬ[ℝ] ℝ, a q = 0 ∧ a w = β ∧
      (∀ x ∈ segment ℝ q w, a x ∈ Icc 0 β) ∧
      segmentDomain q w β = {p : E × ℝ | p.1 ∈ segment ℝ q w ∧ p.2 ∈ Icc 0 (a p.1)} := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℝ (sub_ne_zero.mpr hqw.symm)
  let a : E →ᴬ[ℝ] ℝ := β • ((LinearMap.toContinuousLinearMap l).toContinuousAffineMap.comp
    (ContinuousAffineMap.id ℝ E - ContinuousAffineMap.const ℝ E q))
  have hval (x : E) : a x = β * l (x - q) := rfl
  have hline (s : ℝ) : a (lineMap q w s) = β * s := by
    rw [hval, lineMap_apply_module', add_sub_cancel_right, map_smul, hl]
    simp only [smul_eq_mul, mul_one]
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · rw [hval, sub_self, map_zero, mul_zero]
  · rw [hval, hl, mul_one]
  · intro x hx
    rw [segment_eq_image_lineMap] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    rw [hline]
    exact ⟨mul_nonneg hβ.le hs.1, mul_le_of_le_one_right hβ.le hs.2⟩
  · ext p
    rw [mem_segmentDomain_iff hβ]
    constructor
    · rintro ⟨s, hs, hbase, ht⟩
      refine ⟨hbase ▸ lineMap_mem_segment ℝ q w hs, ?_⟩
      rwa [hbase, hline]
    · rintro ⟨hx, ht⟩
      rw [segment_eq_image_lineMap] at hx
      obtain ⟨s, hs, hlinep⟩ := hx
      refine ⟨s, hs, hlinep.symm, ?_⟩
      simpa only [← hlinep, hline] using ht

end TaperedStrip

import PoincareConjecture.Definitions.Ch01.RiemannianMetric

set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in

theorem riemannianEDist_le_of_normed_differential_bound
    (g : RiemannianMetric n M) {f : E → M}
    {S : Set E} (hS : Convex ℝ S) (hSopen : IsOpen S)
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) 1 f S) {C : ℝ≥0}
    (hbound : ∀ x ∈ S, ∀ v : E,
      g.tangentNorm (f x) (mfderiv 𝓘(ℝ, E) (𝓡 n) f x v) ≤ C * ‖v‖)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    g.edist (f x) (f y) ≤ (C : ℝ≥0∞) * edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let η := ContinuousAffineMap.lineMap (R := ℝ) x y
  have hη : MapsTo η (Icc 0 1) S := by
    apply mapsTo_iff_image_subset.mpr
    simpa only [η, ContinuousAffineMap.coe_lineMap_eq, ← segment_eq_image_lineMap] using
      hS.segment_subset hx hy
  have hηsmooth : ContMDiff (𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 1 η := η.contDiff.contMDiff
  have hpath : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (f ∘ η) (Icc 0 1) :=
    hf.comp hηsmooth.contMDiffOn hη
  have hdist : g.edist (f x) (f y) ≤ Manifold.pathELength (𝓡 n) (f ∘ η) 0 1 :=
    Manifold.riemannianEDist_le_pathELength hpath
      (by simp [η, ContinuousAffineMap.coe_lineMap_eq])
      (by simp [η, ContinuousAffineMap.coe_lineMap_eq]) zero_le_one
  apply hdist.trans
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_fderiv_lineMap_eq_edist,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hft := (hf.contMDiffAt (hSopen.mem_nhds (hη ht))).mdifferentiableAt one_ne_zero
  have hchain := mfderiv_comp_mfderivWithin t hft
    (hηsmooth.mdifferentiable one_ne_zero t).mdifferentiableWithinAt
    ((uniqueMDiffWithinAt_iff_uniqueDiffWithinAt).mpr (uniqueDiffOn_Icc zero_lt_one t ht))
  rw [hchain]
  change ‖mfderiv 𝓘(ℝ, E) (𝓡 n) f (η t)
    (mfderivWithin (𝓘(ℝ, ℝ)) 𝓘(ℝ, E) η (Icc 0 1) t 1)‖ₑ ≤ _
  rw [mfderivWithin_eq_fderivWithin]
  let v := fderivWithin ℝ η (Icc 0 1) t 1
  have h := ENNReal.ofReal_le_ofReal (hbound (η t) (hη ht) v)
  have hvnorm : ‖mfderiv 𝓘(ℝ, E) (𝓡 n) f (η t) v‖ =
      g.tangentNorm (f (η t)) (mfderiv 𝓘(ℝ, E) (𝓡 n) f (η t) v) :=
    norm_eq_sqrt_real_inner _
  rw [← hvnorm, ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ofReal_norm, ofReal_norm] at h
  exact h

end PoincareConjecture.M10

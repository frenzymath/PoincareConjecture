import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Lipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity.LocalDistance









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem one_le_gradient_norm_of_calibrated_spheres (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hcal : ∀ r : ℝ, 0 < r → ∃ y : M,
      g.edist x y = ENNReal.ofReal r ∧ f y = f x + r) :
    1 ≤ g.tangentNorm x (D.gradient f x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  by_contra h
  obtain ⟨C, hCgrad, hC1⟩ := exists_between (lt_of_not_ge h)
  have hC0 : 0 < C := (Real.sqrt_nonneg _).trans_lt hCgrad
  let K : ℝ≥0 := ⟨C, hC0.le⟩
  let s : Set M := {z | g.tangentNorm z (D.gradient f z) < C}
  have hcont : Continuous (fun z => g.tangentNorm z (D.gradient f z)) :=
    g.continuous_tangentNorm_gradient hf
  have hs : s ∈ 𝓝 x := (isOpen_lt hcont continuous_const).mem_nhds hCgrad
  have hbound (z : M) (hz : z ∈ s) :
      ‖mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f z‖ₑ ≤ K := by
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    apply ContinuousLinearMap.opNorm_le_bound _ hC0.le
    intro v
    change ‖mvfderiv (𝓡 n) f z v‖ ≤ C * g.tangentNorm z v
    rw [Real.norm_eq_abs]
    exact (D.abs_mvfderiv_le_gradient_norm f z v).trans
      (mul_le_mul_of_nonneg_right hz.le (Real.sqrt_nonneg _))
  obtain ⟨V, hV, _, hLip⟩ :=
    Poincare.exists_nhds_edist_le_mul_riemannianEDist_of_mfderiv_le
      (I := 𝓡 n) hs (fun z _ => (hf z).of_le (by simp))
      (show 0 < K from hC0) hbound
  obtain ⟨r, hr, hrV⟩ := setOfPred_riemannianEDist_lt_subset_nhds (𝓡 n) hV
  have hr0 : 0 < (r : ℝ) / 2 := by exact div_pos hr (by norm_num)
  obtain ⟨y, hxy, hfy⟩ := hcal ((r : ℝ) / 2) hr0
  have hyV : y ∈ V := by
    apply hrV
    change g.edist x y < (r : ℝ≥0∞)
    rw [hxy, ← ENNReal.ofReal_coe_nnreal]
    apply (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hr)).mpr
    linarith
  have hdist := hLip x (mem_of_mem_nhds hV) y hyV
  change EDist.edist (f x) (f y) ≤ (K : ℝ≥0∞) * g.edist x y at hdist
  rw [hxy] at hdist
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hdist
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal hr0.le, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg, Real.dist_eq, hfy] at hreal
  have habs : |f x - (f x + (r : ℝ) / 2)| = (r : ℝ) / 2 := by
    rw [sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg, abs_of_pos hr0]
  rw [habs] at hreal
  change (r : ℝ) / 2 ≤ C * ((r : ℝ) / 2) at hreal
  nlinarith



theorem gradient_normSq_eq_one_of_distance_lipschitz_of_calibrated_spheres
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal) {x : M}
    (hcal : ∀ r : ℝ, 0 < r → ∃ y : M,
      g.edist x y = ENNReal.ofReal r ∧ f y = f x + r) :
    g.inner x (D.gradient f x) (D.gradient f x) = 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnorm := D.gradient_norm_le_of_distance_lipschitz (C := 1)
    (by norm_num) (by simpa only [one_mul] using hLip)
    ((hf x).mdifferentiableAt (by simp))
  have heq := le_antisymm hnorm (D.one_le_gradient_norm_of_calibrated_spheres hf hcal)
  change ‖D.gradient f x‖ = 1 at heq
  change inner ℝ (D.gradient f x) (D.gradient f x) = 1
  rw [real_inner_self_eq_norm_sq, heq, one_pow]

end PoincareConjecture.LeviCivitaData

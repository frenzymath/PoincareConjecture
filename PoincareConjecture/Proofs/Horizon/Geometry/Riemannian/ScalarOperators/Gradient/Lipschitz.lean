import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.InitialData







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem gradient_norm_le_of_eventual_distance_bound (D : LeviCivitaData g)
    {f : M → ℝ} {C : ℝ} {x : M} (hC : 0 ≤ C)
    (hLip : ∀ᶠ y in 𝓝 x, |f x - f y| ≤ C * (g.edist x y).toReal)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) :
    g.tangentNorm x (D.gradient f x) ≤ C := by
  apply (D.gradient_norm_le_iff f x hC).mpr
  intro v
  obtain ⟨δ, hδ, _, γ, hγ, hp, hv⟩ := g.exists_geodesic_initial_data x v
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := by constructor <;> linarith
  have hγd := (hγ.contMDiffOn.contMDiffAt (isOpen_Ioo.mem_nhds h0)).mdifferentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  subst x
  have hchart := (mdifferentiableAt_extChartAt (I := 𝓡 n)
    (mem_chart_source _ (γ 0)))
  have heq := congrArg (fun L => L 1) (mfderiv_comp 0 hchart hγd)
  rw [mfderiv_eq_fderiv] at heq
  change deriv (fun t => extChartAt (𝓡 n) (γ 0) (γ t)) 0 = _ at heq
  rw [hv.deriv] at heq
  rw [mfderiv_extChartAt_self] at heq
  change v = mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1 at heq
  have hd := (hf.hasMFDerivAt.comp 0 hγd.hasMFDerivAt).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun t => f (γ t))
    (mvfderiv (𝓡 n) f (γ 0) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ 0 1)) 0 at hd
  rw [← heq] at hd
  have hnorm := (hγ.tangentNorm_initial h0 rfl hv).symm
  rw [← heq] at hnorm
  apply hd.le_of_lip' (C := C * g.tangentNorm (γ 0) v)
    (mul_nonneg hC (Real.sqrt_nonneg _))
  filter_upwards [isOpen_Ioo.mem_nhds h0, hγd.continuousAt.eventually hLip]
    with t ht htLip
  have hdist := hγ.edist_le_initial_speed h0 rfl hv ht
  rw [hnorm] at hdist
  have hdist' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top) hdist
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (show 0 ≤ g.tangentNorm (γ 0) v from
    Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (abs_nonneg _)] at hdist'
  simpa only [Real.norm_eq_abs, sub_zero, abs_sub_comm, mul_assoc] using
    htLip.trans (mul_le_mul_of_nonneg_left hdist' hC)



theorem gradient_norm_le_of_distance_lipschitz (D : LeviCivitaData g)
    {f : M → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ x y, |f x - f y| ≤ C * (g.edist x y).toReal)
    {x : M} (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) :
    g.tangentNorm x (D.gradient f x) ≤ C :=
  D.gradient_norm_le_of_eventual_distance_bound hC (Eventually.of_forall (hLip x)) hf

end PoincareConjecture.LeviCivitaData

import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.JacobiPairing
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Jacobi.ManifoldComparison
import Mathlib.Analysis.Calculus.MeanValue











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.ManifoldJacobi

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem manifold_jacobi_half_inner_one_lower_bound
    (D : LeviCivitaData g) {q : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {K c : ℝ}
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) J) t)
    (hsub : Icc 0 1 ⊆ I)
    (hjac : ∀ t ∈ I, manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 t =
      -D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1))
    (hK : ∀ t ∈ Icc 0 1, D.curvatureTensorNorm (q t) ≤ K)
    (hc : ∀ t ∈ Icc 0 1, g.tangentNorm (q t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) = c)
    (hcr : c ≤ Poincare.ODE.Jacobi.comparisonRadius K / 4) (hJ0 : J 0 = 0) :
    g.tangentNorm (q 0) (manifoldCovDerivAlong g q J 1 0) ^ 2 / 2 ≤
      g.inner (q 1) (manifoldCovDerivAlong g q J 1 1) (J 1) := by
  have h01 : (0 : ℝ) < 1 := by norm_num
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans (hK 0 hzero)
  have hc0 : 0 ≤ c := by rw [← hc 0 hzero]; exact Real.sqrt_nonneg _
  have hfour : 4 * c ≤ Poincare.ODE.Jacobi.comparisonRadius K := by linarith
  have hcoeff : K * c ^ 2 ≤ 1 / 16 := by
    have h := Poincare.ODE.Jacobi.curvature_mul_sq_le_one_of_le_comparisonRadius
      hK0 (by positivity : 0 ≤ 4 * c) hfour
    nlinarith only [h]
  obtain ⟨P, hP0, hPi, hP, hpair, hestimate⟩ :=
    manifold_jacobi_estimates D h01 hI hq hJ hsub hjac hK hc hJ0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (q 0)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) (q 0)
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) (q 0) :=
    (show EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] TangentSpace (𝓡 n) (q 0) from
      LinearEquiv.refl ℝ _).toContinuousLinearEquiv
  let y := fun s => e ((P s).inverse (J s))
  let v := fun s => e ((P s).inverse (manifoldCovDerivAlong g q J 1 s))
  let v' := fun s => e ((P s).inverse
    (manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 s))
  have henorm (u : EuclideanSpace ℝ (Fin n)) : ‖e u‖ = g.tangentNorm (q 0) u := by
    change ‖e u‖ = Real.sqrt (inner ℝ (e u) (e u))
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hinvnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (u : EuclideanSpace ℝ (Fin n)) :
      ‖e ((P t).inverse u)‖ = g.tangentNorm (q t) u := by
    rw [henorm]
    have hp := hpair t ht ((P t).inverse u) ((P t).inverse u)
    rw [(hPi t ht).self_apply_inverse] at hp
    exact congrArg Real.sqrt hp.symm
  have hv0 : ‖v 0‖ = g.tangentNorm (q 0) (manifoldCovDerivAlong g q J 1 0) :=
    hinvnorm 0 hzero _
  have hvderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt v (v' t) t := by
    have hqt := hq.contMDiffAt (hI.mem_nhds (hsub ht))
    have hDJ := contDiffAt_chartField_covDeriv g hI hq hJ (hsub ht) (mem_extChartAt_source _)
    exact e.hasFDerivAt.comp_hasDerivAt t
      (inverse_manifold_parallel_hasDerivAt g h01 ht hPi hqt (hP t ht)
        (hDJ.differentiableAt (by simp)))
  have hjnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g.tangentNorm (q t) (J t) ≤ 3 * ‖v 0‖ / 2 := by
    have hs := Poincare.ODE.Jacobi.quarter_comparisonRadius_pairing_smallness hK0 hc0 hcr ht
    have hs' : K * c ^ 2 * Real.exp (max 1 (K * c ^ 2) * 1) * t ^ 2 ≤ 3 := by
      simpa only [mul_one] using hs.trans (by norm_num : (1 : ℝ) / 4 ≤ 3)
    have hj := ((hestimate t ht).2 hs').2
    rw [← hv0] at hj
    nlinarith [mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (v 0))]
  have hv'bound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖v' t‖ ≤ ‖v 0‖ / 8 := by
    dsimp only [v']
    rw [hjac t (hsub ht), map_neg, map_neg, norm_neg, hinvnorm t ht]
    have hn := curvature_norm_le D (q t) (J t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
    rw [hc t ht] at hn
    have hcurv : g.tangentNorm (q t)
        (D.curvature (q t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q t 1)) ≤
        (K * c ^ 2) * g.tangentNorm (q t) (J t) := by
      calc
        _ ≤ D.curvatureTensorNorm (q t) * g.tangentNorm (q t) (J t) * c * c := hn
        _ = (D.curvatureTensorNorm (q t) * c ^ 2) * g.tangentNorm (q t) (J t) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hK t ht) (sq_nonneg c)) (Real.sqrt_nonneg _)
    have h := mul_le_mul hcoeff (hjnorm t ht) (Real.sqrt_nonneg _) (by norm_num)
    nlinarith [hcurv, h, norm_nonneg (v 0)]
  have hvrem : ‖v 1 - v 0‖ ≤ ‖v 0‖ / 8 := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t ht => (hvderiv t ht).hasDerivWithinAt)
      (fun t ht => hv'bound t (Ico_subset_Icc_self ht))
    exact h
  have hyrem : ‖y 1 - (1 : ℝ) • v 0‖ ≤ 1 * ‖v 0‖ / 8 := by
    have hrem := (hestimate 1 hone).1
    have heq : y 1 - (1 : ℝ) • v 0 =
        e ((P 1).inverse (J 1) -
          (show EuclideanSpace ℝ (Fin n) from manifoldCovDerivAlong g q J 1 0)) := by
      simp only [y, v, hP0, ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply,
        map_sub, one_smul]
    rw [heq, henorm]
    simp only [one_smul, one_pow, mul_one] at hrem
    rw [← hv0] at hrem
    have hs := Poincare.ODE.Jacobi.quarter_comparisonRadius_pairing_smallness hK0 hc0 hcr hone
    simp only [one_pow, mul_one] at hs
    have h := mul_le_mul_of_nonneg_right hs (norm_nonneg (v 0))
    nlinarith [hrem, h, norm_nonneg (v 0)]
  have h := Poincare.ODE.Jacobi.inner_ge_half_of_remainders zero_le_one hvrem hyrem
  have hipair : inner ℝ (v 1) (y 1) =
      g.inner (q 1) (manifoldCovDerivAlong g q J 1 1) (J 1) := by
    change g.inner (q 0) ((P 1).inverse (manifoldCovDerivAlong g q J 1 1))
      ((P 1).inverse (J 1)) = _
    rw [← hpair 1 hone, (hPi 1 hone).self_apply_inverse, (hPi 1 hone).self_apply_inverse]
  simpa only [one_mul, hv0, hipair] using h

end PoincareConjecture.ManifoldJacobi

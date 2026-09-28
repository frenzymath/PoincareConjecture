import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Level
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.ProductIsometry









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric


theorem exists_curvatureTensor_ne_zero_of_scalar_pos
    {k : ℕ} {P : Type*} [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) P] [IsManifold (𝓡 k) ∞ P]
    {metric : RiemannianMetric k P} (D : LeviCivitaData metric) (p : P)
    (hp : 0 < D.scalarCurvature p) :
    ∃ u v w z : TangentSpace (𝓡 k) p, D.curvatureTensor p u v w z ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hs : D.scalarCurvature p = 0 := by
    simp only [LeviCivitaData.scalarCurvature, LeviCivitaData.ricci, hn, Finset.sum_const_zero]
  linarith

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] {g : RiemannianMetric (n + 1) M}




theorem exists_parallelGradient_productIsometry_curvature [ConnectedSpace M]
    {D : LeviCivitaData g} {f : M → ℝ} (hc : MetricComplete g)
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    let h := regularLevelMetric hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    let Dh := h.leviCivitaData
    Nonempty (zeroLevelSet f) ∧ ConnectedSpace (zeroLevelSet f) ∧ MetricComplete h ∧
    ∃ Φ : ℝ → M → M,
      ∃ e : (zeroLevelSet f × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M,
        (∀ x, Φ 0 x = x) ∧
        (∀ x, IsMIntegralCurve (fun t => Φ t x) (D.gradient f)) ∧
        (∀ z, e z = Φ z.2 (zeroLevelIncl f z.1)) ∧
        (∀ z, f (e z) = z.2) ∧
        (∀ (z : zeroLevelSet f × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
          g.inner (e z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z v)
            (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z w) =
              h.inner z.1 v.1 w.1 + v.2 * w.2) ∧
        (∀ p, Dh.scalarCurvature (e.symm p).1 = D.scalarCurvature p) ∧
        (∀ p, Dh.curvatureTensorNorm (e.symm p).1 = D.curvatureTensorNorm p) ∧
        ((∀ p, D.NonnegativeCurvatureOperator p) → ∀ y, Dh.NonnegativeCurvatureOperator y) ∧
        (∀ K : ℝ, (∀ p, D.curvatureTensorNorm p ≤ K) → ∀ y, Dh.curvatureTensorNorm y ≤ K) ∧
        (∀ p, 0 < D.scalarCurvature p → 0 < Dh.scalarCurvature (e.symm p).1) ∧
        (∀ p, 0 < D.scalarCurvature p →
          ∃ u v w z : TangentSpace (𝓡 n) (e.symm p).1,
            Dh.curvatureTensor (e.symm p).1 u v w z ≠ 0) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  let h := regularLevelMetric hf (⊤ : Opens M) hreg 0 g
  let Dh := h.leviCivitaData
  obtain ⟨hne, hconn, hcomplete, Φ, e, h0, hΦ, hs, he, hfe, hm, ht, hlevel⟩ :=
    exists_parallelGradient_productIsometry hc hf hu hz
  have hfactor := parallelGradient_factor_curvature hf hu hz
  have hFs (t : ℝ) : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (Φ t) :=
    hs.comp (contMDiff_const.prodMk contMDiff_id)
  have hmetric (t : ℝ) (x : M) (u v : TangentSpace (𝓡 (n + 1)) x) :
      g.inner x u v = g.inner (Φ t x)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (Φ t) x u)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (Φ t) x v) :=
    (gradientFlow_preserves_metric hf hz hs hΦ h0 t x u v).symm
  have hscalar (p : M) : Dh.scalarCurvature (e.symm p).1 = D.scalarCurvature p := by
    rw [(hfactor (e.symm p).1).2.2.2.1, hlevel]
    exact (D.scalarCurvature_eq_of_local_isometry D isOpen_univ (hFs (-f p)).contMDiffOn
      (fun x _ => hmetric (-f p) x) (mem_univ p)).symm
  have hnorm (p : M) : Dh.curvatureTensorNorm (e.symm p).1 = D.curvatureTensorNorm p := by
    rw [(hfactor (e.symm p).1).2.2.2.2.1, hlevel]
    exact (D.curvatureTensorNorm_eq_of_local_isometry D isOpen_univ (hFs (-f p)).contMDiffOn
      (fun x _ => hmetric (-f p) x) (mem_univ p)).symm
  refine ⟨hne, hconn, hcomplete, Φ, e, h0, hΦ, he, hfe, hm, hscalar, hnorm, ?_, ?_, ?_, ?_⟩
  · intro hnonneg y
    exact (hfactor y).2.2.2.2.2 (hnonneg _)
  · intro K hbound y
    rw [(hfactor y).2.2.2.2.1]
    exact hbound _
  · intro p hp
    rw [hscalar]
    exact hp
  · intro p hp
    apply exists_curvatureTensor_ne_zero_of_scalar_pos Dh
    rw [hscalar]
    exact hp

end PoincareConjecture.RiemannianMetric

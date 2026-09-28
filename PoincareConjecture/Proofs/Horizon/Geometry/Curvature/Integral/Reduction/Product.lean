import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Volume.Measure
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.ThreeDimensional
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric
private theorem integral_product_halfCylinder
    {n : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [T3Space M] [T3Space P] [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) P] [IsManifold (𝓡 (n+1)) ∞ P]
    (g : RiemannianMetric n M) (G : RiemannianMetric (n+1) P)
    (e : (M × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n+1)⟯ P)
    (hmetric : ∀ (z : M × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
      G.inner (e z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) e z v)
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n+1)) e z w) =
        g.inner z.1 v.1 w.1 + v.2 * w.2)
    (u : P → ℝ) (v : M → ℝ) (hvalue : ∀ z : M × ℝ, u (e z) = v z.1)
    (S : Set M) :
    (∫ z in e '' (S ×ˢ Ioo (-(1/2 : ℝ)) (1/2)), u z ∂G.volumeMeasure) =
      ∫ x in S, v x ∂g.volumeMeasure := by
  rw [(g.measurePreserving_productIsometry G e hmetric).setIntegral_image_emb
    e.toHomeomorph.measurableEmbedding]
  simp_rw [hvalue]
  have hh := setIntegral_prod_mul (μ := g.volumeMeasure) (ν := volume)
    v (fun _ : ℝ => (1 : ℝ)) S (Ioo (-(1/2 : ℝ)) (1/2))
  norm_num at hh ⊢
  exact hh
end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RiemannianMetric
private theorem halfBall_pos_scalar_integral_le_of_product
    {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [T3Space M] [T3Space P] [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace P] [BorelSpace P] [PreconnectedSpace M] [PreconnectedSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P] [IsManifold (𝓡 3) ∞ P]
    (g : RiemannianMetric 2 M) (D : LeviCivitaData g)
    (G : RiemannianMetric 3 P) (DG : LeviCivitaData G)
    (e : (M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ P)
    (hmetric : ∀ (z : M × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      G.inner (e z) (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
        g.inner z.1 v.1 w.1 + v.2 * w.2)
    (hscalar : ∀ z : M × ℝ, DG.scalarCurvature (e z) = D.scalarCurvature z.1)
    (hc : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 2) x), -1 ≤ D.sectionalCurvature x v w)
    (hsecG : ∀ x (v w : TangentSpace (𝓡 3) x), -1 ≤ DG.sectionalCurvature x v w)
    (p : M) {C : ℝ}
    (hbound : (∫ z in G.ball (e (p,0)) 1, DG.scalarCurvature z ∂G.volumeMeasure) ≤ C) :
    (∫ x in g.ball p (1/2), max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      C + 2 * modelVolume 3 1 1 := by
  let : SecondCountableTopology M := g.secondCountableTopology
  have hcG := g.metricComplete_of_product_pullback G e hmetric hc
  have hiP := G.integrableOn_ball_of_continuous hcG
    ((continuous_const (y := (0 : ℝ))).sup DG.continuous_scalarCurvature) (e (p,0)) 1
  have hiR := G.integrableOn_ball_of_continuous hcG DG.continuous_scalarCurvature (e (p,0)) 1
  have hiC := G.integrableOn_ball_of_continuous hcG (continuous_const (y := (2 : ℝ))) (e (p,0)) 1
  have hshift (z : P) : max 0 (DG.scalarCurvature z) ≤ DG.scalarCurvature z + 2 := by
    have hs := D.scalarCurvature_lower_bound_of_sectionalCurvature_lower_bound
      (e.symm z).1 1 (hsec (e.symm z).1)
    have hid := hscalar (e.symm z)
    rw [e.apply_symm_apply] at hid
    norm_num at hs
    rw [hid]
    exact max_le (by linarith) (by linarith)
  have hP := integral_mono hiP (hiR.add hiC) hshift
  dsimp only [Pi.add_apply] at hP
  rw [integral_add hiR hiC, integral_const] at hP
  simp only [smul_eq_mul, measureReal_restrict_apply_univ] at hP
  have hv := G.volumeMeasure_real_ball_le_modelVolume_of_sectional_lower_bound
    (e (p,0)) (by norm_num : 1 ≤ 3) hcG DG hsecG (by norm_num : (0 : ℝ) < 1)
  have hvol : (∫ z in G.ball (e (p,0)) 1, max 0 (DG.scalarCurvature z) ∂G.volumeMeasure) ≤
      C + 2 * modelVolume 3 1 1 := by nlinarith
  rw [← integral_product_halfCylinder g G e hmetric
    (fun z => max 0 (DG.scalarCurvature z)) (fun x => max 0 (D.scalarCurvature x))
    (fun z => by rw [hscalar z])]
  exact (setIntegral_mono_set hiP (Filter.Eventually.of_forall (fun _ => le_max_left _ _))
    (Filter.Eventually.of_forall (g.product_half_cylinder_subset_ball G e hmetric p))).trans hvol

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RiemannianMetric
private theorem unitBall_scalar_integral_le_of_halfBall_pos_bound
    {M : Type*} [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ∞ M] (g : RiemannianMetric 2 M) (D : LeviCivitaData g)
    (hc : MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 2) x), -1 ≤ D.sectionalCurvature x v w)
    {C : ℝ}
    (hhalf : ∀ q : M, (∫ x in g.ball q (1/2), max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C)
    (p : M) :
    (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤
      (⌈modelVolume 2 1 3 / modelVolume 2 1 (1/4)⌉₊ : ℝ) * C := by
  have hP := (continuous_const (y := (0 : ℝ))).sup D.continuous_scalarCurvature
  obtain ⟨q, _, hq⟩ := g.exists_unitBall_integral_concentration p
    (by norm_num : 1 ≤ 2) (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hc D hsec hP (fun _ => le_max_left _ _)
  have hiR := g.integrableOn_ball_of_continuous hc D.continuous_scalarCurvature p 1
  have hiP := g.integrableOn_ball_of_continuous hc hP p 1
  have hle := (integral_mono hiR hiP (fun _ => le_max_right _ _)).trans hq
  norm_num at hle
  exact hle.trans (mul_le_mul_of_nonneg_left (hhalf q) (Nat.cast_nonneg _))
end PoincareConjecture.RiemannianMetric

universe u

theorem PoincareConjecture.exists_uniform_unitBall_scalar_integral_bound_two :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
        [IsManifold (𝓡 2) ∞ M]
        (g : PoincareConjecture.RiemannianMetric 2 M) (D : PoincareConjecture.LeviCivitaData g),
        PoincareConjecture.MetricComplete g →
        (∀ (x : M) (v w : TangentSpace (𝓡 2) x),
          -1 ≤ D.sectionalCurvature x v w) →
        ∀ p : M,
          (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C := by
  classical
  obtain ⟨C₃, hC₃, hthree⟩ := PoincareConjecture.exists_uniform_unitBall_scalar_integral_bound_three.{0}
  let B : ℝ := C₃ + 2 * PoincareConjecture.RiemannianMetric.modelVolume 3 1 1
  let N : ℕ := ⌈PoincareConjecture.RiemannianMetric.modelVolume 2 1 3 /
    PoincareConjecture.RiemannianMetric.modelVolume 2 1 (1/4)⌉₊
  have hB : 0 < B := by
    have hv := PoincareConjecture.RiemannianMetric.modelVolume_pos
      (by norm_num : 1 ≤ 3) (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1)
    dsimp [B]
    linarith
  refine ⟨(N : ℝ) * B + 1, by positivity, ?_⟩
  intro M _ _ _ _ _ _ g D hc hsec p
  apply g.scalar_integral_le_of_small_connected_bound D hc hsec ((N : ℝ) * B + 1) ?_ p
  intro Q _ _ _ _ _ _ _ h E hcQ hsecQ q
  let := PoincareConjecture.RiemannianMetric.lineProductChartedSpace (n := 2) (M := Q)
  let := PoincareConjecture.RiemannianMetric.lineProductIsManifold (n := 2) (M := Q)
  let G := h.lineProduct
  let DG := G.leviCivitaData
  let e := PoincareConjecture.RiemannianMetric.lineProductDiffeomorph (n := 2) (M := Q)
  have hmetric := h.lineProduct_inner
  have hcG := h.metricComplete_of_product_pullback G e hmetric hcQ
  have hsG := h.lineProduct_sectionalCurvature_lower_bound E hsecQ
  have hscalar := h.lineProduct_scalarCurvature E
  have hhalf (z : Q) :
      (∫ x in h.ball z (1/2), max 0 (E.scalarCurvature x) ∂h.volumeMeasure) ≤ B := by
    exact h.halfBall_pos_scalar_integral_le_of_product E G DG e hmetric hscalar hcQ hsecQ hsG z
      (hthree (Q × ℝ) G DG hcG hsG (e (z,0)))
  have hunit := h.unitBall_scalar_integral_le_of_halfBall_pos_bound E hcQ hsecQ hhalf q
  exact hunit.trans (le_add_of_nonneg_right (by norm_num))

import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.SlabBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Tensors
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [SecondCountableTopology M] [NoncompactSpace M] in
private theorem scalarCurvature_nonpos_of_bounded_smoothExhaustion
    (hC : RicciFlowCurvatureTheory.{u}) {T : ℝ} (F : RicciFlow n M (Icc 0 T))
    {O : M} (S : SmoothExhaustion F O) (hT : 0 ≤ T)
    (hcomplete : MetricComplete (F.metric 0))
    (hRic : ∀ t ∈ Icc 0 T, ∀ x (v : TangentSpace (𝓡 n) x),
      0 ≤ (F.connection t).ricci x v v)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x, (F.connection t).scalarCurvature x ≤ B)
    (hinit : ∀ x, (F.connection 0).scalarCurvature x ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → (F.connection t).scalarCurvature x ≤ 0 := by
  apply S.nonpos_of_heat_le_mul_of_metricComplete (show 0 ∈ Icc 0 T from ⟨le_rfl, hT⟩)
    hcomplete (u := fun x t => (F.connection t).scalarCurvature x)
    (du := fun x t => (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x) (C := 2 * B) (B := B)
    (by positivity) Subset.rfl
  · have hreg : ContinuousOn (fun z : ℝ × M => (F.connection z.1).scalarCurvature z.2)
        (Icc 0 T ×ˢ univ) := (hC.scalar_regular n M (Icc 0 T) F).continuousOn
    have hswap : Continuous (fun z : M × ℝ => (z.2, z.1)) :=
      continuous_snd.prodMk continuous_fst
    exact hreg.comp (f := fun z : M × ℝ => (z.2, z.1))
      hswap.continuousOn (fun z hz => ⟨hz.2, hz.1⟩)
  · intro t ht
    exact Poincare.RicciFlow.Harnack.scalarCurvature_contMDiff_slice hC _ F t ht
  · intro x t ht
    exact hC.scalar_evolution n M (Icc 0 T) F t ⟨ht.1.le, ht.2⟩ x
  · intro x t ht
    exact hbound t ht x
  · intro x t ht
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have hricci := (F.connection t).ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg
      (hC.tensor_calculus n M (F.metric t) (F.connection t)) x (hRic t ht' x)
    have hnonneg : 0 ≤ (F.connection t).scalarCurvature x :=
      Finset.sum_nonneg (fun i _ => hRic t ht' x _)
    have hreaction := mul_le_mul_of_nonneg_right (hbound t ht' x) hnonneg
    nlinarith
  · exact hinit

theorem scalarCurvature_terminal_nonpos_of_bounded_ancient_slice_nonpos
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {a : ℝ} (ha : a < 0)
    (hinit : ∀ x, (F.connection a).scalarCurvature x ≤ 0) :
    ∀ x, (F.connection 0).scalarCurvature x ≤ 0 := by
  classical
  have hshift : (fun t : ℝ => t + a) '' Icc 0 (-a) ⊆ Iic 0 := by
    rintro _ ⟨t, ht, rfl⟩
    change t + a ≤ 0
    linarith [ht.2]
  have hne : (Icc 0 (-a)).Nontrivial := by
    refine ⟨0, ⟨le_rfl, by linarith⟩, -a, ⟨by linarith, le_rfl⟩, ?_⟩
    linarith
  let G := F.translate a hshift ordConnected_Icc hne
  have hzero : (0 : ℝ) ∈ Icc 0 (-a) := ⟨le_rfl, by linarith⟩
  have hcompleteG : MetricComplete (G.metric 0) := by
    simpa only [G, translate, zero_add] using hcomplete a ha.le
  have hcurv (t : ℝ) (ht : t ∈ Icc 0 (-a)) (x : M) :
      (G.connection t).curvatureTensorNorm x ≤ K :=
    hbound (t + a) (by linarith [ht.2]) x
  have hoperatorG (t : ℝ) (ht : t ∈ Icc 0 (-a)) (x : M) :
      (G.connection t).NonnegativeCurvatureOperator x :=
    hoperator (t + a) (by linarith [ht.2]) x
  obtain ⟨C, hCpos, hderiv⟩ :=
    F.exists_curvatureDerivativeNorm_bound_on_buffered_slab hC
      (a := a - 1) (b := 0) (δ := 1) (K := K)
      (by linarith) (fun _ ht => ht.2) (by norm_num)
      (hcomplete _ (by linarith)) (fun t ht => hbound t ht.2) 1
  obtain ⟨B, _, hsmooth⟩ := RiemannianMetric.exists_uniform_smoothDistanceLike n hK
  let O : M := Classical.choice inferInstance
  obtain ⟨S, _⟩ := hsmooth (G.metric 0) (G.connection 0) hcompleteG (hcurv 0 hzero) O
  have hRicDeriv : ∀ t ∈ Icc 0 (-a), ∀ y (v w z : TangentSpace (𝓡 n) y),
      |(G.connection t).covariantTensorDerivative (G.connection t).ricciEvaluation
        y ![v, w, z]| ≤ (n : ℝ) * C * (G.metric t).tangentNorm y v *
          (G.metric t).tangentNorm y w * (G.metric t).tangentNorm y z := by
    intro t ht y v w z
    apply ((G.connection t).abs_covariantTensorDerivative_ricci_le_curvatureDerivativeNorm
      (hC.tensor_calculus n M (G.metric t) (G.connection t)) y v w z).trans
    have hd : (G.connection t).curvatureDerivativeNorm 1 y ≤ C :=
      hderiv (t + a) (by constructor <;> linarith [ht.1, ht.2]) y
    have hnorm (v : TangentSpace (𝓡 n) y) : 0 ≤ (G.metric t).tangentNorm y v :=
      Real.sqrt_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n))
        (hnorm v)) (hnorm w)) (hnorm z)
  let exhaustion := G.smoothExhaustionOfInitialOfCurvatureBound O 0 hzero S K
    ((n : ℝ) * C) (-a) hK (by positivity)
    (fun t ht => by simpa only [sub_zero, abs_of_nonneg ht.1] using ht.2)
    hcurv hRicDeriv
  have hscalar_bound (t : ℝ) (ht : t ∈ Icc 0 (-a)) (x : M) :
      (G.connection t).scalarCurvature x ≤ (n : ℝ) ^ 2 * K :=
    (le_abs_self _).trans (((G.connection t).abs_scalarCurvature_le_curvatureTensorNorm x).trans
      (mul_le_mul_of_nonneg_left (hcurv t ht x) (sq_nonneg _)))
  have hresult : ∀ x t, t ∈ Icc 0 (-a) → (G.connection t).scalarCurvature x ≤ 0 := by
    refine scalarCurvature_nonpos_of_bounded_smoothExhaustion hC G exhaustion
      (by linarith) hcompleteG ?_ (by positivity) hscalar_bound ?_
    · intro t ht x v
      exact ((G.connection t).ricci_bounds_of_nonnegative_curvatureOperator
        (hC.tensor_calculus n M (G.metric t) (G.connection t)) x (hoperatorG t ht x) v).1
    · intro x
      exact (congrArg (fun t => (F.connection t).scalarCurvature x ≤ 0) (zero_add a)).mpr
        (hinit x)
  intro x
  have hx := hresult x (-a) ⟨by linarith, le_rfl⟩
  change (F.connection (-a + a)).scalarCurvature x ≤ 0 at hx
  exact (congrArg (fun t => (F.connection t).scalarCurvature x ≤ 0) (neg_add_cancel a)).mp hx

theorem scalarCurvature_positive_somewhere_of_bounded_ancient
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hnonflat : ∃ p : M, 0 < (F.connection 0).scalarCurvature p) :
    ∀ a ≤ 0, ∃ x : M, 0 < (F.connection a).scalarCurvature x := by
  intro a ha
  rcases lt_or_eq_of_le ha with ha | rfl
  · by_contra hn
    push Not at hn
    obtain ⟨p, hp⟩ := hnonflat
    exact hp.not_ge (F.scalarCurvature_terminal_nonpos_of_bounded_ancient_slice_nonpos
      hC hcomplete hoperator hK hbound ha hn p)
  · exact hnonflat

end PoincareConjecture.RicciFlow

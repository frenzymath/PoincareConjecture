import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.ParallelGradient.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Nonflatness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Main













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

open RiemannianMetric



theorem exists_ancientKappaSolution_factor_of_minimizing_line
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hop : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ) (hnc : AncientKappaNoncollapsed F κ)
    (hscalar : ∃ p, 0 < (F.connection 0).scalarCurvature p)
    (γ : ℝ → M)
    (hγ : ∀ s t : ℝ, (F.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    let f := (F.metric 0).busemann γ
    letI : SecondCountableTopology M := (F.metric 0).secondCountableTopology
    ∃ (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
      (hu : HasUnitGradient (F.connection 0) f)
      (hz : HasZeroHessian (F.connection 0) f),
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 2 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 2 0
    ∃ hconn : ConnectedSpace (zeroLevelSet f),
    letI := hconn
    ∃ A : AncientKappaSolution 2 (zeroLevelSet f),
      A.flow = F.terminalParallelGradientFactor hC hc hop hK hbound hf hu hz ∧
      A.kappa = κ / 2 ∧
      ∃ e : (zeroLevelSet f × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
        (∀ z, f (e z) = z.2) ∧
        (∀ (t : ℝ), t ≤ 0 → ∀ (z : zeroLevelSet f × ℝ)
          (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          (F.metric t).inner (e z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
              (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
        (∀ (t : ℝ), t ≤ 0 → ∀ x,
          (A.flow.connection t).curvatureTensorNorm (e.symm x).1 =
            (F.connection t).curvatureTensorNorm x) := by
  let f := (F.metric 0).busemann γ
  let : SecondCountableTopology M := (F.metric 0).secondCountableTopology
  let : NoncompactSpace M := (F.metric 0).noncompactSpace_of_minimizing_line hγ
  have hRic : (F.connection 0).NonnegativeRicciCurvature := by
    intro x v
    exact ((F.connection 0).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus 3 M (F.metric 0) (F.connection 0)) x (hop 0 le_rfl x) v).1
  obtain ⟨hf, hu, _, hz, _⟩ := (F.metric 0).busemann_parallel_unit_gradient
    (F.connection 0) (hc 0 le_rfl) hRic hγ
  refine ⟨hf, hu, hz, ?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg 2 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg 2 0
  have hp := F.ancient_backward_persistence_of_parallel_gradient hC (by norm_num)
    hc hop ⟨K, hK, hbound⟩ f hf hu hz
  let huall := fun t ht => (hp t ht).2.1
  let hzall := fun t ht => (hp t ht).2.2
  let H := F.terminalParallelGradientFactor hC hc hop hK hbound hf hu hz
  obtain ⟨_, hconn, hcomplete, hoperator, hnorm, hpos⟩ :=
    F.parallelGradientFactor_geometry hf (show (0 : ℝ) ∈ Iic 0 by simp)
      huall hzall hc hop hbound
  refine ⟨hconn, ?_⟩
  let : ConnectedSpace (zeroLevelSet f) := hconn
  have hpast := F.scalarCurvature_positive_somewhere_of_bounded_ancient hC hc hop hK hbound hscalar
  have hnonflat : ∀ t ≤ 0, ∃ y, (H.connection t).curvatureTensorNorm y ≠ 0 := by
    intro t ht
    obtain ⟨x, hx⟩ := hpast t ht
    obtain ⟨y, hy⟩ := hpos t ht x hx
    refine ⟨y, ?_⟩
    intro hzero
    have hb := (H.connection t).abs_scalarCurvature_le_curvatureTensorNorm y
    rw [hzero, mul_zero] at hb
    exact hy.not_ge ((le_abs_self _).trans hb)
  let A : AncientKappaSolution 2 (zeroLevelSet f) :=
    { flow := H
      kappa := κ / 2
      kappa_pos := by positivity
      complete := hcomplete
      nonnegative_curvature_operator := hoperator
      bounded_curvature := fun t ht => ⟨K, hK, fun y => by
        have hnonneg : 0 ≤ (H.connection t).curvatureTensorNorm y := Real.sqrt_nonneg _
        rw [abs_of_nonneg hnonneg]
        exact hnorm t ht y⟩
      nonflat := hnonflat
      noncollapsed := F.terminalParallelGradientFactor_parabolic_noncollapsed
        hC hc hop hK hbound hf hu hz hnc }
  refine ⟨A, rfl, rfl, ?_⟩
  obtain ⟨_, _, _, Φ, e, h0, hΦ, he, hcoord, _, _, _, _⟩ :=
    exists_parallelGradient_productIsometry_curvature (n := 2) (hc 0 le_rfl) hf hu hz
  have hproduct (t : ℝ) (ht : t ≤ 0) :
      (∀ (z : zeroLevelSet f × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
        (F.metric t).inner (e z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
            (H.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
      (∀ x, (H.connection t).curvatureTensorNorm (e.symm x).1 =
        (F.connection t).curvatureTensorNorm x) := by
    obtain ⟨_, _, _, Ψ, d, hΨ0, hΨ, hd, _, hm, _, hn, _⟩ :=
      exists_parallelGradient_productIsometry_curvature (n := 2)
        (hc t ht) hf (huall t ht) (hzall t ht)
    have hde : d = e := by
      apply Diffeomorph.ext
      intro z
      rw [hd, he]
      have hcurve := hΨ (zeroLevelIncl f z.1)
      rw [(hp t ht).1] at hcurve
      have hsame := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
        ((F.connection 0).contMDiff_gradient hf |>.of_le (by simp)) hcurve
        (hΦ (zeroLevelIncl f z.1))
        (show Ψ 0 (zeroLevelIncl f z.1) = Φ 0 (zeroLevelIncl f z.1) by rw [hΨ0, h0])
      exact congrFun hsame z.2
    rw [hde] at hm hn
    exact ⟨hm, hn⟩
  exact ⟨e, hcoord, fun t ht => (hproduct t ht).1, fun t ht => (hproduct t ht).2⟩

end PoincareConjecture.RicciFlow

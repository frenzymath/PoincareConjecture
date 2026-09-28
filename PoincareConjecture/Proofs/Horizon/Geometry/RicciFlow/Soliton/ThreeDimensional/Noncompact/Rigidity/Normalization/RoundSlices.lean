import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.FactorNoncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.TerminalFactor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Main
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Classification
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Homothety
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

open RiemannianMetric

variable {M : Type u} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

def RiemannianMetric.HasCompactRoundParallelFactor (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) : Prop :=
  ∃ (f : M → ℝ) (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (_hz : HasZeroHessian D f),
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 2 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 2 0
    let h := regularLevelMetric hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    CompactSpace (zeroLevelSet f) ∧ ConstantPositiveSectionalCurvature h h.leviCivitaData

namespace RicciFlow

theorem exists_compact_round_parallel_factor_of_ancient_line
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (F : RicciFlow 3 M (Iic 0))
    (hc : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hop : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hb : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ≤ 0, ∀ x,
      (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : ∀ t ≤ 0,
      MetricKappaNoncollapsed (F.metric t) (F.connection t) κ)
    (hpos : ∀ t ≤ 0, ∀ x, 0 < (F.connection t).scalarCurvature x)
    (hline : ∃ γ : ℝ → M, ∀ s t : ℝ,
      (F.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    (F.metric 0).HasCompactRoundParallelFactor (F.connection 0) := by
  obtain ⟨γ, hγ⟩ := hline
  have hRic : (F.connection 0).NonnegativeRicciCurvature := by
    intro x v
    exact ((F.connection 0).ricci_bounds_of_nonnegative_curvatureOperator
      (hP.curvature.tensor_calculus 3 M (F.metric 0) (F.connection 0)) x
      (hop 0 le_rfl x) v).1
  obtain ⟨hf, hu, _, hz, _⟩ := (F.metric 0).busemann_parallel_unit_gradient
    (F.connection 0) (hc 0 le_rfl) hRic hγ
  let f := (F.metric 0).busemann γ
  refine ⟨f, hf, hu, hz, ?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hu x) 2 0
  let := isManifold_openLevelSet hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hu x) 2 0
  have hp := F.ancient_backward_persistence_of_parallel_gradient hP.curvature
    (by norm_num) hc hop hb f hf hu hz
  let hu' := fun t ht => (hp t ht).2.1
  let hz' := fun t ht => (hp t ht).2.2
  let H := F.parallelGradientFactor hf (show (0 : ℝ) ∈ Iic 0 by simp) hu' hz'
  obtain ⟨K, hK, hbound⟩ := hb
  have hg := F.parallelGradientFactor_geometry hf (show (0 : ℝ) ∈ Iic 0 by simp)
    hu' hz' hc hop hbound
  let : ConnectedSpace (zeroLevelSet f) := hg.2.1
  have hk := F.parallelGradientFactor_kappaNoncollapsed hf
    (show (0 : ℝ) ∈ Iic 0 by simp) hu' hz' hc hκ
  let A : AncientKappaSolution 2 (zeroLevelSet f) := {
    flow := H
    kappa := κ / 2
    kappa_pos := div_pos (hκ 0 le_rfl).1 (by norm_num)
    complete := hg.2.2.1
    nonnegative_curvature_operator := hg.2.2.2.1
    bounded_curvature := by
      intro t ht
      refine ⟨K, hK, fun y => ?_⟩
      rw [abs_of_nonneg (show 0 ≤ (H.connection t).curvatureTensorNorm y
        from Real.sqrt_nonneg _)]
      exact hg.2.2.2.2.1 t ht y
    nonflat := by
      intro t ht
      obtain ⟨y, hy⟩ := hg.2.2.2.2.2 t ht (γ 0) (hpos t ht (γ 0))
      refine ⟨y, fun hzero => ?_⟩
      have hsharp := (H.connection t).scalarCurvature_le_curvatureTensorNorm_sharp y
      rw [hzero, mul_zero] at hsharp
      exact (not_le_of_gt hy) hsharp
    noncollapsed := by
      intro r₀ hr₀ t ht y r hr hrr₀ hcurv
      apply (hk t ht).2 y r hr
      exact hcurv t ⟨by nlinarith [sq_pos_of_pos hr], le_rfl⟩ }
  obtain ⟨C⟩ := hP.two_dimensional.ancient_classification A
  exact ⟨C.compact, C.round_at_all_times 0 le_rfl⟩

theorem exists_compact_round_parallel_factor_of_line_at_each_time
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (F : RicciFlow 3 M (Iio 1))
    (hc : ∀ t < 1, MetricComplete (F.metric t))
    (hop : ∀ t < 1, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hb : ∀ T < 1, ∃ K : ℝ, 0 ≤ K ∧ ∀ t ≤ T, ∀ x,
      (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : ∀ t < 1,
      MetricKappaNoncollapsed (F.metric t) (F.connection t) κ)
    (hpos : ∀ t < 1, ∀ x, 0 < (F.connection t).scalarCurvature x)
    (hline : ∀ t < 1, ∃ γ : ℝ → M, ∀ s r : ℝ,
      (F.metric t).edist (γ s) (γ r) = ENNReal.ofReal |s - r|)
    (t : ℝ) (ht : t < 1) :
    (F.metric t).HasCompactRoundParallelFactor (F.connection t) := by
  have hmap : (fun s : ℝ => s + t) '' Iic 0 ⊆ Iio 1 := by
    rintro _ ⟨s, hs, rfl⟩
    exact lt_of_le_of_lt (by linarith [show s ≤ 0 from hs]) ht
  let G := F.translate t hmap ordConnected_Iic
    ⟨-1, by norm_num, 0, by norm_num, by norm_num⟩
  have hGtime (s : ℝ) (hs : s ≤ 0) : s + t < 1 := by linarith
  have hGb : ∃ K : ℝ, 0 ≤ K ∧ ∀ s ≤ 0, ∀ x,
      (G.connection s).curvatureTensorNorm x ≤ K := by
    obtain ⟨K, hK, hbound⟩ := hb t ht
    exact ⟨K, hK, fun s hs x => hbound (s + t) (by linarith) x⟩
  have h := G.exists_compact_round_parallel_factor_of_ancient_line hP
    (fun s hs => hc (s + t) (hGtime s hs))
    (fun s hs => hop (s + t) (hGtime s hs)) hGb
    (fun s hs => hκ (s + t) (hGtime s hs))
    (fun s hs => hpos (s + t) (hGtime s hs))
    (by simpa only [G, translate_metric, zero_add] using hline t ht)
  change (F.metric (0 + t)).HasCompactRoundParallelFactor (F.connection (0 + t)) at h
  exact (congrArg (fun s => (F.metric s).HasCompactRoundParallelFactor (F.connection s))
    (zero_add t)).mp h

theorem scalarCurvature_spatially_constant_of_line_at_each_time
    (hP : ThreeDimensionalClassificationPredecessors.{u})
    (F : RicciFlow 3 M (Iio 1))
    (hc : ∀ t < 1, MetricComplete (F.metric t))
    (hop : ∀ t < 1, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hb : ∀ T < 1, ∃ K : ℝ, 0 ≤ K ∧ ∀ t ≤ T, ∀ x,
      (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : ∀ t < 1,
      MetricKappaNoncollapsed (F.metric t) (F.connection t) κ)
    (hpos : ∀ t < 1, ∀ x, 0 < (F.connection t).scalarCurvature x)
    (hline : ∀ t < 1, ∃ γ : ℝ → M, ∀ s r : ℝ,
      (F.metric t).edist (γ s) (γ r) = ENNReal.ofReal |s - r|)
    (t : ℝ) (ht : t < 1) (x y : M) :
    (F.connection t).scalarCurvature x = (F.connection t).scalarCurvature y := by
  obtain ⟨f, hf, hu, hz, _, hround⟩ :=
    F.exists_compact_round_parallel_factor_of_line_at_each_time hP hc hop hb hκ hpos hline t ht
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf (⊤ : Opens M)
    (fun z _ => regular_of_hasUnitGradient hu z) 2 0
  let := isManifold_openLevelSet hf (⊤ : Opens M)
    (fun z _ => regular_of_hasUnitGradient hu z) 2 0
  obtain ⟨_, _, _, Φ, e, _, _, _, _, _, hscalar, _⟩ :=
    exists_parallelGradient_productIsometry_curvature (hc t ht) hf hu hz
  obtain ⟨R, _, hR⟩ :=
    (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp hround
  exact (hscalar x).symm.trans ((hR (e.symm x).1).trans
    ((hR (e.symm y).1).symm.trans (hscalar y)))

end RicciFlow

end PoincareConjecture

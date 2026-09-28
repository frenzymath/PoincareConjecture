import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.AncientSolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.AncientRescaledLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.ParallelGradient.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.FlowProduct
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.ParallelGradient.AncientFactor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Construction
















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1000000

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.AncientKappaSolution

open RiemannianMetric

variable {M : Type} [TopologicalSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem exists_round_surface_factor_of_persistent_parallel_coordinate
    (P : M23NormalizedKappaCompactnessPredecessors) (K : AncientKappaSolution 3 M)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ≤ 0, ∀ x, (K.flow.connection t).curvatureTensorNorm x ≤ B)
    (p : M) {f : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hu : ∀ t ≤ 0, HasUnitGradient (K.flow.connection t) f)
    (hz : ∀ t ≤ 0, HasZeroHessian (K.flow.connection t) f)
    (hp : ∀ t ≤ 0, (K.flow.connection t).gradient f = (K.flow.connection 0).gradient f) :
    ∃ (N : Type) (_ : TopologicalSpace N) (_ : T3Space N)
      (_ : ConnectedSpace N) (_ : MeasurableSpace N) (_ : BorelSpace N)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N)
      (_ : IsManifold (𝓡 2) ∞ N) (_ : SecondCountableTopology N)
      (A : AncientKappaSolution 2 N),
      A.kappa = K.kappa / 2 ∧ Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
      ∃ e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
        (∀ t ≤ 0, ∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          (K.flow.metric t).inner (e z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
              (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
        (∀ q, (e.symm q).2 = f q) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun q (_ : q ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient (hu 0 le_rfl) q
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg 2 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg 2 0
  let H := K.flow.parallelGradientFactor hf (show (0 : ℝ) ∈ Iic 0 by simp) hu hz
  obtain ⟨hne, hconn, hcN, hopN, hboundN, hposN⟩ :=
    K.flow.parallelGradientFactor_geometry hf (show (0 : ℝ) ∈ Iic 0 by simp)
      hu hz K.complete K.nonnegative_curvature_operator hbound
  let : ConnectedSpace (zeroLevelSet f) := hconn
  let : Nonempty (zeroLevelSet f) := hne
  let : SecondCountableTopology (zeroLevelSet f) := (H.metric 0).secondCountableTopology
  obtain ⟨_, _, _, Φ, e, h0, hΦ, hs, he, _, _, hcoord, _⟩ :=
    exists_parallelGradient_productIsometry (K.complete 0 le_rfl) hf (hu 0 le_rfl) (hz 0 le_rfl)
  have hnonflat : ∀ t ≤ 0, ∃ y, (H.connection t).curvatureTensorNorm y ≠ 0 := by
    intro t ht
    obtain ⟨y, hy⟩ := hposN t ht p (P.scalar_pos M K t ht p)
    refine ⟨y, fun hzero => ?_⟩
    have hb := (H.connection t).abs_scalarCurvature_le_curvatureTensorNorm y
    rw [hzero, mul_zero] at hb
    exact hy.not_ge ((le_abs_self _).trans hb)
  let A : AncientKappaSolution 2 (zeroLevelSet f) := {
    flow := H
    kappa := K.kappa / 2
    kappa_pos := div_pos K.kappa_pos (by norm_num)
    complete := hcN
    nonnegative_curvature_operator := hopN
    bounded_curvature := fun t ht => ⟨B, hB, fun y => by
      rw [abs_of_nonneg (show 0 ≤ (H.connection t).curvatureTensorNorm y from
        Real.sqrt_nonneg _)]
      exact hboundN t ht y⟩
    nonflat := hnonflat
    noncollapsed := K.flow.parallelGradientFactor_parabolic_noncollapsed K.complete hf
      hu hz hp K.noncollapsed }
  refine ⟨zeroLevelSet f, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, A, rfl,
    P.two_dimensional_classification (zeroLevelSet f) A, e, ?_, hcoord⟩
  intro t ht z v w
  have hΦt (q : M) : IsMIntegralCurve (fun s => Φ s q) ((K.flow.connection t).gradient f) := by
    rw [hp t ht]
    exact hΦ q
  have heq : (e : zeroLevelSet f × ℝ → M) =
      (fun z => Φ z.2 (zeroLevelIncl f z.1)) := funext he
  rw [heq]
  exact gradientFlow_product_metric hf (hu t ht) (hz t ht) hs hΦt h0 z v w




theorem exists_compact_round_surface_product_of_minimizing_line
    (P : M23NormalizedKappaCompactnessPredecessors) (K : AncientKappaSolution 3 M)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ≤ 0, ∀ x, (K.flow.connection t).curvatureTensorNorm x ≤ B)
    (p : M) (γ : ℝ → M)
    (hγ : ∀ s t : ℝ, (K.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ∃ C : FlowCarrier.{0} 2,
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : MeasurableSpace C.carrier := C.measurableSpace
      letI : BorelSpace C.carrier := C.borelSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
      letI : T2Space C.carrier := C.t2Space
      letI : T3Space C.carrier := C.t3Space
      letI : SecondCountableTopology C.carrier := C.secondCountable
      letI : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
      ∃ A : AncientKappaSolution 2 C.carrier,
        A.kappa = K.kappa / 2 ∧ Nonempty (TwoDimensionalAncientRoundCertificate A) ∧
        ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
          (∀ t ≤ 0, ∀ (z : C.carrier × ℝ)
            (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            (K.flow.metric t).inner (e z)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                (A.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
          (∀ t ≤ 0, ∀ x,
            (A.flow.connection t).curvatureTensorNorm (e.symm x).1 =
              (K.flow.connection t).curvatureTensorNorm x) := by
  let : SecondCountableTopology M := (K.flow.metric 0).secondCountableTopology
  let f := (K.flow.metric 0).busemann γ
  obtain ⟨hf, hu, hz, hconn, A, hflow, hconstant, e, _, hmetric, hnorm⟩ :=
    K.flow.exists_ancientKappaSolution_factor_of_minimizing_line
      ricciFlowCurvatureTheory K.complete K.nonnegative_curvature_operator hB hbound
      K.kappa_pos K.noncollapsed ⟨p, P.scalar_pos M K 0 le_rfl p⟩ γ hγ
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hu x) 2 0
  let := isManifold_openLevelSet hf (⊤ : Opens M)
    (fun x _ => regular_of_hasUnitGradient hu x) 2 0
  let : ConnectedSpace (zeroLevelSet f) := hconn
  let C := FlowCarrier.ofConnectedManifold 2 (zeroLevelSet f)
  exact ⟨C, A, hconstant, P.two_dimensional_classification (zeroLevelSet f) A,
    e, hmetric, hnorm⟩

end PoincareConjecture.AncientKappaSolution

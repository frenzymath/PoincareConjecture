import PoincareConjecture.Proofs.M32.Claim11_35.FiniteProductPersistence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.FactorFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.AncientRescaledLimit

noncomputable section
set_option autoImplicit false

universe u

namespace PoincareConjecture.M32

open Set TopologicalSpace
open RiemannianMetric
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle ENNReal Topology

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem blowupLimit_exists_fixed_product_on_closed_slab
    (P : RepairedHornSelectionPredecessors.{u}) {T₀ : ℝ≥0∞}
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval T₀))
    {T : ℝ} (hT : 0 < T) (hsub : Icc (-T) 0 ⊆ blowupBackwardInterval T₀)
    (γ : ℝ → L.carrier.carrier)
    (hγ : ∀ s t : ℝ,
      (L.flow.metric 0).edist (γ s) (γ t) = ENNReal.ofReal |s - t|) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ t ∈ Icc (-T) 0, ∀ x,
        |(L.flow.connection t).curvatureTensorNorm x| ≤ B) ∧
      ∃ C : FlowCarrier.{u} 2,
        ∃ H : RicciFlow 2 C.carrier (Icc (-T) 0),
          (∀ t ∈ Icc (-T) 0, MetricComplete (H.metric t)) ∧
          (∀ t ∈ Icc (-T) 0, ∀ y, (H.connection t).NonnegativeCurvatureOperator y) ∧
          (∀ t ∈ Icc (-T) 0, ∀ y, (H.connection t).curvatureTensorNorm y ≤ B) ∧
          ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L.carrier.carrier,
            (∀ z, (L.flow.metric 0).busemann γ (e z) = z.2) ∧
            (∀ t ∈ Icc (-T) 0, ∀ (z : C.carrier × ℝ)
              (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
              (L.flow.metric t).inner (e z)
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                  (H.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
            (∀ t ∈ Icc (-T) 0, ∀ x,
              (H.connection t).scalarCurvature (e.symm x).1 =
                (L.flow.connection t).scalarCurvature x) ∧
            (∀ t ∈ Icc (-T) 0, ∀ x,
              (H.connection t).curvatureTensorNorm (e.symm x).1 =
                (L.flow.connection t).curvatureTensorNorm x) ∧
            (H.connection 0).scalarCurvature (e.symm L.base).1 = 1 := by
  let : ConnectedSpace L.carrier.carrier := L.connectedSpace
  let f := (L.flow.metric 0).busemann γ
  obtain ⟨hf, _, hp⟩ := blowupLimit_busemann_persists_on_closed_slab P L hT hsub γ hγ
  have hneg : -T < 0 := by linarith
  have hzero : (0 : ℝ) ∈ Icc (-T) 0 := ⟨hneg.le, le_rfl⟩
  have hnontrivial : (Icc (-T) (0 : ℝ)).Nontrivial :=
    ⟨-T, ⟨le_rfl, hneg.le⟩, 0, hzero, hneg.ne⟩
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow
    L.flow hsub ordConnected_Icc hnontrivial
  have hc : ∀ t ∈ Icc (-T) 0, MetricComplete (F.metric t) :=
    fun t ht => L.complete t (hsub ht)
  have hop : ∀ t ∈ Icc (-T) 0, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x :=
    fun t ht x => L.nonnegative_curvature_operator t (hsub ht) x
  obtain ⟨B, hB, hbound⟩ :=
    L.curvature_locally_bounded_in_time (Icc (-T) 0) isCompact_Icc hsub
  have hbound' : ∀ t ∈ Icc (-T) 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ B :=
    fun t ht x => (le_abs_self _).trans (hbound t ht x)
  let huall : ∀ t ∈ Icc (-T) 0, HasUnitGradient (F.connection t) f :=
    fun t ht => (hp t ht).2.1
  let hzall : ∀ t ∈ Icc (-T) 0, HasZeroHessian (F.connection t) f :=
    fun t ht => (hp t ht).2.2
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens L.carrier.carrier)) =>
    regular_of_hasUnitGradient (huall 0 hzero) x
  let := openLevelSetChartedSpace hf (⊤ : Opens L.carrier.carrier) hreg 2 0
  let := isManifold_openLevelSet hf (⊤ : Opens L.carrier.carrier) hreg 2 0
  let H := F.parallelGradientFactor hf hzero huall hzall
  obtain ⟨_, hconn, hcomplete, hoperator, hnorm, _⟩ :=
    F.parallelGradientFactor_geometry hf hzero huall hzall hc hop hbound'
  let : ConnectedSpace (zeroLevelSet f) := hconn
  obtain ⟨_, _, _, Φ, e, hΦ0, hΦ, he, hcoord, _, _, _, _⟩ :=
    exists_parallelGradient_productIsometry_curvature (n := 2)
      (hc 0 hzero) hf (huall 0 hzero) (hzall 0 hzero)
  have hproduct (t : ℝ) (ht : t ∈ Icc (-T) 0) :
      (∀ (z : zeroLevelSet f × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
        (F.metric t).inner (e z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
            (H.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
      (∀ x, (H.connection t).scalarCurvature (e.symm x).1 =
        (F.connection t).scalarCurvature x) ∧
      (∀ x, (H.connection t).curvatureTensorNorm (e.symm x).1 =
        (F.connection t).curvatureTensorNorm x) := by
    obtain ⟨_, _, _, Ψ, d, hΨ0, hΨ, hd, _, hm, hs, hn, _⟩ :=
      exists_parallelGradient_productIsometry_curvature (n := 2)
        (hc t ht) hf (huall t ht) (hzall t ht)
    have hde : d = e := by
      apply Diffeomorph.ext
      intro z
      rw [hd, he]
      have hcurve := hΨ (zeroLevelIncl f z.1)
      have hfield : (F.connection t).gradient f = (F.connection 0).gradient f :=
        (hp t ht).1
      rw [hfield] at hcurve
      have hsame := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
        ((F.connection 0).contMDiff_gradient hf |>.of_le (by simp)) hcurve
        (hΦ (zeroLevelIncl f z.1))
        (show Ψ 0 (zeroLevelIncl f z.1) = Φ 0 (zeroLevelIncl f z.1) by rw [hΨ0, hΦ0])
      exact congrFun hsame z.2
    rw [hde] at hm hs hn
    exact ⟨hm, hs, hn⟩
  let C := FlowCarrier.ofConnectedManifold 2 (zeroLevelSet f)
  refine ⟨B, hB, hbound, C, H, hcomplete, hoperator, hnorm, e, hcoord,
    fun t ht => (hproduct t ht).1, fun t ht => (hproduct t ht).2.1,
    fun t ht => (hproduct t ht).2.2, ?_⟩
  exact ((hproduct 0 hzero).2.1 L.base).trans L.scalar_normalized

end PoincareConjecture.M32

import PoincareConjecture.Proofs.M03.Existence.DeTurckResidualNative

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.DeTurckSmoothForcingNative

open SpectralHeatNative QuasilinearDeTurckNative TimeL2BilinearNative
  DeTurckMetricProducerNative ContinuousPathCompositionNative

section Forcing

variable {iota : Type*} [Countable iota] {T : ℝ}
  (lambda : iota → NNReal)
  (A : C(State iota, State iota →L[ℝ] State iota)) (b : C(State iota, State iota))

def uncutForcing (hT : 0 ≤ T) (F : ForcingSpace iota T) : ForcingSpace iota T :=
  productOperator hT (ContinuousLinearMap.id ℝ (State iota →L[ℝ] State iota))
      (A.comp (shiftedTraceOperator hT lambda F)) (shiftedHighOperator hT lambda F) +
    tracePathL2 hT (b.comp (shiftedTraceOperator hT lambda F))

theorem uncutForcing_contDiff (hT : 0 ≤ T)
    (hA : ContDiff ℝ ∞ (A : State iota → State iota →L[ℝ] State iota))
    (hb : ContDiff ℝ ∞ (b : State iota → State iota)) :
    ContDiff ℝ ∞ (uncutForcing lambda A b hT) := by
  have hAc : ContDiff ℝ ∞ (fun F : ForcingSpace iota T =>
      A.comp (shiftedTraceOperator hT lambda F)) :=
    (contDiff_postcomp (Icc (0 : ℝ) T) A hA).comp
      (shiftedTraceOperator hT lambda).contDiff
  have hbc : ContDiff ℝ ∞ (fun F : ForcingSpace iota T =>
      b.comp (shiftedTraceOperator hT lambda F)) :=
    (contDiff_postcomp (Icc (0 : ℝ) T) b hb).comp
      (shiftedTraceOperator hT lambda).contDiff
  have htop : ContDiff ℝ ∞ (fun F : ForcingSpace iota T =>
      productOperator hT (ContinuousLinearMap.id ℝ (State iota →L[ℝ] State iota))
        (A.comp (shiftedTraceOperator hT lambda F)) (shiftedHighOperator hT lambda F)) := by
    simpa only [Function.comp_def] using
      (((productOperator hT
        (ContinuousLinearMap.id ℝ (State iota →L[ℝ] State iota))).contDiff.comp hAc).clm_apply
          (shiftedHighOperator hT lambda).contDiff)
  have hlower : ContDiff ℝ ∞ (fun F : ForcingSpace iota T =>
      tracePathL2 (E := State iota) hT (b.comp (shiftedTraceOperator hT lambda F))) := by
    simpa only [Function.comp_def] using
      (tracePathL2 (E := State iota) hT).contDiff.comp hbc
  change ContDiff ℝ ∞ (fun F : ForcingSpace iota T =>
    productOperator hT (ContinuousLinearMap.id ℝ (State iota →L[ℝ] State iota))
      (A.comp (shiftedTraceOperator hT lambda F)) (shiftedHighOperator hT lambda F) +
    tracePathL2 (E := State iota) hT (b.comp (shiftedTraceOperator hT lambda F)))
  exact htop.add hlower

theorem uncutForcing_coe (hT : 0 ≤ T) (F : ForcingSpace iota T) :
    uncutForcing lambda A b hT F =ᵐ[timeMeasure T] fun t =>
      A (shiftedBaseMultiplier lambda (shiftedHighOperator hT lambda F t))
          (shiftedHighOperator hT lambda F t) +
        b (shiftedBaseMultiplier lambda (shiftedHighOperator hT lambda F t)) := by
  let ev := ContinuousLinearMap.id ℝ (State iota →L[ℝ] State iota)
  let P := A.comp (shiftedTraceOperator hT lambda F)
  let Q := b.comp (shiftedTraceOperator hT lambda F)
  let H := shiftedHighOperator hT lambda F
  filter_upwards [product_ae_eq_on_interval hT ev P H, tracePathL2_ae_eq hT Q,
    Lp.coeFn_add (product hT ev P H) (tracePathL2 hT Q),
    intermediate_high_eq_trace hT lambda F, ae_restrict_mem measurableSet_Ioc]
      with t hproduct hlower hadd htrace ht
  have hmem : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  change (product hT ev P H + tracePathL2 hT Q) t = _
  rw [hadd, Pi.add_apply, hproduct hmem, hlower hmem]
  change A (shiftedTracePath hT lambda F ⟨t, hmem⟩) (H t) +
    b (shiftedTracePath hT lambda F ⟨t, hmem⟩) = _
  rw [← htrace hmem]

theorem uncutForcing_eq_cutoff_forcing (hT : 0 ≤ T) (hT1 : T ≤ 1)
    {rho : ℝ} (hrho : 0 < rho) (C C0 : NNReal)
    (hmix : LocalMixedBound lambda rho C C0
      (fun x => A (shiftedBaseMultiplier lambda x) x + b (shiftedBaseMultiplier lambda x)))
    (F : ForcingSpace iota T)
    (hF : ‖F‖ ≤ (cutoffSpatialResidual lambda hrho
      (fun x => A (shiftedBaseMultiplier lambda x) x + b (shiftedBaseMultiplier lambda x))
      C C0 hmix).forcingRadius) :
    uncutForcing lambda A b hT F =
      (cutoffSpatialResidual lambda hrho
        (fun x => A (shiftedBaseMultiplier lambda x) x + b (shiftedBaseMultiplier lambda x))
        C C0 hmix).forcingResidual hT F := by
  apply Lp.ext
  filter_upwards [uncutForcing_coe lambda A b hT F,
    (cutoffSpatialResidual lambda hrho
      (fun x => A (shiftedBaseMultiplier lambda x) x + b (shiftedBaseMultiplier lambda x))
      C C0 hmix).forcingResidual_coe hT F,
    cutoffSpatialResidual_response_eq hT hT1 lambda hrho
      (fun x => A (shiftedBaseMultiplier lambda x) x + b (shiftedBaseMultiplier lambda x))
      C C0 hmix F hF] with t hraw hforcing hcutoff
  exact hraw.trans (hcutoff.symm.trans hforcing.symm)

end Forcing

section NativeForcing

open TensorProbeNative TensorHilbertNative NativeChartScalarLocalization
  DeTurckJetCoordinatesNative DeTurckResidualNative ChartMeasureNative

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {g0 : RiemannianMetric n M} (d : Data g0)
  (L : FiniteChartLocalizationData d.charts)
  (A : CompatibleChartCover (n := n) (M := M))

include L A in

theorem exists_native_smooth_forcing (r p : ℕ) (hpr : 2 * p ≤ r)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ N : SpatialResidual d.symmetricParameters,
      2 * N.forcingRadius < rho ∧
      (∀ (g : RiemannianMetric n M) (D : LeviCivitaData g) (B : LeviCivitaData g0)
        (h : SmoothTensor (n := n) (M := M))
        (hsymm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v),
        (∀ (x : M) (v w : TangentSpace (𝓡 n) x),
          g.inner x v w = g0.inner x v w + h x v w) →
        ‖d.smoothTensorCoordinates (2 * r + 1) h hsymm‖ ≤ rho →
        N.toFun (d.smoothTensorCoordinates (2 * r + 2) h hsymm) =
          d.residualCoordinates (2 * r) D B h hsymm) ∧
      ∀ T : ℝ, ∀ hT : 0 ≤ T,
        ∃ R : ForcingSpace d.SymmetricIndex T → ForcingSpace d.SymmetricIndex T,
          ContDiff ℝ ∞ R ∧
          ∀ (_hT1 : T ≤ 1) (F : ForcingSpace d.SymmetricIndex T),
            ‖F‖ ≤ N.forcingRadius → R F = N.forcingResidual hT F := by
  obtain ⟨Aop, b, hA, hb, _, rho, hrho, C, C0, hmix, hEq⟩ :=
    exists_rawResidual d L A r p hpr hp
  let Amap : C(State d.SymmetricIndex, State d.SymmetricIndex →L[ℝ] State d.SymmetricIndex) :=
    ⟨Aop, hA.continuous⟩
  let bmap : C(State d.SymmetricIndex, State d.SymmetricIndex) := ⟨b, hb.continuous⟩
  let raw := fun x => Aop (shiftedBaseMultiplier d.symmetricParameters x) x +
    b (shiftedBaseMultiplier d.symmetricParameters x)
  let N := cutoffSpatialResidual d.symmetricParameters hrho raw C C0 hmix
  refine ⟨rho, hrho, N,
    cutoffSpatialResidual_forcingRadius d.symmetricParameters hrho raw C C0 hmix, ?_, ?_⟩
  · intro g D B h hsymm hmetric hsmall
    have hJ : shiftedBaseMultiplier d.symmetricParameters
        (d.smoothTensorCoordinates (2 * r + 2) h hsymm) =
        d.smoothTensorCoordinates (2 * r + 1) h hsymm := by
      simpa only [Nat.add_assoc] using
        shiftedBase_smoothTensorCoordinates d (2 * r + 1) h hsymm
    change (cutoffSpatialResidual d.symmetricParameters hrho raw C C0 hmix).toFun _ = _
    rw [cutoffSpatialResidual_apply_of_small d.symmetricParameters hrho raw C C0 hmix
      (by rw [hJ]; exact hsmall)]
    exact hEq g D B h hsymm hmetric hsmall
  · intro T hT
    refine ⟨uncutForcing d.symmetricParameters Amap bmap hT,
      uncutForcing_contDiff d.symmetricParameters Amap bmap hT hA hb, ?_⟩
    intro hT1 F hF
    exact uncutForcing_eq_cutoff_forcing d.symmetricParameters Amap bmap hT hT1
      hrho C C0 hmix F hF

end NativeForcing

end PoincareConjecture.DeTurckSmoothForcingNative

end

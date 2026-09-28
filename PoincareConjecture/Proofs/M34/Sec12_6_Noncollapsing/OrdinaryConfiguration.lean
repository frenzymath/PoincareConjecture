import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryStableVolume
import PoincareConjecture.Proofs.M34.Standard.OrdinarySliceMetric
import PoincareConjecture.Definitions.M15Noncollapsing










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M34



theorem ordinaryProduct_configuration
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    {I : SpacetimeInterval} {F : RicciFlow n M I.domain}
    (R : OrdinaryProductRicciGeometry F.metric I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    {T taumax tau taubar l0 V r : ℝ} (hT : T ∈ I.domain) (p : M)
    (out : M14OrdinaryCaptureOutput (ordinaryProductLGeometry R hRicci) M I
      R.product.productCylinder R.product.productMetric F T taumax
      (ordinaryProductCaptureData (I := I) (F := F) R hRicci hT taumax))
    (E : M14ExponentialFamily (ordinaryProductLGeometry R hRicci) T
      (R.product.sliceIdentification ⟨T, hT⟩ p).val)
    (H : M14StableSet (ordinaryProductLGeometry R hRicci) T tau
      (R.product.sliceIdentification ⟨T, hT⟩ p).val E)
    (C : MetricHomothetyCalculus (F.metric T) (R.product.slices T).metricOnPoints
      (R.product.sliceIdentification ⟨T, hT⟩) 1)
    (hcomplete : MetricComplete (F.metric T))
    (hmax : tau < taumax) (hbar : tau ≤ taubar) (hr : r ^ 2 ≤ tau)
    (hmem : T - tau ∈ I.domain) {Omega : Set M} (hOmega : IsOpen Omega)
    (hvol : ENNReal.ofReal V ≤ calibratedMetricVolume (F.metric (T - tau)) Omega)
    (hlength : ∀ y ∈ Omega, reducedLength F T p y tau ≤ l0)
    {K : SpacetimeInterval} {A : Type u} [TopologicalSpace A]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) A] [IsManifold (𝓡 n) ∞ A]
    [T2Space A] [SecondCountableTopology A]
    (B : M15ActualBallCylinder (ordinaryProductLGeometry R hRicci) T
      (R.product.sliceIdentification ⟨T, hT⟩ p) r K A) :
    Nonempty (M15Theorem81Configuration (ordinaryProductLGeometry R hRicci) T
      (R.product.sliceIdentification ⟨T, hT⟩ p) E taubar l0 V r K A B) := by
  have hl : ∀ y ∈ Omega, reducedLength F T
      (ordinaryProductProjection R.product (R.product.sliceIdentification ⟨T, hT⟩ p).val)
      y tau ≤ l0 := by
    rw [ordinaryProductProjection_eq, R.product.sliceIdentification_eq]
    exact hlength
  obtain ⟨W, hW, hWH, hWlength, hWvol⟩ :=
    ordinaryProduct_stable_open_volume R hRicci hT out E H hmax hmem hOmega hl
  exact ⟨{
    tau₀ := tau
    tau₀_pos := H.tau_pos
    tau₀_le := hbar
    radius_sq_le_tau₀ := hr
    terminal_mem := hmem
    terminal_ball_compact := ordinarySlice_compact_ball R.product ⟨T, hT⟩ C hcomplete p r
    stable := H
    W := W
    W_open := hW
    W_subset_stable := hWH
    normalized_reduced_length := hWlength
    terminal_image_volume := hvol.trans_eq hWvol.symm
  }⟩

end PoincareConjecture.M34

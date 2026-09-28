import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.Persistence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Collars.Comparison



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}




theorem exists_late_captured_static_neck_transfer_of_two_le
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    {ε δ l u : ℝ} (hεpos : 0 < ε) (hε : ε ≤ 1 / 200)
    (hεδ : 2 * ε ≤ δ) (hδhalf : δ < 1 / 2) (hl : 0 < l) (hu : 0 < u)
    (x₀ : H.regularRegion P04) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t (ht : t ∈ Ico H.reference.tMinus T), s ≤ t →
        ∀ N : EpsilonNeck (F.metric t), N.epsilon = ε →
          H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
          l ≤ N.connection.scalarCurvature N.center →
          N.connection.scalarCurvature N.center ≤ u →
          ∃ N' : EpsilonNeck (H.terminalMetric P04),
            N'.epsilon = δ ∧ N'.connection = H.terminalConnection P04 ∧
            (N'.center : M) = H.reference.inverse t ht N.center ∧
            N'.scale = ((H.terminalConnection P04).scalarCurvature N'.center) ^ (-1 / 2 : ℝ) ∧
            N'.coordinate_map = SingularRegularLimit.openRetraction (H.regularRegion P04) x₀ ∘
              H.reference.inverse t ht ∘ N.coordinate_map ∧
            N'.coordinate_inverse = N.coordinate_inverse ∘ H.regularNeckSourceMap P04 ht ∧
            N'.central_sphere = H.regularReferencePreimage P04 t ht N.central_sphere ∧
            N'.carrier = H.regularReferencePreimage P04 t ht (N.region (-δ⁻¹) δ⁻¹) ∧
            ∀ a b : ℝ, N'.region a b = H.regularReferencePreimage P04 t ht
              (N.region (-δ⁻¹) δ⁻¹ ∩ N.region a b) := by
  obtain ⟨s, hs, hsT, hcomparison⟩ :=
    H.exists_late_static_neck_terminal_comparison P04 hA hεpos hε hl hu
  refine ⟨s, hs, hsT, ?_⟩
  intro t ht hst N hNε hNA hql hqu
  have hcapture : MapsTo (H.reference.inverse t ht) N.carrier H.reference.regularLimitSet := by
    intro y hy
    obtain ⟨x, _, hx⟩ := hNA (mem_image_of_mem _ hy)
    exact hx ▸ x.property
  let K := H.regularStaticNeck P04 ht N x₀ hcapture
  have hKA : K.carrier ⊆ A := H.regularReferencePreimage_subset P04 t ht N.carrier hNA
  have hKe : K.epsilon = ε := (H.regularStaticNeck_epsilon P04 ht N x₀ hcapture).trans hNε
  have hKq := H.regularStaticNeck_scalar_center P04 ht N x₀ hcapture
  have hKl : l ≤ K.connection.scalarCurvature K.center := by simpa only [K, hKq] using hql
  have hKu : K.connection.scalarCurvature K.center ≤ u := by simpa only [K, hKq] using hqu
  obtain ⟨hQ, hclose⟩ := hcomparison t ⟨hst, ht.2⟩ K hKe hKA hKl hKu
  have hQT : 0 < (H.terminalConnection P04).scalarCurvature K.center := by
    simpa only [H.terminalFlow_scalar_at_terminal] using hQ
  have hcloseT : RoundCylinderClose δ 0 (fun z v w =>
      (H.terminalConnection P04).scalarCurvature K.center *
        roundCylinderPullback (H.terminalMetric P04) K.coordinate_map z v w) := by
    apply NoncompactKappa.Positive.roundCylinderClose_mono
      (by positivity : 0 < 2 * ε) hεδ (by norm_num : (0 : ℝ) < 1)
    simpa only [H.terminalFlow_scalar_at_terminal, H.terminalFlow_metric_at_terminal] using hclose
  have hweak : K.epsilon ≤ δ := by rw [hKe]; linarith
  let L := K.withMetric (H.terminalMetric P04) (H.terminalConnection P04)
    hweak hδhalf hQT hcloseT
  refine ⟨L, rfl, rfl, H.regularStaticNeck_center_val P04 ht N x₀ hcapture,
    rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (K.withMetric_carrier (H.terminalMetric P04) (H.terminalConnection P04)
      hweak hδhalf hQT hcloseT).trans (H.regularStaticNeck_region P04 ht N x₀ hcapture _ _)
  · intro a b
    rw [K.withMetric_region (H.terminalMetric P04) (H.terminalConnection P04)
      hweak hδhalf hQT hcloseT]
    rfl

end PoincareConjecture.SingularTimeAssumptions

import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Static
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Topology.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Volume.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Transport.CoreVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Transport.ScalarBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

theorem exists_cap_transport_of_terminal_neck_comparisons_of_m27
    (P : M27KappaAlternativePredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ kappa : ℝ, 0 < kappa → ∀ C₀ : ℝ, 0 < C₀ →
        ∃ C : ℝ, 0 < C ∧
          ∀ {S : NormalizedKappaSolutionSequence kappa}
            {G : M23InteriorConvergence S}
            {e : ∀ j, NormalizedKappaSpacetimeEmbedding
              (source := S.term (G.subsequence j)) (target := G.limit)
              (Iic 0 ×ˢ G.exhaustion j)},
            M23TerminalMetricConvergence G e →
            (∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
              ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2) →
            ∀ A : CapCertificate (G.limit.flow.flow.metric 0),
              A.epsilon ≤ epsilon₀ → A.cap_constant ≤ C₀ →
              (∀ᶠ k in atTop, RoundCylinderClose A.epsilon 0 (fun z v w ↦
                ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
                  ((e k).toFun (0, A.end_neck.center)).2 *
                roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
                  (G.terminalNeckEmbedding e A.end_neck A.epsilon k) z v w)) →
              (∀ᶠ k in atTop, RoundCylinderClose A.epsilon 0 (fun z v w ↦
                ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
                  ((e k).toFun (0, A.boundary_neck.center)).2 *
                roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
                  (G.terminalNeckEmbedding e A.boundary_neck A.epsilon k) z v w)) →
              ∀ᶠ k in atTop,
                ∃ B : CapCertificate ((S.term (G.subsequence k)).flow.flow.metric 0),
                  B.epsilon = A.epsilon ∧ B.cap_constant = C ∧
                  B.carrier = (fun x ↦ ((e k).toFun (0, x)).2) '' A.carrier ∧
                  B.core = (fun x ↦ ((e k).toFun (0, x)).2) '' A.core ∧
                  B.closed_core = (fun x ↦ ((e k).toFun (0, x)).2) '' A.closed_core ∧
                  B.boundary_sphere = (fun x ↦ ((e k).toFun (0, x)).2) '' A.boundary_sphere ∧
                  B.model_kind = A.model_kind ∧
                  B.connection = (S.term (G.subsequence k)).flow.flow.connection 0 := by
  obtain ⟨D, hD, hderivatives⟩ := uniformKappaCapDerivativeFields_small_of_m27 P
  obtain ⟨epsilon₀, hepsilon₀, hsmall, hcoreVolume⟩ :=
    exists_transferred_core_volume_threshold_of_m27 P
  refine ⟨epsilon₀, hepsilon₀, hsmall, ?_⟩
  intro kappa hkappa C₀ hC₀
  obtain ⟨V, hV, hcore⟩ := hcoreVolume kappa hkappa
  let C := max (4 * C₀) (max D V)
  have hfourC : 4 * C₀ ≤ C := le_max_left _ _
  have hDC : D ≤ C := (le_max_left D V).trans (le_max_right _ _)
  have hVC : V ≤ C := (le_max_right D V).trans (le_max_right _ _)
  have hC : 0 < C := (mul_pos (by norm_num) hC₀).trans_le hfourC
  refine ⟨C, hC, ?_⟩
  intro S G e hconv hfixed A hepsilon hAC₀ hendClose hboundaryClose
  have hAC : A.cap_constant ≤ C := by linarith
  have hfourAC : 4 * A.cap_constant ≤ C := by linarith
  have hhalf : A.epsilon < 1 / 2 := by linarith [A.epsilon_le_threshold]
  have hcompact := A.isCompact_closure_carrier (G.limit.flow.complete 0 le_rfl)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  have hsup := (hconv.tendsto_cap_scalarSup hfixed A).eventually (lt_mem_nhds A.scalar_sup_pos)
  filter_upwards [eventually_ge_atTop j, hendClose, hboundaryClose,
    hconv.eventually_terminalNeck_center_scalar_pos hfixed A.end_neck,
    hconv.eventually_terminalNeck_center_scalar_pos hfixed A.boundary_neck,
    hconv.eventually_cap_scalar_pos_and_ratio hfixed A,
    hconv.eventually_cap_intrinsic_diameter_bound hfixed A,
    hconv.eventually_cap_volume_bound_original_constant hfixed A,
    hcore hconv hfixed A hepsilon, hsup]
    with k hk hendClose hboundaryClose hendPos hboundaryPos hscalar hdiam hvol hcoreFields hsup
  let E := (e k).spatialHomeomorph (mem_Iic.mpr le_rfl) (G.exhaustion_open k)
  let g := (S.term (G.subsequence k)).flow.flow.metric 0
  let sourceD := (S.term (G.subsequence k)).flow.flow.connection 0
  have hAstage : A.carrier ⊆ G.exhaustion k :=
    subset_closure.trans (hj.trans (hmono hk))
  have hA : A.carrier ⊆ E.source := hAstage
  have hE : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E E.source :=
    (e k).spatialHomeomorph_contMDiffOn (mem_Iic.mpr le_rfl) (G.exhaustion_open k)
  have hEi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.symm E.target :=
    (e k).spatialHomeomorph_symm_contMDiffOn (mem_Iic.mpr le_rfl) (G.exhaustion_open k)
  have hendStage := A.end_neck_subset.trans hAstage
  have hboundaryStage := A.boundary_neck_subset.trans hAstage
  have hendSource : (G.terminalNeckEmbedding e A.end_neck A.epsilon k).source =
      univ ×ˢ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ := by
    simpa only [A.end_neck_epsilon, EpsilonNeck.cylinderDomain] using
      G.terminalNeckEmbedding_full_source e A.end_neck k hendStage
  have hboundarySource : (G.terminalNeckEmbedding e A.boundary_neck A.epsilon k).source =
      univ ×ˢ Ioo (-A.epsilon⁻¹) A.epsilon⁻¹ := by
    simpa only [A.boundary_neck_epsilon, EpsilonNeck.cylinderDomain] using
      G.terminalNeckEmbedding_full_source e A.boundary_neck k hboundaryStage
  let endNeck := G.terminalStaticNeck e A.end_neck A.epsilon_pos hhalf k
    hendSource hendPos hendClose
  let boundaryNeck := G.terminalStaticNeck e A.boundary_neck A.epsilon_pos hhalf k
    hboundarySource hboundaryPos hboundaryClose
  have hendCarrier : endNeck.carrier = E '' A.end_neck.carrier :=
    G.terminalStaticNeck_carrier_of_epsilon_eq e A.end_neck A.epsilon_pos hhalf k
      hendSource hendPos hendClose A.end_neck_epsilon hendStage
  have hboundaryCarrier : boundaryNeck.carrier = E '' A.boundary_neck.carrier :=
    G.terminalStaticNeck_carrier_of_epsilon_eq e A.boundary_neck A.epsilon_pos hhalf k
      hboundarySource hboundaryPos hboundaryClose A.boundary_neck_epsilon hboundaryStage
  have hboundarySphere : boundaryNeck.central_sphere = E '' A.boundary_neck.central_sphere :=
    G.terminalStaticNeck_central_sphere e A.boundary_neck A.epsilon_pos hhalf k
      hboundarySource hboundaryPos hboundaryClose
  have hendRegion : endNeck.region (-A.epsilon⁻¹) (-A.epsilon⁻¹ / 2) =
      E '' A.end_neck.region (-A.epsilon⁻¹) (-A.epsilon⁻¹ / 2) :=
    G.terminalStaticNeck_region_of_epsilon_eq e A.end_neck A.epsilon_pos hhalf k
      hendSource hendPos hendClose A.end_neck_epsilon hendStage _ _
  obtain ⟨radius, hradius, lower, hlower, hvolumeLower⟩ := hcoreFields
  have hcoreImage : E '' A.core ⊆ E '' A.closed_core := image_mono A.core_subset_closed_core
  obtain ⟨hgradient, hevolution⟩ :=
    hderivatives (S.term (G.subsequence k)).flow 0 C (E '' A.carrier) le_rfl hDC
  have hdiamC : intrinsicDiameter g (E '' A.carrier) <
      ENNReal.ofReal (C * scalarCurvatureSupOn g sourceD (E '' A.carrier) ^ (-1 / 2 : ℝ)) := by
    apply hdiam.trans_le
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hfourAC
      (Real.rpow_nonneg hsup.le _))
  have hvolC : calibratedMetricVolume g (E '' A.carrier) <
      ENNReal.ofReal C *
        ENNReal.ofReal (scalarCurvatureSupOn g sourceD (E '' A.carrier) ^ (-3 / 2 : ℝ)) :=
    hvol.trans_le (mul_le_mul' (ENNReal.ofReal_le_ofReal hAC) le_rfl)
  let B : CapCertificate g := {
    epsilon := A.epsilon
    epsilon_pos := A.epsilon_pos
    epsilon_le_threshold := A.epsilon_le_threshold
    cap_constant := C
    cap_constant_pos := hC
    carrier := E '' A.carrier
    carrier_open := A.image_carrier_open E hA
    closed_core := E '' A.closed_core
    closed_core_compact := A.image_closed_core_compact E hA
    core := E '' A.core
    core_nonempty := A.core_nonempty.image E
    core_eq_interior_closed_core := A.image_core_eq_interior E hA
    puncture := A.puncture
    model_kind := A.model_kind
    model_equivalence := A.imageModelEquivalence E hA hE hEi
    connection := sourceD
    end_neck := endNeck
    end_neck_epsilon := rfl
    end_neck_subset := by rw [hendCarrier]; exact image_mono A.end_neck_subset
    end_neck_connection := rfl
    closed_core_eq_complement_end := by
      rw [hendCarrier]
      exact A.image_closed_core_eq_complement_end E hA
    boundary_sphere := E '' A.boundary_sphere
    boundary_neck := boundaryNeck
    boundary_neck_epsilon := rfl
    boundary_neck_subset := by rw [hboundaryCarrier]; exact image_mono A.boundary_neck_subset
    boundary_neck_connection := rfl
    boundary_eq_neck_sphere := by rw [hboundarySphere, ← A.boundary_eq_neck_sphere]
    boundary_eq_end_frontier := by
      rw [hendCarrier]
      exact A.image_boundary_eq_end_frontier E hA
    boundary_subset_negative_end_closure := by
      rw [hendRegion]
      exact A.image_boundary_subset_negative_end_closure E hA
    boundary_subset := image_mono A.boundary_subset
    core_frontier_eq_boundary := A.image_core_frontier_eq_boundary E hA
    boundary_local_defining_function := A.horizon_image_boundary_local_defining_function E hA hE hEi
    scalar_pos := hscalar.1
    intrinsic_diameter_bound := hdiamC
    scalar_ratio := ⟨hscalar.2.choose, hscalar.2.choose_spec.1.trans_le hAC,
      hscalar.2.choose_spec.2⟩
    volume_bound := hvolC
    core_radius := radius
    core_radius_pos := fun y hy ↦ (hradius y (hcoreImage hy)).1
    core_radius_eq := fun y hy ↦ (hradius y (hcoreImage hy)).2.1
    core_ball_subset := fun y hy ↦ (hradius y (hcoreImage hy)).2.2.1
    core_ball_compact := fun y hy ↦ (hradius y (hcoreImage hy)).2.2.2.1
    core_ball_volume_lower := ⟨lower, (inv_anti₀ hV hVC).trans_lt hlower,
      fun y hy ↦ hvolumeLower y (hcoreImage hy)⟩
    gradient_bound := hgradient
    laplacian_bound := hevolution }
  exact ⟨B, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end M23TerminalMetricConvergence

end PoincareConjecture

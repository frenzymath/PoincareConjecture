import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceAccuracy
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceOrdinaryJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceOrdinaryComparison
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapOrdinaryEmbeddingAnalytic
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapLimitNormalization
import PoincareConjecture.Proofs.M34.Standard.CapNeckNormalizedImageWrappers
import PoincareConjecture.Proofs.M34.Standard.CapImageAnalyticBounds
import PoincareConjecture.Proofs.M34.Standard.CapImageCertificate












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    MeasurableSpace L.carrier.carrier := L.carrier.measurableSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    BorelSpace L.carrier.carrier := L.carrier.borelSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    T2Space L.carrier.carrier := L.carrier.t2Space
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    T3Space L.carrier.carrier := L.carrier.t3Space
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    SecondCountableTopology L.carrier.carrier := L.carrier.secondCountable
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ConnectedSpace L.carrier.carrier := L.connectedSpace




theorem exists_ordinary_cap_persistence_accuracy {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ epsilon / 4 ∧
      ∀ (C : ℝ), 1 ≤ C →
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace E₃ M]
        [IsManifold (𝓡 3) ∞ M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
        [ConnectedSpace M] (I : SpacetimeInterval) (F : RicciFlow 3 M I.domain)
        (R : OrdinaryProductRicciGeometry F.metric I),
        (∀ t ∈ I.domain, MetricComplete (F.metric t)) →
      ∀ (p : ℕ → (ordinaryChapter11Flow (I := I) (F := F) R).point)
        (hp : ∀ k, 0 < (ordinaryChapter11Flow (I := I) (F := F) R).scalar (p k))
        (hd : Tendsto (fun k => (ordinaryChapter11Flow (I := I) (F := F) R).scalar (p k))
          atTop atTop)
        (Conv : GeneralizedBlowupConvergence
          (fixedFlowBlowupSequence (ordinaryChapter11Flow (I := I) (F := F) R) p hp hd)
          (blowupBackwardInterval ⊤))
        (N : CapCertificate (Conv.limit.flow.metric 0)),
        N.epsilon < delta0 → N.cap_constant ≤ C →
        N.connection = Conv.limit.flow.connection 0 → Conv.limit.base ∈ N.core →
        ∀ᶠ k : ℕ in atTop,
          ∃ H : CapCertificate (M13.scaleSmoothMetric (F.metric (p (Conv.subsequence k)).1)
              ((ordinaryChapter11Flow (I := I) (F := F) R).scalar (p (Conv.subsequence k)))
              (hp (Conv.subsequence k))),
            H.epsilon = epsilon ∧
            H.cap_constant = capPersistenceConstant C (capBallVolumeCoefficient C) ∧
            ordinaryChapter11Projection R (p (Conv.subsequence k)) ∈ H.core := by
  classical
  have hepsilonHalf : epsilon < 1 / 2 := hsmall.trans_lt (by norm_num)
  obtain ⟨tau, htau, eta, heta, hnecks⟩ :=
    exists_capNeckNormalizedImage_end_boundary_tolerance.{u, u} hepsilon hepsilonHalf
  obtain ⟨delta0, hdelta0, hd0epsilon, haccuracy⟩ :=
    capPersistence_exists_common_neck_accuracy.{u} epsilon tau eta hepsilon htau heta
  refine ⟨delta0, hdelta0, hd0epsilon, ?_⟩
  intro C hC1 M _ _ _ _ _ _ _ _ I F R hcomplete p hp hd Conv N hN hC hconnection hcore
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  let : LocallyCompactSpace Conv.limit.carrier.carrier :=
    ChartedSpace.locallyCompactSpace E₃ Conv.limit.carrier.carrier
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hNepsilon : N.epsilon < epsilon :=
    (hN.trans_le hd0epsilon).trans (by linarith)
  have hJ : UniqueDiffOn ℝ (blowupBackwardInterval ⊤) := by
    simpa only [blowupBackwardInterval, ENNReal.ofReal_lt_top, and_true, Set.Iic] using
      uniqueDiffOn_Iic (0 : ℝ)
  have hend := haccuracy Conv.limit.carrier.carrier (Conv.limit.flow.metric 0) N.end_neck
    (by rwa [N.end_neck_epsilon])
  have hboundary := haccuracy Conv.limit.carrier.carrier (Conv.limit.flow.metric 0)
    N.boundary_neck (by rwa [N.boundary_neck_epsilon])
  have hscalarOld : ∀ x ∈ closure N.end_neck.carrier,
      |N.end_neck.scale ^ 2 * N.connection.scalarCurvature x - 1| ≤
        min (eta / 2) (1 / 10) := by
    simpa only [N.end_neck_connection] using hend.2.2
  have hscale : N.boundary_neck.scale ≤ (9 / 8 : ℝ) * N.end_neck.scale := by
    apply N.boundary_scale_le_of_scalar_error
    intro x hx
    have hxend : x ∈ closure N.end_neck.carrier :=
      closure_mono (fun _ hy => hy.1) (N.boundary_subset_negative_end_closure hx)
    exact (hscalarOld x hxend).trans (min_le_right _ _)
  obtain ⟨hcompleteLimit, hRicLimit, hnormalLimit⟩ := blowupLimit_zero_geometry Conv.limit
  have hnormal : N.connection.scalarCurvature Conv.limit.base = 1 := by
    simpa only [hconnection] using hnormalLimit
  have hRic : ∀ x, ∀ v : TangentSpace (𝓡 3) x, 0 ≤ N.connection.ricci x v v := by
    simpa only [hconnection] using hRicLimit
  have hcapCompact := N.isCompact_closure_of_normalized_base hcompleteLimit
    (N.core_subset_carrier' hcore) hnormal
  obtain ⟨O, hO, hcapO, hOc⟩ := exists_isOpen_superset_and_isCompact_closure hcapCompact
  have hNO : N.carrier ⊆ O := subset_closure.trans hcapO
  have hNK : N.carrier ⊆ closure O := hNO.trans subset_closure
  obtain ⟨nu, hnu, hanalytic⟩ := N.exists_image_scalarAnalytic_tolerance hCpos heta
  have hmetric := capPersistence_eventually_ordinary_tangent_comparison R p hp hd Conv hOc
  have hscalar := capOrdinaryEmbedding_eventually_scalarAnalytic_close
    R p hp hd Conv hJ hOc nu hnu
  have hjetEnd := capPersistence_eventually_ordinary_neck_error R p hp hd Conv hJ
    N.end_neck (Nat.floor epsilon⁻¹) hend.1 hOc (N.end_neck_subset.trans hNK)
      tau htau hend.2.1
  have hjetBoundary := capPersistence_eventually_ordinary_neck_error R p hp hd Conv hJ
    N.boundary_neck (Nat.floor epsilon⁻¹) hboundary.1 hOc (N.boundary_neck_subset.trans hNK)
      tau htau hboundary.2.1
  filter_upwards [hmetric, hscalar, hjetEnd, hjetBoundary] with k hkmetric hkscalar hkEnd hkBoundary
  let e0 := capOrdinaryEmbedding R p hp hd Conv k
  let e := e0.restrOpen O hO
  let h : RiemannianMetric 3 M := M13.scaleSmoothMetric (F.metric (p (Conv.subsequence k)).1)
    ((ordinaryChapter11Flow (I := I) (F := F) R).scalar (p (Conv.subsequence k)))
    (hp (Conv.subsequence k))
  let D : LeviCivitaData h := M13.scaleLeviCivitaData (F.connection (p (Conv.subsequence k)).1)
    ((ordinaryChapter11Flow (I := I) (F := F) R).scalar (p (Conv.subsequence k)))
    (hp (Conv.subsequence k))
  have heSmooth := capOrdinaryEmbedding_smooth R p hp hd Conv k
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source :=
    heSmooth.1.mono inter_subset_left
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target :=
    heSmooth.2.mono inter_subset_left
  have hsource : N.carrier ⊆ e.source := by
    intro x hx
    exact ⟨hkmetric.1 (hNK hx), hNO hx⟩
  have hupper : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
        2 * (Conv.limit.flow.metric 0).tangentNorm x v :=
    fun x hx v => (hkmetric.2 x (subset_closure hx.2) v).1
  have hlower : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
      (Conv.limit.flow.metric 0).tangentNorm x v ≤
        2 * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) :=
    fun x hx v => (hkmetric.2 x (subset_closure hx.2) v).2
  have htuple : ∀ x ∈ N.carrier,
      ‖(D.scalarCurvature (e x), scalarGradientNorm h D (e x),
          D.laplacian D.scalarCurvature (e x) + 2 * D.ricciNormSq (e x)) -
        (N.connection.scalarCurvature x, scalarGradientNorm (Conv.limit.flow.metric 0)
          N.connection x, N.connection.laplacian N.connection.scalarCurvature x +
            2 * N.connection.ricciNormSq x)‖ ≤ nu := by
    intro x hx
    simpa only [hconnection, e, e0, h, D, OpenPartialHomeomorph.coe_restrOpen] using
      (hkscalar.2 x (hNK hx)).le
  obtain ⟨hscalarNew, hgradient, hevolution, hendScalar, hboundaryScalar, hboundaryLower⟩ :=
    hanalytic h D e hscalarOld htuple
  have hEndEpsilon : N.end_neck.epsilon ≤ epsilon := by
    simpa only [N.end_neck_epsilon] using hNepsilon.le
  have hBoundaryEpsilon : N.boundary_neck.epsilon ≤ epsilon := by
    simpa only [N.boundary_neck_epsilon] using hNepsilon.le
  let qe := (N.end_neck.coordinate_inverse N.end_neck.center).1
  have hshift : epsilon⁻¹ - N.end_neck.epsilon⁻¹ ∈
      Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    have hinv := inv_anti₀ N.end_neck.epsilon_pos hEndEpsilon
    constructor <;> linarith [inv_pos.mpr hepsilon, inv_pos.mpr N.end_neck.epsilon_pos]
  obtain ⟨Eend, heEnd, hdEnd, _hcEnd, _hsEnd, hcarrierEnd, hnegativeEnd⟩ :=
    (hnecks h N.end_neck hEndEpsilon D e hf hi (N.end_neck_subset.trans hsource)
      hkEnd.2.1 hkEnd.2.2).1 qe
        (hendScalar _ (N.end_neck.coordinate_map_mem_of_axial_mem hshift))
  have hcenter : N.boundary_neck.center ∈
      N.boundary_neck.coordinate_map '' (univ ×ˢ ({0} : Set ℝ)) := by
    rw [← N.boundary_neck.central_sphere_eq]
    exact N.boundary_neck.center_on_central_sphere
  obtain ⟨⟨qb, s⟩, ⟨_, hs⟩, hqb⟩ := hcenter
  have hs0 : s = 0 := hs
  subst s
  obtain ⟨Eboundary, heBoundary, hdBoundary, _hcBoundary, _hsBoundary,
      hcarrierBoundary, hsphereBoundary⟩ :=
    (hnecks h N.boundary_neck hBoundaryEpsilon D e hf hi (N.boundary_neck_subset.trans hsource)
      hkBoundary.2.1 hkBoundary.2.2).2 qb (by simpa only [hqb] using hboundaryScalar)
  have hb : -N.epsilon⁻¹ < 2 / epsilon - N.epsilon⁻¹ := by
    linarith [div_pos (by norm_num : (0 : ℝ) < 2) hepsilon]
  have hb' : 2 / epsilon - N.epsilon⁻¹ < N.epsilon⁻¹ := by
    have hinv := (inv_lt_inv₀ hepsilon N.epsilon_pos).mpr hNepsilon
    rw [div_eq_mul_inv]
    linarith
  have hcapture : closure (N.recutCarrier (2 / epsilon - N.epsilon⁻¹)) ⊆ e.source :=
    (N.recutCarrier_compact_closure hb hb').2.trans hsource
  have hcompleteTarget : MetricComplete h := ordinaryCap_scaled_metric_complete
    (F.metric (p (Conv.subsequence k)).1) (hp (Conv.subsequence k))
      (hcomplete _ (ordinaryChapter11Point_time_mem R (p (Conv.subsequence k))))
  obtain ⟨H, heH, hCH, _hDH, hcoreH, _hcarrierH, _hmodelH⟩ :=
    N.exists_image_recut_cap hC1 hC hcompleteLimit hRic (N.core_subset_carrier' hcore) hnormal
      h D hcompleteTarget e hf hi hepsilon hsmall hNepsilon hsource hcapture hupper hlower
      (fun x hx => hscalarNew x (N.recutCarrier_subset_carrier _ hx))
      (fun x hx => hgradient x (N.recutCarrier_subset_carrier _ hx))
      (fun x hx => hevolution x (N.recutCarrier_subset_carrier _ hx))
      hboundaryLower hscale Eend Eboundary heEnd heBoundary hdEnd hdBoundary
      (by simpa only [N.end_neck_epsilon] using hcarrierEnd) hcarrierBoundary
      (by simpa only [← N.boundary_eq_neck_sphere] using hsphereBoundary)
      (by simpa only [N.end_neck_epsilon] using hnegativeEnd)
  refine ⟨H, heH, hCH, ?_⟩
  rw [hcoreH]
  exact ⟨Conv.limit.base, hcore, capOrdinaryEmbedding_base R p hp hd Conv k⟩

end PoincareConjecture.M34

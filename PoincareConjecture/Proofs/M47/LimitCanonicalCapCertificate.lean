import PoincareConjecture.Proofs.M47.LimitCanonicalNeckImage
import PoincareConjecture.Proofs.M47.SeedLimitPhysicalTangent
import PoincareConjecture.Proofs.M47.BlowupControlsCapImageCertificate
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapLimitNormalization
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
private local instance : MeasurableSpace G.limit.carrier.carrier := G.limit.carrier.measurableSpace
private local instance : BorelSpace G.limit.carrier.carrier := G.limit.carrier.borelSpace
private local instance : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
private local instance : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
private local instance : SecondCountableTopology G.limit.carrier.carrier :=
  G.limit.carrier.secondCountable
private local instance : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace

theorem limitCanonical_eventually_cap_certificate
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (N : CapCertificate (G.limit.flow.metric 0))
    (hconnection : N.connection = G.limit.flow.connection 0)
    (hbase : G.limit.base ∈ N.core) :
    ∀ᶠ k in atTop,
      let f := limitCanonicalPhysicalTerminalChart G F R k
      let g := M13.scaleSmoothMetric
        ((F (G.subsequence k)).metric
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
      let D := M13.scaleLeviCivitaData
        ((F (G.subsequence k)).connection
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
      ∃ H : CapCertificate g,
        H.epsilon = N.epsilon ∧ H.cap_constant = N.cap_constant ∧ H.connection = D ∧
        H.core = f '' N.core ∧ H.closed_core = f '' N.closed_core ∧
        H.carrier = f '' N.carrier ∧ H.boundary_sphere = f '' N.boundary_sphere ∧
        H.model_kind = N.model_kind ∧ f G.limit.base ∈ H.core := by
  classical
  let : LocallyCompactSpace G.limit.carrier.carrier :=
    ChartedSpace.locallyCompactSpace E G.limit.carrier.carrier
  obtain ⟨hcomplete, hRicLimit, hnormalLimit⟩ := M34.blowupLimit_zero_geometry G.limit
  have hnormal : N.connection.scalarCurvature G.limit.base = 1 := by
    simpa only [hconnection] using hnormalLimit
  have hRic : ∀ x, ∀ v : TangentSpace (𝓡 3) x, 0 ≤ N.connection.ricci x v v := by
    simpa only [hconnection] using hRicLimit
  have hcapCompact := N.isCompact_closure_of_normalized_base hcomplete
    (N.core_subset_carrier' hbase) hnormal
  obtain ⟨O, hO, hcapO, hK⟩ := exists_isOpen_superset_and_isCompact_closure hcapCompact
  have hNO : N.carrier ⊆ O := subset_closure.trans hcapO
  have hNK : N.carrier ⊆ closure O := hNO.trans subset_closure
  obtain ⟨L, hL, nu, hnu, hcap⟩ :=
    exists_cap_image_certificate_tolerance.{u, 0} N hcomplete hRic
  have hLpos : 0 < L := zero_lt_one.trans hL
  have hinv : L⁻¹ < 1 := (inv_lt_one₀ hLpos).mpr hL
  filter_upwards [Proofs.M47.seedLimit_eventually_physical_tangent_comparison
    G F R hK 0 G.limit.zero_mem (inv_pos.mpr hLpos) hinv,
    limitCanonical_cap_eventually_compact_analytics G P F R hK hnu,
    limitCanonical_eventually_neck_image G P F R N.end_neck
      (N.end_neck_connection.trans hconnection) hK (N.end_neck_subset.trans hNK),
    limitCanonical_eventually_neck_image G P F R N.boundary_neck
      (N.boundary_neck_connection.trans hconnection) hK (N.boundary_neck_subset.trans hNK)]
    with k hm ha he hb
  let f := limitCanonicalPhysicalTerminalChart G F R k
  let e := f.toOpenPartialHomeomorph.restrOpen O hO
  let g : RiemannianMetric 3
      ((F (G.subsequence k)).slice
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))).carrier :=
    M13.scaleSmoothMetric ((F (G.subsequence k)).metric
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
      (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  let D : LeviCivitaData g := M13.scaleLeviCivitaData
    ((F (G.subsequence k)).connection
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  let : CompactSpace
      ((F (G.subsequence k)).slice
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))).carrier :=
    isCompact_univ_iff.mp ((F (G.subsequence k)).slices_compact _
      ((R (G.subsequence k)).time_subset (limitCanonical_terminal_clock_mem G k)))
  have h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source :=
    f.contMDiffOn_toFun.mono inter_subset_left
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target :=
    f.contMDiffOn_invFun.mono inter_subset_left
  have hsource : N.carrier ⊆ e.source := by
    intro x hx
    refine ⟨?_, hNO hx⟩
    change x ∈ (limitCanonicalPhysicalTerminalChart G F R k).source
    rw [limitCanonicalPhysicalTerminalChart, limitCanonicalPhysicalChart_source]
    exact hm.1 (hNK hx)
  have hroot : 0 < Real.sqrt (V.scale (G.subsequence k)) :=
    Real.sqrt_pos.mpr (V.base_scalar_pos (G.subsequence k))
  have hnorm (x : G.limit.sliceCarrier.carrier) (hx : x ∈ e.source)
      (v : TangentSpace (𝓡 3) x) :
      (G.limit.flow.metric 0).tangentNorm x v ≤
          L * g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ∧
        g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
          L * (G.limit.flow.metric 0).tangentNorm x v := by
    have hn := hm.2.2 h0 (limitCanonical_terminal_clock_mem G k) x
      (subset_closure hx.2) v
    change (G.limit.flow.metric 0).tangentNorm x v ≤
        (Real.sqrt (V.scale (G.subsequence k)) / L⁻¹) *
          ((F (G.subsequence k)).metric
            ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))).tangentNorm
              (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ∧
      ((F (G.subsequence k)).metric
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))).tangentNorm
          (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
        (1 / (L⁻¹ * Real.sqrt (V.scale (G.subsequence k)))) *
          (G.limit.flow.metric 0).tangentNorm x v at hn
    constructor
    · refine hn.1.trans_eq ?_
      change _ = L * RiemannianMetric.tangentNorm (M13.scaleSmoothMetric _ _ _) _ _
      rw [M13.scaleSmoothMetric_tangentNorm, div_inv_eq_mul]
      ring
    · change RiemannianMetric.tangentNorm (M13.scaleSmoothMetric _ _ _) _ _ ≤ _
      rw [M13.scaleSmoothMetric_tangentNorm]
      apply (mul_le_mul_of_nonneg_left hn.2 hroot.le).trans_eq
      field_simp
  have hcompare (x : G.limit.sliceCarrier.carrier) (hx : x ∈ N.carrier) :
      |D.scalarCurvature (e x) - N.connection.scalarCurvature x| ≤ nu ∧
      |scalarGradientNorm g D (e x) -
        scalarGradientNorm (G.limit.flow.metric 0) N.connection x| ≤ nu ∧
      |(D.laplacian D.scalarCurvature (e x) + 2 * D.ricciNormSq (e x)) -
        (N.connection.laplacian N.connection.scalarCurvature x +
          2 * N.connection.ricciNormSq x)| ≤ nu := by
    have htuple : ‖(D.scalarCurvature (e x), scalarGradientNorm g D (e x),
        D.laplacian D.scalarCurvature (e x) + 2 * D.ricciNormSq (e x)) -
      (N.connection.scalarCurvature x,
        scalarGradientNorm (G.limit.flow.metric 0) N.connection x,
        N.connection.laplacian N.connection.scalarCurvature x +
          2 * N.connection.ricciNormSq x)‖ ≤ nu := by
      rw [show e x = f x from rfl, hconnection]
      exact ha.2 x (hNK hx)
    exact ⟨(norm_fst_le _).trans htuple, (norm_fst_le _).trans ((norm_snd_le _).trans htuple),
      (norm_snd_le _).trans ((norm_snd_le _).trans htuple)⟩
  obtain ⟨Eend, heEnd, _hxEnd, hdEnd, hcEnd, _hsEnd, _hmEnd, hiEnd, hrEnd⟩ := he.2
  obtain ⟨Eboundary, heBoundary, _hxBoundary, hdBoundary, hcBoundary, hsBoundary,
    _hmBoundary, _hiBoundary, _hrBoundary⟩ := hb.2
  have hregions : Eend.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) =
      e '' N.end_neck.region (-N.epsilon⁻¹) (-N.epsilon⁻¹ / 2) :=
    hrEnd _ _ (by rw [N.end_neck_epsilon]) (by
      rw [N.end_neck_epsilon]
      have h := inv_pos.mpr N.epsilon_pos
      linarith)
  obtain ⟨H, hHe, hHC, hHD, hHcore, hHclosed, hHcarrier, hHboundary, hHmodel,
    _hHend, _hHboundaryNeck⟩ :=
    hcap g D e hf hi hsource (fun x hx v => (hnorm x hx v).2)
      (fun x hx v => (hnorm x hx v).1) hcompare Eend Eboundary
      (heEnd.trans N.end_neck_epsilon) (heBoundary.trans N.boundary_neck_epsilon)
      hdEnd hdBoundary hcEnd hcBoundary
      (by rw [N.boundary_eq_neck_sphere]; exact hsBoundary) hiEnd hregions
  refine ⟨H, hHe, hHC, hHD, hHcore, hHclosed, hHcarrier, hHboundary, hHmodel, ?_⟩
  rw [hHcore]
  exact mem_image_of_mem e hbase

end PoincareConjecture.M47

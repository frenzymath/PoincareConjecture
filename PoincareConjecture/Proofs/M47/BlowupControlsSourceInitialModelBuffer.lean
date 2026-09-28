import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRecentGeometry
import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingBuffer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem exists_source_initial_model_buffer
    {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
    {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck atlas G v gamma z
      (Icc (-v * (G.connection v).scalarCurvature z) 0))
    (hsmall : gamma ≤ 1 / 1200) :
    ∃ r : ℝ, 0 < r ∧ ∃ E : EpsilonNeck (G.metric v),
      E.epsilon = 2 * gamma ∧ E.connection = G.connection v ∧ E.center = z ∧
      E.coordinate_map = N.patch.coordinate ∧ E.coordinate_inverse = N.patch.inverse ∧
      E.carrier = N.patch.coordinate '' (univ ×ˢ Ioo (-gamma⁻¹ / 2) (gamma⁻¹ / 2)) ∧
      E.carrier ⊆ g0.metric.ball 0 r := by
  have hzero : (0 : ℝ) ∈ Icc (-v * (G.connection v).scalarCurvature z) 0 :=
    ⟨mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr N.time_mem.1) N.scalar_pos.le, le_rfl⟩
  let K := (N.staticAtZero hzero).toEpsilonNeck
  have hgamma : 0 < gamma := N.epsilon_pos
  have hge : K.epsilon ≤ 2 * gamma := by change gamma ≤ 2 * gamma; linarith only [hgamma]
  have hhalf : 2 * gamma < 1 / 2 := by linarith only [hsmall]
  let E := K.restrict hge hhalf
  have hwidth : (2 * gamma)⁻¹ < gamma⁻¹ :=
    (inv_lt_inv₀ (by positivity) hgamma).mpr (by linarith only [hgamma])
  have hcompact : IsCompact (K.coordinate_map '' (univ ×ˢ Icc (-(2 * gamma)⁻¹) (2 * gamma)⁻¹)) :=
    K.isCompact_image_closed_axial_interval (neg_lt_neg hwidth) hwidth
  obtain ⟨a, ha, hbuffer⟩ := hcompact.isBounded.subset_ball_lt 0 (0 : StandardCapSpace)
  let r := M36.radialArclength g0 a
  have hr : 0 < r := by
    simpa only [M36.radialArclength_zero] using (M36.radialArclength_strictMono g0) ha
  have hinverse : (2 * gamma)⁻¹ = gamma⁻¹ / 2 := by simp only [mul_inv_rev, div_eq_mul_inv]
  refine ⟨r, hr, E, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      refine ⟨E.coordinate_inverse x, ⟨mem_univ _, ?_⟩,
        E.coordinate_map_coordinate_inverse hx⟩
      have h := (E.coordinate_inverse_mem x hx).2
      change (E.coordinate_inverse x).2 ∈ Ioo (-(2 * gamma)⁻¹) (2 * gamma)⁻¹ at h
      simpa only [hinverse, neg_div] using h
    · rintro ⟨p, hp, rfl⟩
      apply E.coordinate_map_mem_of_axial_mem
      change p.2 ∈ Ioo (-(2 * gamma)⁻¹) (2 * gamma)⁻¹
      simpa only [hinverse, neg_div] using hp.2
  · intro x hx
    rw [M36.standard_ball_eq_euclidean g0 hr, M36.radialEuclideanRadius_arclength]
    apply hbuffer
    refine ⟨E.coordinate_inverse x, ⟨mem_univ _, ?_⟩,
      E.coordinate_map_coordinate_inverse hx⟩
    exact ⟨(E.coordinate_inverse_mem x hx).2.1.le, (E.coordinate_inverse_mem x hx).2.2.le⟩

theorem exists_source_initial_fixed_geometry_tolerance
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {v gamma : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck standard.atlas standard.flow v gamma z
      (Icc (-v * (standard.flow.connection v).scalarCurvature z) 0))
    (hsmall : gamma ≤ 1 / 1200)
    (hdisjoint : Disjoint N.patch.carrier
      {y | g0.metric.edist 0 y ≤ ENNReal.ofReal (g0.cylindrical_end.radius + 4)})
    (hshort : v * (standard.flow.connection v).scalarCurvature z < 1 + gamma) :
    ∃ eta0 delta0 : ℝ, 0 < eta0 ∧ 0 < delta0 ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (T : ℝ) (hT : T ∈ F.surgery_times) (_hn : Nonempty (F.slice T).carrier)
        (i : Fin (F.event T hT).cap_count) (A eta : ℝ) (J : Set ℝ)
        (e : SurgeryFlowCylinder F (F.slice T) T ((F.parameters.h T)⁻¹ ^ 2) J
          ((F.metric T).ball ((F.event T hT).caps i).tip (A * F.parameters.h T)))
        (initial : SurgeryCapInitialComparison F T hT i A),
        SurgeryCapFamilyComparison F S A eta e initial.chart →
      ∀ hzero : (0 : ℝ) ∈ J,
        (∀ y ∈ (F.metric T).ball ((F.event T hT).caps i).tip (A * F.parameters.h T),
          HEq (e.forward 0 hzero y) y) →
        0 < eta → eta ≤ eta0 → ((F.event T hT).necks i).neck.epsilon ≤ delta0 →
      let U := N.patch.coordinate '' (univ ×ˢ Ioo (-gamma⁻¹ / 2) (gamma⁻¹ / 2))
      U ⊆ F.standard_initial.metric.ball 0 A →
      ∀ x ∈ N.patch.carrier, |(N.patch.inverse x).2| ≤ 1 →
      let old := ((F.event T hT).necks i).neck
      let c := (old.coordinate_inverse (sourceInitialOldMap initial x)).2
      x ∈ U ∧ (∀ y ∈ U, initial.chart y ∉ ((F.event T hT).caps i).carrier) ∧
        c + 2 * gamma⁻¹ / 3 < 0 ∧ MapsTo (sourceInitialOldMap initial) U
          (old.region (c - 2 * gamma⁻¹ / 3) (c + 2 * gamma⁻¹ / 3)) := by
  obtain ⟨eta0, delta0, heta0, _hetaSmall, hdelta0, geometry⟩ :=
    exists_source_initial_recent_geometry_tolerance g0 gamma N.epsilon_pos hsmall
  refine ⟨eta0, delta0, heta0, hdelta0, ?_⟩
  intro F hinitial S hS T hT hn i A eta J e initial comparison hzero hbased
    heta hetaSmall hdelta U hsource x hx hheight
  cases hinitial
  cases hS
  exact geometry F rfl T hT i standard.flow A eta J e initial comparison hzero hbased
    heta hetaSmall hdelta standard.atlas v z N hdisjoint hshort hsource x hx hheight

end PoincareConjecture.M47

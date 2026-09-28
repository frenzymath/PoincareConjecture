import PoincareConjecture.Proofs.M35.CapGeometry.InitialNormalizedPatch
import PoincareConjecture.Proofs.M35.CapGeometry.InitialNeckMargin
import PoincareConjecture.Proofs.M35.Prop12_31.ScalarPositivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

theorem exists_initial_evolving_necks {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta epsilon : ℝ}
    (htheta : theta ∈ Ico 0 E.flow.base.lifetime)
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    ∃ K : Set StandardCapSpace, IsCompact K ∧ ∀ x ∉ K, ∀ t ∈ Icc 0 theta,
      ∃ N : StandardEvolvingNeck E.atlas E.flow t epsilon x
          (Icc (-t * (E.flow.connection t).scalarCurvature x) 0),
        Disjoint N.patch.carrier
          {y | g₀.metric.edist 0 y ≤ ENNReal.ofReal (g₀.cylindrical_end.radius + 4)} := by
  obtain ⟨dn, hdn, hnormalize⟩ := exists_initial_normalized_patch_comparison E htheta he
  obtain ⟨dm, hdm, hmargin⟩ := exists_initial_neck_margin g₀.cylindrical_end.radius
    epsilon g₀.cylindrical_end.radius_pos.le he
  let d := min dn dm
  have hd : 0 < d := lt_min hdn hdm
  obtain ⟨A⟩ := E.asymptotic theta htheta d hd
  refine ⟨A.compact_set, A.compact, ?_⟩
  intro x hx t ht
  obtain ⟨N, hN⟩ := A.patches x hx
  obtain ⟨hc, hcsmall, hcl, hclose⟩ :=
    hnormalize d hd (min_le_left _ _) x N hN t ht
  let Q := (E.flow.connection t).scalarCurvature x
  let c := (Real.sqrt Q)⁻¹
  have htime : t ∈ Ico 0 E.flow.base.lifetime := ⟨ht.1, ht.2.trans_lt htheta.2⟩
  have hQ : 0 < Q := E.scalar_pos htime x
  let M := N.axialRescale c epsilon⁻¹ hc (inv_pos.mpr he) hcl
  have hfamily : RoundCylinderFamilyClose d (Icc 0 theta)
      (fun u => roundCylinderPullback (E.flow.metric u) N.coordinate) := by
    simpa only [StandardSpacetimeCylinderClose, div_one, zero_add, one_mul] using hN
  have hzero : (0 : ℝ) ∈ Icc 0 theta := ⟨le_rfl, htheta.1⟩
  have hclosezero : RoundCylinderClose d 0 (roundCylinderPullback g₀.metric N.coordinate) := by
    have hm : E.flow.metric 0 = g₀.metric := E.flow.base.initial_metric
    rw [← hm]
    exact ⟨hfamily.1 0 hzero, hfamily.2.choose, hfamily.2.choose_spec.1,
      hfamily.2.choose_spec.2 0 hzero⟩
  obtain ⟨hcl', _hunitmargin, hdisjoint⟩ := hmargin d hd (min_le_right _ _) g₀.metric
    g₀.connection g₀.rotation_invariant x N hclosezero c hc hcsmall
  let N' : StandardEvolvingNeck E.atlas E.flow t epsilon x (Icc (-t * Q) 0) := {
    time_mem := htime
    epsilon_pos := he
    epsilon_lt_half := hehalf
    scalar_pos := hQ
    patch := M
    interval_survival := fun u hu =>
      ⟨(initial_affine_clock ht hQ hu).1.1,
        (initial_affine_clock ht hQ hu).1.2.trans_lt htheta.2⟩
    close := hclose
  }
  exact ⟨N', hdisjoint⟩

theorem initial_neck_alternative_outside_compact {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta epsilon : ℝ}
    (htheta : theta ∈ Ico 0 E.flow.base.lifetime)
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2) :
    ∃ K : Set StandardCapSpace, IsCompact K ∧ ∀ x ∉ K, ∀ t ∈ Icc 0 theta,
      ∀ C : ℝ, StandardCanonicalAlternative E.atlas E.flow t x epsilon C := by
  obtain ⟨K, hK, hnecks⟩ := exists_initial_evolving_necks E htheta he hehalf
  refine ⟨K, hK, ?_⟩
  intro x hx t ht C
  obtain ⟨N, hdisjoint⟩ := hnecks x hx t ht
  exact StandardCanonicalAlternative.initial_neck N hdisjoint

end PoincareConjecture.M35

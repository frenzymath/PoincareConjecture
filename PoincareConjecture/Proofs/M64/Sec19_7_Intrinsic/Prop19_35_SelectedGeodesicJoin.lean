import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CylindricalContactNormals
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_OppositeGeodesicJoin












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_nonembedded_normal_strip_has_embedded_geodesic
    (N : IntrinsicAnnulus)
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u) {T : ℝ}
    (hperiod : ∀ t, Function.Periodic (fun a => u (a, t)) rampPeriod)
    (hboundary : ∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a)
    (hinside : ∀ a ∈ Ico (0 : ℝ) rampPeriod, ∀ t ∈ Ioc (0 : ℝ) T,
      1 < ‖u (a, t)‖)
    (hregular : ∀ z ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T,
      Function.Injective (fderiv ℝ u z))
    (hunit : ∀ z ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T,
      N.metric.inner (u z) (fderiv ℝ u z (0, 1)) (fderiv ℝ u z (0, 1)) = 1)
    (horth : ∀ z ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T,
      N.metric.inner (u z) (fderiv ℝ u z (0, 1)) (fderiv ℝ u z (1, 0)) = 0)
    (hgeo : ∀ a ∈ Ico (0 : ℝ) rampPeriod,
      N.metric.IsGeodesicOn (fun t => u (a, t)) (Icc (0 : ℝ) T))
    (hfail : ¬InjOn u (Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T)) :
    ∃ (a b R : ℝ) (gamma : ℝ → AnnulusCoordinates),
      a ∈ Ico (0 : ℝ) rampPeriod ∧ b ∈ Ico (0 : ℝ) rampPeriod ∧ a ≠ b ∧
      0 < R ∧ R ≤ T ∧ ContDiff ℝ ∞ gamma ∧
      N.metric.IsGeodesicOn gamma (Icc (0 : ℝ) (R + R)) ∧
      InjOn gamma (Icc (0 : ℝ) (R + R)) ∧
      gamma 0 = intrinsicAnnulusBoundary 1 a ∧
      gamma (R + R) = intrinsicAnnulusBoundary 1 b ∧
      gamma '' Icc (0 : ℝ) (R + R) =
        (fun t => u (a, t)) '' Icc 0 R ∪ (fun t => u (b, t)) '' Icc 0 R ∧
      (∀ t ∈ Icc (0 : ℝ) (R + R),
        N.metric.inner (gamma t) (deriv gamma t) (deriv gamma t) = 1) ∧
      (∀ t ≤ R, gamma t = u (a, t)) ∧
      (∀ t ≥ R, gamma t = u (b, R + R - t)) ∧
      ∀ t ∈ Ioo (0 : ℝ) (R + R), 1 < ‖gamma t‖ := by
  have hP : 0 < rampPeriod := by unfold rampPeriod; positivity
  obtain ⟨a, b, R, ha, hb, hab, hR, hRT, hmeet, hopp, hbelow⟩ :=
    m64Intrinsic_nonembedded_normal_strip_has_opposite_contact N.metric hu hperiod
      hboundary hinside hregular hunit horth hfail
  have hcollision (p q : ℝ × ℝ)
      (hp : p ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) R)
      (hq : q ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) R)
      (heq : u p = u q) : p = q ∨ p.2 = R ∧ q.2 = R := by
    by_cases hpq : p = q
    · exact Or.inl hpq
    have hpT : p ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T :=
      ⟨hp.1, hp.2.1, hp.2.2.trans hRT⟩
    have hqT : q ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T :=
      ⟨hq.1, hq.2.1, hq.2.2.trans hRT⟩
    obtain ⟨hp0, hq0⟩ := m64Intrinsic_normal_collision_heights_pos
      hboundary hinside hpT hqT hpq heq
    have h := m64Intrinsic_cylindrical_normal_contact_opposite N.metric hu hP hp.1 hq.1
      ⟨hp0, hp.2.2⟩ ⟨hq0, hq.2.2⟩ hpq heq hbelow (hregular p hpT)
      (hregular q hqT) (hunit p hpT) (hunit q hqT) (horth p hpT) (horth q hqT)
    exact Or.inr ⟨h.1, h.2.1⟩
  have hri (c : ℝ) (hc : c ∈ Ico (0 : ℝ) rampPeriod) :
      InjOn (fun t => u (c, t)) (Icc (0 : ℝ) R) := by
    intro s hs t ht hst
    rcases hcollision (c, s) (c, t) ⟨hc, hs⟩ ⟨hc, ht⟩ hst with heq | ⟨hsR, htR⟩
    · exact congrArg Prod.snd heq
    · exact hsR.trans htR.symm
  have hcontact : ∀ s ∈ Icc (0 : ℝ) R, ∀ t ∈ Icc (0 : ℝ) R,
      u (a, s) = u (b, t) → s = R ∧ t = R := by
    intro s hs t ht hst
    rcases hcollision (a, s) (b, t) ⟨ha, hs⟩ ⟨hb, ht⟩ hst with heq | hends
    · exact (hab (congrArg Prod.fst heq)).elim
    · exact hends
  have hray (c : ℝ) : ContDiff ℝ ∞ (fun t => u (c, t)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hder (c t : ℝ) : deriv (fun s => u (c, s)) t = fderiv ℝ u (c, t) (0, 1) :=
    ((hu.differentiable (by simp) (c, t)).hasFDerivAt.comp_hasDerivAt
      (f := fun s : ℝ => (c, s)) t ((hasDerivAt_const t c).prodMk (hasDerivAt_id t))).deriv
  have hgr (c : ℝ) (hc : c ∈ Ico (0 : ℝ) rampPeriod) :
      N.metric.IsGeodesicOn (fun t => u (c, t)) (Icc (0 : ℝ) R) :=
    fun t ht => hgeo c hc t ⟨ht.1, ht.2.trans hRT⟩
  obtain ⟨gamma, hleft, hright, hg, hgg, hgi, hg0, hgend, himage⟩ :=
    m64Intrinsic_opposite_first_contact_embedded_join N.metric (hray a) (hray b)
      (hgr a ha) (hgr b hb) hR hR hmeet (by simpa only [hder] using hopp)
      (hri a ha) (hri b hb) hcontact
  have hinit : N.metric.inner (gamma 0) (curveVelocity (n := 2) gamma 0)
      (curveVelocity (n := 2) gamma 0) = 1 := by
    have heq : gamma =ᶠ[𝓝 (0 : ℝ)] (fun t => u (a, t)) := by
      filter_upwards [Iio_mem_nhds hR] with t ht
      exact hleft t ht.le
    rw [m64Intrinsic_curveVelocity_eq_deriv, heq.deriv_eq, hder, hg0]
    exact hunit (a, 0) ⟨ha, le_rfl, hR.le.trans hRT⟩
  have hgu := m64Intrinsic_geodesic_velocity_unit N (by linarith : 0 < R + R)
    hgg (Subset.refl _) hinit
  refine ⟨a, b, R, gamma, ha, hb, hab, hR, hRT, hg, hgg, hgi,
    hg0.trans (hboundary a), hgend.trans (hboundary b), himage, ?_, hleft, hright, ?_⟩
  · intro t ht
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using hgu t ht
  · intro t ht
    by_cases htR : t ≤ R
    · rw [hleft t htR]
      exact hinside a ha t ⟨ht.1, htR.trans hRT⟩
    · rw [hright t (le_of_not_ge htR)]
      exact hinside b hb (R + R - t) ⟨by linarith [ht.2], by linarith⟩

end PoincareConjecture

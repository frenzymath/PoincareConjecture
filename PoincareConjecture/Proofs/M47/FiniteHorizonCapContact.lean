import PoincareConjecture.Proofs.M47.BlowupControlsSourceBall
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47



theorem finiteHorizon_cap_contact_of_no_source
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {base Q duration A : ℝ}
    (hbase : base ∈ H.generalized.interval) (hQ : 0 < Q)
    (hduration : 0 < duration) (hA : 0 < A)
    (hwindow : Icc (base - 2 * duration / Q) base ⊆ F.time_domain)
    (y : (F.slice base).carrier)
    (hfail : ¬ ∃ _htime : ∀ s ∈ Icc (-duration) 0,
        base + s / Q ∈ H.generalized.interval,
      Nonempty (GeneralizedFlowCylinder H.generalized (F.slice base) base Q
        (Icc (-duration) 0) ((F.metric base).ball y (A / Real.sqrt Q)))) :
    ∃ (a : ℝ) (ha : a ∈ Icc (-duration) 0),
      ∃ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
          ((F.metric base).ball y (A / Real.sqrt Q)),
        (∀ hs z, z ∈ (F.metric base).ball y (A / Real.sqrt Q) →
          HEq (e.forward 0 hs z) z) ∧
        ∃ hEvent : base + a / Q ∈ F.surgery_times,
          ∀ [Nonempty (F.slice (base + a / Q)).carrier],
            ∃ i : Fin (F.event (base + a / Q) hEvent).cap_count,
              (e.forward a ⟨le_rfl, ha.2⟩ ''
                  (F.metric base).ball y (A / Real.sqrt Q) ∩
                ((F.event (base + a / Q) hEvent).caps i).carrier).Nonempty := by
  obtain ⟨U, hU, _p0, _hp0, hsearch⟩ :=
    exists_blowup_six_radius_source_or_cap H hbase hQ hduration
      (R := A / 6) (div_pos hA (by norm_num)) hwindow y
  have hsource : (U : Set (F.slice base).carrier) =
      (F.metric base).ball y (A / Real.sqrt Q) := by
    simpa only [show 6 * (A / 6) = A by ring] using hU
  rcases hsearch with ⟨htime, d, _hidentity, _himage⟩ | hcap
  · exfalso
    apply hfail
    refine ⟨htime, ?_⟩
    simpa only [hsource] using
      (show Nonempty (GeneralizedFlowCylinder H.generalized (F.slice base) base Q
        (Icc (-duration) 0) U) from ⟨d⟩)
  · obtain ⟨a, ha, e, hbased, hEvent, hcap⟩ := hcap
    have hsub : (F.metric base).ball y (A / Real.sqrt Q) ⊆ U :=
      hsource.symm.subset
    let E := e.restrict (Subset.refl (Icc a 0)) ordConnected_Icc hsub
    refine ⟨a, ha, E, fun hs z hz => hbased hs z (hsub hz), hEvent, ?_⟩
    intro hn
    obtain ⟨i, z, hzimage, hzcap⟩ := hcap
    obtain ⟨w, hw, rfl⟩ := hzimage
    refine ⟨i, e.forward a ⟨le_rfl, ha.2⟩ w, ?_, hzcap⟩
    exact ⟨w, hsource.subset hw, rfl⟩

end PoincareConjecture.M47

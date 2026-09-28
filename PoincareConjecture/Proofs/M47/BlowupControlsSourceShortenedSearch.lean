import PoincareConjecture.Proofs.M47.BlowupControlsSourceCylinder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

theorem exists_first_failure_controlled_shortened_source_or_cap
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C) {A : ℝ} (hA : 0 < A) :
    ∃ Q0 tauMax K : ℝ, 0 < Q0 ∧ 0 < tauMax ∧ tauMax ≤ 1 ∧ 0 < K ∧
      ∀ tau : ℝ, 0 < tau → tau ≤ tauMax →
      ∀ (p : SurgeryParameterPrefix S.constants) (F : SurgeryFlowData.{u})
        (O : SurgeryObservation F),
      F.standard_initial = S.setup.standard_initial → F.local_constants = S.constants →
      F.parameters.epsilon = S.setup.epsilon → F.parameters.C = S.setup.C →
      ∀ (W : M33RegularHistoryWindow F) (H : M33RegularHistoryData W)
        {base Q r : ℝ} (ht : base ∈ H.generalized.interval),
      base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → r⁻¹ ^ 2 ≤ Q →
      SurgeryFlowPinched F →
      SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) r →
      (∀ t ∈ surgeryObservationInterval O ∩ Ico (surgeryEpochStart (p.i - 1)) O.H,
        F.parameters.delta t ≤ B.delta S.setup.standard_initial S.constants) →
      ∀ x : (H.generalized.slice base).carrier,
      H.generalized.scalar ⟨base, x⟩ = Q →
        (∃ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc (-tau) 0)
            ((F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q)),
          (∀ hs y,
            y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
              HEq (e.forward 0 hs y) y) ∧
          ∀ s hs y,
            y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
              (F.connection (base + s / Q)).curvatureTensorNorm
                (e.forward s hs y) ≤ K * Q) ∨
        ∃ (a : ℝ) (ha : a ∈ Icc (-tau) 0),
          ∃ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
              ((F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q)),
            (∀ hs y,
              y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
                HEq (e.forward 0 hs y) y) ∧
            ∃ hT : base + a / Q ∈ F.surgery_times,
              ∀ [Nonempty (F.slice (base + a / Q)).carrier],
                ∃ i : Fin (F.event (base + a / Q) hT).cap_count,
                  (e.forward a ⟨le_rfl, ha.2⟩ ''
                      (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) ∩
                    ((F.event (base + a / Q) hT).caps i).carrier).Nonempty := by
  obtain ⟨Qmin, tauMax, K, hQmin, htauMax, htauMaxOne, hK, geometry⟩ :=
    exists_first_failure_short_search_geometry P S B hA.le
  refine ⟨max Qmin 192, tauMax, K, hQmin.trans_le (le_max_left _ _),
    htauMax, htauMaxOne, hK, ?_⟩
  intro tau htau hshort p F O hInitial hConstants hEpsilon hC W H base Q r ht
    hBase hLarge hThreshold hPinched hEarlier hOverlap x hscale
  have hQminQ : Qmin ≤ Q := (le_max_left _ _).trans hLarge
  have h192 : 192 ≤ Q := (le_max_right _ _).trans hLarge
  have hQ : 0 < Q := hQmin.trans_le hQminQ
  have htauOne : tau ≤ 1 := hshort.trans htauMaxOne
  have hJ : Icc (base - 2 * tau / Q) base ⊆ F.time_domain :=
    terminalCommonInterval_search_window p O hBase (by positivity)
      (by linarith only [htauOne, h192])
  obtain ⟨U, hU, p0, _hp0, hsearch⟩ :=
    exists_blowup_six_radius_source_or_cap H ht hQ htau
      (by positivity : 0 < A / 6) hJ (H.history.forward base ht x)
  have hUball : (U : Set (F.slice base).carrier) =
      (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) := by
    simpa only [show 6 * (A / 6) = A by ring] using hU
  have hspace : (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) ⊆ U :=
    hUball.symm.subset
  rcases hsearch with ⟨htime, d, hid, _hcover⟩ | ⟨a, ha, e, hbased, hT, hcap⟩
  · let e := terminalSourceNormal_historyCylinder H U htime d
    let h0 : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau.le, le_rfl⟩
    have hbased := source_cylinder_based_of_terminal_map U p0 e h0 hid
    let eBall := e.restrict (Subset.refl (Icc (-tau) 0)) ordConnected_Icc hspace
    have hbasedBall : ∀ hs y,
        y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
          HEq (eBall.forward 0 hs y) y :=
      fun hs y hy => hbased hs y (hspace hy)
    refine Or.inl ⟨eBall, hbasedBall, ?_⟩
    have hgeometry := geometry p F O hInitial hConstants hEpsilon hC W H ht hBase
      hQminQ hThreshold hPinched hEarlier hOverlap
      (show -tau ∈ Ico (-tauMax) 0 from ⟨neg_le_neg hshort, neg_lt_zero.mpr htau⟩)
      x hscale eBall hbasedBall
    intro s hs y hy
    exact (abs_le.mp (hgeometry s hs y hy).2.1).2
  · let eBall := e.restrict (Subset.refl (Icc a 0)) ordConnected_Icc hspace
    refine Or.inr ⟨a, ha, eBall, fun hs y hy => hbased hs y (hspace hy), hT, ?_⟩
    intro hn
    obtain ⟨i, hi⟩ := hcap
    refine ⟨i, ?_⟩
    change (e.forward a ⟨le_rfl, ha.2⟩ ''
      (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) ∩
        ((F.event (base + a / Q) hT).caps i).carrier).Nonempty
    rwa [← hUball]

end PoincareConjecture.M47

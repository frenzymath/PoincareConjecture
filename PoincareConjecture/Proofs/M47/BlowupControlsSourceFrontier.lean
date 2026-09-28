import PoincareConjecture.Proofs.M47.BlowupControlsSourcePaths
import PoincareConjecture.Proofs.M34.Mathlib.FirstExitOpen










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {base : ℝ} (ht : base ∈ H.generalized.interval)



theorem cap_contact_of_not_regular_history
    (hT : base ∈ F.surgery_times) [Nonempty (F.slice base).carrier]
    (z : (F.slice base).carrier)
    (hz : z ∉ range (H.history.forward base ht)) :
    ∃ i : Fin (F.event base hT).cap_count, z ∈ ((F.event base hT).caps i).carrier := by
  classical
  let E := F.event base hT
  let K : Set (F.slice base).carrier := ⋃ i : Fin E.cap_count, (E.caps i).carrier
  have hK : IsClosed K := isClosed_iUnion_of_finite (fun i => (E.caps i).carrier_compact.isClosed)
  have hret : Kᶜ ⊆ interior E.retained_post := by
    apply hK.isOpen_compl.subset_interior_iff.mpr
    intro y hy
    have hcover : y ∈ E.retained_post ∪ K := by
      change y ∈ E.retained_post ∪ ⋃ i, (E.caps i).carrier
      rw [E.post_cover]
      exact mem_univ y
    exact hcover.resolve_right hy
  have hcap : z ∈ K := by
    by_contra hnot
    apply hz
    rw [H.regular_range]
    intro hT'
    exact hret hnot
  exact mem_iUnion.mp hcap




theorem exists_cap_contact_scalar_of_bounded_distance
    {Q A D : ℝ} (hQ : 0 < Q)
    (x : (H.generalized.slice base).carrier)
    (hscale : H.generalized.scalar ⟨base, x⟩ = Q)
    (hestimate : RepairedBoundedDistanceEstimate H.generalized A D base x)
    (hT : base ∈ F.surgery_times) [Nonempty (F.slice base).carrier]
    (i : Fin (F.event base hT).cap_count) (y : (F.slice base).carrier)
    (hy : y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q))
    (hycap : y ∈ ((F.event base hT).caps i).carrier) :
    ∃ j : Fin (F.event base hT).cap_count, ∃ z : (F.slice base).carrier,
      z ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) ∧
      z ∈ ((F.event base hT).caps j).carrier ∧
      (F.connection base).scalarCurvature z ≤ D * Q := by
  classical
  obtain ⟨gamma, hzero, hone, hgamma, hlength, hball⟩ :=
    (F.metric base).exists_short_path_in_ball (H.history.forward base ht x) y hy
  let V := range (H.history.forward base ht)
  have hV : IsOpen V := (H.history.forward_openEmbedding base ht).isOpen_range
  by_cases hretain : MapsTo gamma (Icc (0 : ℝ) 1) V
  · refine ⟨i, y, hy, hycap, ?_⟩
    have hbound := regular_history_path_prefix_scalar_bound H ht hQ x hscale hestimate
      hgamma hzero hlength (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hretain
    simpa only [hone] using hbound
  · obtain ⟨b, hb, hbnot⟩ : ∃ b ∈ Icc (0 : ℝ) 1, gamma b ∉ V := by
      by_contra hnot
      apply hretain
      intro b hb
      by_contra hbnot
      exact hnot ⟨b, hb, hbnot⟩
    obtain ⟨t, ht', hfront, hbefore⟩ :=
      (hgamma.continuousOn.mono (Icc_subset_Icc le_rfl hb.2)).exists_first_exit_open
        hb.1 hV (by rw [hzero]; exact mem_range_self x) hbnot
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht'.1.le, ht'.2.trans hb.2⟩
    have htNot : gamma t ∉ V := by
      simpa only [hV.interior_eq] using hfront.2
    obtain ⟨j, hj⟩ := cap_contact_of_not_regular_history H ht hT (gamma t) htNot
    refine ⟨j, gamma t, hball ht01, hj, ?_⟩
    have hscalarBefore : (fun s => (F.connection base).scalarCurvature (gamma s)) ''
        Ico (0 : ℝ) t ⊆ Iic (D * Q) := by
      rintro _ ⟨s, hs, rfl⟩
      apply regular_history_path_prefix_scalar_bound H ht hQ x hscale hestimate
        hgamma hzero hlength ⟨hs.1, hs.2.le.trans ht01.2⟩
      intro v hv
      exact hbefore v ⟨hv.1, hv.2.trans_lt hs.2⟩
    have hcontinuous : ContinuousWithinAt
        (fun s => (F.connection base).scalarCurvature (gamma s)) (Ico (0 : ℝ) t) t :=
      (((M34.contMDiff_scalarCurvature (F.connection base)).continuous.comp_continuousOn
        hgamma.continuousOn) t ht01).mono
          (fun s hs => ⟨hs.1, hs.2.le.trans ht01.2⟩)
    have htClosure : t ∈ closure (Ico (0 : ℝ) t) := by
      rw [closure_Ico ht'.1.ne]
      exact ⟨ht'.1.le, le_rfl⟩
    exact closure_minimal hscalarBefore isClosed_Iic
      (hcontinuous.mem_closure_image htClosure)



theorem exists_zero_age_cap_contact_scalar_bound
    (S : RepairedControlledSchedulesData.{u}) {epsilon C A : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ S.calibration.epsilon₁₀)
    (hC : 0 < C) (hA : 0 ≤ A) :
    ∃ D0 D : ℝ, 0 < D0 ∧ 0 < D ∧
      ∀ (F : SurgeryFlowData.{u}) (W : M33RegularHistoryWindow F)
        (H : M33RegularHistoryData W) {base Q r : ℝ}
        (ht : base ∈ H.generalized.interval), 0 < base → 0 < Q →
      F.parameters.epsilon = epsilon → F.parameters.C = C →
      SurgeryFlowPinched F → SurgeryCanonicalOn F (Ico 0 base) r →
      r⁻¹ ^ 2 ≤ Q → ∀ x : (H.generalized.slice base).carrier,
      H.generalized.scalar ⟨base, x⟩ = Q → D0 ≤ Q →
      ∀ (hT : base ∈ F.surgery_times), ∀ [Nonempty (F.slice base).carrier],
      ∀ (i : Fin (F.event base hT).cap_count) (y : (F.slice base).carrier),
      y ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) →
      y ∈ ((F.event base hT).caps i).carrier →
      ∃ j : Fin (F.event base hT).cap_count, ∃ z : (F.slice base).carrier,
        z ∈ (F.metric base).ball (H.history.forward base ht x) (A / Real.sqrt Q) ∧
        z ∈ ((F.event base hT).caps j).carrier ∧
        (F.connection base).scalarCurvature z ≤ D * Q := by
  obtain ⟨D0, D, hD0, hD, estimate⟩ :=
    exists_regular_history_bounded_distance S epsilon hepsilon hepsilonSmall C hC A hA
  refine ⟨D0, D, hD0, hD, ?_⟩
  intro F W H base Q r ht hbase hQ he hCeq hpinch hpast hthreshold x hscale
    hlarge hT hn i y hy hycap
  apply exists_cap_contact_scalar_of_bounded_distance H ht hQ x hscale
    (hT := hT) (i := i) (y := y) (hy := hy) (hycap := hycap)
  apply estimate F W H (fun s hs => hpinch s (W.time_subset hs)) base ht hbase x
    (by simpa only [hscale] using hlarge)
  intro s hs hsb _hregular z hz
  have hQle : Q ≤ (F.connection s).scalarCurvature z := by
    rw [hscale] at hz
    linarith only [hz, hQ]
  have hc := hpast s ⟨F.time_domain_nonnegative (W.time_subset hs), hsb⟩
    (W.time_subset hs) z (hthreshold.trans hQle)
  simpa only [he, hCeq] using hc

end PoincareConjecture.M47

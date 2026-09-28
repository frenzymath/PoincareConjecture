import PoincareConjecture.Proofs.M47.BlowupControlsSourceShortenedSearch
import PoincareConjecture.Proofs.M47.BlowupControlsSourcePositiveCapCanonical
import PoincareConjecture.Proofs.M47.BlowupControlsSourceZeroCapCanonical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

private theorem canonicalCylinder_zero_contact_of_based
    {F : SurgeryFlowData.{u}} {base Q : ℝ} {U : Set (F.slice base).carrier}
    (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc 0 0) U)
    (hbased : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (hcontact : ∃ hT : base + 0 / Q ∈ F.surgery_times,
      ∀ [Nonempty (F.slice (base + 0 / Q)).carrier],
        ∃ i : Fin (F.event (base + 0 / Q) hT).cap_count,
          (e.forward 0 ⟨le_rfl, le_rfl⟩ '' U ∩
            ((F.event (base + 0 / Q) hT).caps i).carrier).Nonempty) :
    ∃ hT : base ∈ F.surgery_times, ∀ [Nonempty (F.slice base).carrier],
      ∃ i : Fin (F.event base hT).cap_count,
        ∃ y ∈ U, y ∈ ((F.event base hT).caps i).carrier := by
  let Contact (p : (t : ℝ) × (U → (F.slice t).carrier)) : Prop :=
    ∃ hT : p.1 ∈ F.surgery_times, ∀ [Nonempty (F.slice p.1).carrier],
      ∃ i : Fin (F.event p.1 hT).cap_count,
        (range p.2 ∩ ((F.event p.1 hT).caps i).carrier).Nonempty
  have hsource : Contact ⟨base + 0 / Q,
      fun z : U => e.forward 0 ⟨le_rfl, le_rfl⟩ z.1⟩ := by
    obtain ⟨hT, hcontact⟩ := hcontact
    refine ⟨hT, ?_⟩
    intro hn
    obtain ⟨i, z, ⟨y, hy, rfl⟩, hz⟩ := hcontact
    exact ⟨i, _, ⟨⟨y, hy⟩, rfl⟩, hz⟩
  have hmap : (⟨base + 0 / Q, fun z : U => e.forward 0 ⟨le_rfl, le_rfl⟩ z.1⟩ :
      (t : ℝ) × (U → (F.slice t).carrier)) = ⟨base, fun z : U => z.1⟩ := by
    apply Sigma.ext (by simp)
    apply Function.hfunext rfl
    intro z w hzw
    cases hzw
    exact hbased _ z.1 z.2
  have htarget : Contact ⟨base, fun z : U => z.1⟩ :=
    (congrArg Contact hmap).mp hsource
  obtain ⟨hT, htarget⟩ := htarget
  refine ⟨hT, ?_⟩
  intro hn
  obtain ⟨i, z, ⟨y, rfl⟩, hz⟩ := htarget
  exact ⟨i, y.1, y.2, hz⟩

theorem exists_first_failure_source_cylinder_of_pointwise
    (P : M46Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    {Asearch : ℝ} (hAsearch : 0 < Asearch)
    (pointwise : ∀ theta : ℝ, theta < 1 → ∀ v ∈ Icc 0 theta,
      ∀ z : StandardCapSpace,
      ∃ A0 eta0 nearTime Q0 : ℝ, ∃ V : Set StandardCapSpace,
        0 < A0 ∧ 0 < eta0 ∧ 0 < nearTime ∧ 0 < Q0 ∧ IsOpen V ∧ z ∈ V ∧
        ∀ A : ℝ, A0 ≤ A → ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
        ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
          ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
          ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
            O.H ≤ surgeryEpochStart (p.i + 1) →
          ∀ prior : SurgeryPrefixControls p F O,
            SurgeryFlowAdmissible F → SurgeryFlowPinched F →
            SurgeryPostPrefixScales p F O rNext cutoff →
            (∀ b ∈ surgeryObservationInterval O ∩ overlapInterval p,
              F.parameters.delta b ≤ cutoff) →
          ∀ (t : ℝ) (hT : t ∈ F.surgery_times),
          ∀ [Nonempty (F.slice t).carrier], ∀ (i : Fin (F.event t hT).cap_count)
            (J : Set ℝ)
            (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
              ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
            (initial : SurgeryCapInitialComparison F t hT i A),
            SurgeryCapFamilyComparison F
              (O.redecorateTo prior.standard_initial_eq).standard_flow A eta e initial.chart →
          ∀ hzero : (0 : ℝ) ∈ J,
            (∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
              HEq (e.forward 0 hzero y) y) →
            0 < F.parameters.h t →
          ∀ (s : ℝ) (hs : s ∈ J), s ∈ Icc 0 theta → Icc 0 s ⊆ J →
            |s - v| < nearTime → ∀ z' ∈ V,
            let base := t + s / ((F.parameters.h t)⁻¹ ^ 2)
            let x := e.forward s hs (initial.chart z')
            let Q := (F.connection base).scalarCurvature x
            base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → rNext⁻¹ ^ 2 ≤ Q →
            SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
            Q * (base - t) ∈ Icc 0 1 →
            SurgeryCanonicalControl F base x S.setup.epsilon S.setup.C) :
    ∃ Q0 tau K : ℝ, 0 < Q0 ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < K ∧
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          O.H ≤ surgeryEpochStart (p.i + 1) →
        ∀ _prior : SurgeryPrefixControls p F O,
          SurgeryFlowAdmissible F → SurgeryFlowPinched F →
          SurgeryPostPrefixScales p F O rNext cutoff →
          (∀ b ∈ surgeryObservationInterval O ∩ overlapInterval p,
            F.parameters.delta b ≤ cutoff) →
        ∀ (W : M33RegularHistoryWindow F) (H : M33RegularHistoryData W)
          {base Q : ℝ} (ht : base ∈ H.generalized.interval),
          base ∈ Ico (surgeryEpochStart p.i) O.H → Q0 ≤ Q → rNext⁻¹ ^ 2 ≤ Q →
          SurgeryCanonicalOn F (surgeryObservationInterval O ∩ Iio base) rNext →
        ∀ x : (H.generalized.slice base).carrier,
          H.generalized.scalar ⟨base, x⟩ = Q →
          ¬ SurgeryCanonicalControl F base (H.history.forward base ht x)
            F.parameters.epsilon F.parameters.C →
          ∃ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc (-tau) 0)
              ((F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q)),
            (∀ hs y,
              y ∈ (F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q) →
                HEq (e.forward 0 hs y) y) ∧
            ∀ s hs y,
              y ∈ (F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q) →
                (F.connection (base + s / Q)).curvatureTensorNorm
                  (e.forward s hs y) ≤ K * Q := by
  obtain ⟨Qsearch, tauMax, K, hQsearch, htauMax, htauMaxOne, hK, search⟩ :=
    exists_first_failure_controlled_shortened_source_or_cap P S B hAsearch
  obtain ⟨Qpositive, tauPositive, hQpositive, htauPositive, _htauPositiveOne, positive⟩ :=
    exists_first_failure_positive_cap_canonical_cutoff P S B p hp hAsearch pointwise
  obtain ⟨Qzero, _hQzero, zero⟩ :=
    exists_first_failure_zero_cap_canonical_cutoff S p hp hAsearch pointwise
  let tau := min tauMax tauPositive
  have htau : 0 < tau := lt_min htauMax htauPositive
  refine ⟨max Qsearch (max Qpositive Qzero), tau, K,
    hQsearch.trans_le (le_max_left _ _), htau,
    (min_le_left _ _).trans htauMaxOne, hK, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨deltaPositive, hdeltaPositive, hdeltaLast, applyPositive⟩ :=
    positive rNext hrNext hrLast
  obtain ⟨deltaZero, hdeltaZero, _hdeltaZeroLast, applyZero⟩ := zero rNext hrNext hrLast
  let cutoff := min deltaPositive (min deltaZero (B.delta S.setup.standard_initial S.constants))
  have hcutPositive : cutoff ≤ deltaPositive := min_le_left _ _
  have hcutZero : cutoff ≤ deltaZero := (min_le_right _ _).trans (min_le_left _ _)
  have hcutAnalytic : cutoff ≤ B.delta S.setup.standard_initial S.constants :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cutoff, lt_min hdeltaPositive (lt_min hdeltaZero (B.delta_pos _ _)),
    hcutPositive.trans hdeltaLast, ?_⟩
  intro F O hH prior hadmissible hpinch next overlap W H base Q ht hBase hLarge
    hScale hEarlier x hscale hfail
  have hQsearchQ : Qsearch ≤ Q := (le_max_left _ _).trans hLarge
  have hQpositiveQ : Qpositive ≤ Q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hLarge)
  have hQzeroQ : Qzero ≤ Q :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hLarge)
  have hInitial : F.standard_initial = S.setup.standard_initial := by
    rw [prior.standard_initial_eq, hp.setup_eq]
  have hepsilon : F.parameters.epsilon = S.setup.epsilon := by
    rw [prior.epsilon_eq, hp.setup_eq]
  have hC : F.parameters.C = S.setup.C := by rw [prior.C_eq, hp.setup_eq]
  have analytic : ∀ b ∈ surgeryObservationInterval O ∩
      Ico (surgeryEpochStart (p.i - 1)) O.H,
      F.parameters.delta b ≤ B.delta S.setup.standard_initial S.constants := by
    intro b hb
    exact (overlap b ⟨hb.1, hb.2.1, hb.2.2.trans_le hH⟩).trans hcutAnalytic
  have alternatives := search tau htau (min_le_left _ _) p F O hInitial
    prior.local_constants_eq hepsilon hC W H ht hBase hQsearchQ hScale hpinch
    hEarlier analytic x hscale
  rcases alternatives with hlong | ⟨a, ha, e, hbased, hT, hcap⟩
  · exact hlong
  · exfalso
    apply hfail
    by_cases hnegative : a < 0
    · let : Nonempty (F.slice (base + a / Q)).carrier :=
        ⟨e.forward a ⟨le_rfl, ha.2⟩ (H.history.forward base ht x)⟩
      obtain ⟨i, y, ⟨contact, hcontact, rfl⟩, hycap⟩ := hcap
      exact applyPositive F O hH prior hadmissible hpinch (next.mono_delta hcutPositive)
        (fun b hb => (overlap b hb).trans hcutPositive) W H ht hBase hQpositiveQ
        hScale hEarlier ⟨(neg_le_neg (min_le_right _ _)).trans ha.1, hnegative⟩
        x hscale e hbased hT i contact hcontact hycap
    · have haZero : a = 0 := le_antisymm ha.2 (le_of_not_gt hnegative)
      subst a
      obtain ⟨hTbase, contact⟩ :=
        canonicalCylinder_zero_contact_of_based e hbased ⟨hT, hcap⟩
      let : Nonempty (F.slice base).carrier := ⟨H.history.forward base ht x⟩
      obtain ⟨i, y, hy, hycap⟩ := contact
      exact applyZero F O hH prior hadmissible hpinch (next.mono_delta hcutZero)
        (fun b hb => (overlap b hb).trans hcutZero) W H ht hBase hQzeroQ
        hScale hEarlier x hscale hTbase i y hy hycap

end PoincareConjecture.M47

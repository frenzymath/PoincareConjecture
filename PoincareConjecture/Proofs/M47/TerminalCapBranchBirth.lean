import PoincareConjecture.Proofs.M47.BlowupControlsSourceCapBirthBridge









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47



theorem terminal_cap_branch_positive_birth
    {F : SurgeryFlowData.{u}} (O : SurgeryObservation F)
    {C : GeneralizedSliceCarrier.{u}} {base Q a : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C base Q (Icc a 0) U) (ha : a < 0)
    (hbirthH : base + a / Q < O.H) {A K eta theta : ℝ}
    (hT : base + a / Q ∈ F.surgery_times)
    [Nonempty (F.slice (base + a / Q)).carrier]
    (i : Fin (F.event (base + a / Q) hT).cap_count)
    (hA : F.standard_initial.cylindrical_end.radius + 5 < A)
    (hscalar : ∀ s (hs : s ∈ Icc a 0), ∀ y ∈ U,
      (F.connection (base + s / Q)).scalarCurvature (e.forward s hs y) ≤ K * Q)
    (hpersist : SurgeryCapPersistenceAlternative F O (base + a / Q)
      hT i A eta theta)
    (hmargin : (O.H - (base + a / Q)) /
      (F.parameters.h (base + a / Q)) ^ 2 < theta)
    {V : Set (F.slice (base + a / Q)).carrier}
    (f : SurgeryFlowCylinder F (F.slice (base + a / Q)) (base + a / Q)
      ((F.parameters.h (base + a / Q))⁻¹ ^ 2)
      (Icc 0 ((O.H - (base + a / Q)) /
        (F.parameters.h (base + a / Q)) ^ 2)) V)
    (hfbased : ∀ hs y, y ∈ V → HEq (f.forward 0 hs y) y)
    (x : C.carrier) (hx : x ∈ U)
    (hyV : e.forward a ⟨le_rfl, ha.le⟩ x ∈ V)
    (hycap : e.forward a ⟨le_rfl, ha.le⟩ x ∈
      ((F.event (base + a / Q) hT).caps i).carrier) :
    let birth := base + a / Q
    let h := F.parameters.h birth
    let d := (O.H - birth) / h ^ 2
    (∀ s (hs : s ∈ Icc a 0), ∀ y ∈ U,
      (F.connection (base + s / Q)).scalarCurvature (e.forward s hs y) ≤ K * Q) ∧
      (e.forward a ⟨le_rfl, ha.le⟩ '' U ∩
        ((F.event birth hT).caps i).carrier).Nonempty ∧
      0 < d ∧ d < theta ∧
      ∃ comparison : SourceSearchCapBirthComparison F O birth hT i A eta,
        comparison.I = Ico 0 d := by
  obtain ⟨hd, hdt, hcomparison⟩ :=
    source_search_cap_birth_comparison_of_positive_age O e ha hbirthH hT i hA
      hpersist hmargin f hfbased x hyV hycap
  exact ⟨hscalar, ⟨_, ⟨x, hx, rfl⟩, hycap⟩, hd, hdt, hcomparison⟩

private theorem zero_contact_of_based
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



theorem terminal_cap_branch_zero_birth
    (S : RepairedControlledSchedulesData.{u}) {Asearch : ℝ} (hAsearch : 0 < Asearch) :
    ∃ Q0 R : ℝ, 0 < Q0 ∧
      S.standard_initial.cylindrical_end.radius + 5 < R ∧
      ∀ A : ℝ, R ≤ A → ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 1000 →
        ∃ delta : ℝ, 0 < delta ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          F.standard_initial = S.standard_initial → F.local_constants = S.constants →
          F.parameters.epsilon = S.setup.epsilon → F.parameters.C = S.setup.C →
          HEq O.standard_flow S.cap_persistence.standard_cap.flow →
        ∀ (W : M33RegularHistoryWindow F) (H : M33RegularHistoryData W)
          {base Q r : ℝ} (ht : base ∈ H.generalized.interval), 0 < base → 0 < Q →
          SurgeryFlowPinched F → SurgeryCanonicalOn F (Ico 0 base) r → r⁻¹ ^ 2 ≤ Q →
        ∀ x : (H.generalized.slice base).carrier,
          H.generalized.scalar ⟨base, x⟩ = Q → Q0 ≤ Q →
          F.parameters.delta base ≤ delta →
        ∀ e : SurgeryFlowCylinder F (F.slice base) base Q (Icc 0 0)
            ((F.metric base).ball (H.history.forward base ht x) (Asearch / Real.sqrt Q)),
          (∀ hs y, y ∈ (F.metric base).ball (H.history.forward base ht x)
              (Asearch / Real.sqrt Q) → HEq (e.forward 0 hs y) y) →
        ∀ K : ℝ,
          (∀ s (hs : s ∈ Icc 0 0), ∀ y ∈ (F.metric base).ball
              (H.history.forward base ht x) (Asearch / Real.sqrt Q),
            (F.connection (base + s / Q)).scalarCurvature (e.forward s hs y) ≤ K * Q) →
          (∃ hT : base + 0 / Q ∈ F.surgery_times,
            ∀ [Nonempty (F.slice (base + 0 / Q)).carrier],
              ∃ i : Fin (F.event (base + 0 / Q) hT).cap_count,
                (e.forward 0 ⟨le_rfl, le_rfl⟩ ''
                  ((F.metric base).ball (H.history.forward base ht x)
                    (Asearch / Real.sqrt Q)) ∩
                    ((F.event (base + 0 / Q) hT).caps i).carrier).Nonempty) →
          (∀ s (hs : s ∈ Icc 0 0), ∀ y ∈ (F.metric base).ball
              (H.history.forward base ht x) (Asearch / Real.sqrt Q),
            (F.connection (base + s / Q)).scalarCurvature (e.forward s hs y) ≤ K * Q) ∧
          ∃ hT : base ∈ F.surgery_times, ∀ [Nonempty (F.slice base).carrier],
            ∃ j : Fin (F.event base hT).cap_count,
              ∃ comparison : SourceSearchCapBirthComparison F O base hT j A eta,
                comparison.I = Icc 0 0 ∧
                ((F.metric base).ball (H.history.forward base ht x)
                    (Asearch / Real.sqrt Q) ⊆
                  (F.metric base).ball ((F.event base hT).caps j).tip
                    (R * F.parameters.h base)) ∧
                ∃ z ∈ F.standard_initial.metric.ball 0 A,
                  comparison.initial.chart z = H.history.forward base ht x ∧
                  F.standard_initial.metric.edist 0 z ≤ ENNReal.ofReal (2 * R) := by
  obtain ⟨Q0, R, hQ0, hR, factory⟩ :=
    exists_zero_age_search_cap_birth_comparison_cutoff S hAsearch
  refine ⟨Q0, R, hQ0, hR, ?_⟩
  intro A hRA eta heta hetaSmall
  obtain ⟨delta, hdelta, birth⟩ := factory A hRA eta heta hetaSmall
  refine ⟨delta, hdelta, ?_⟩
  intro F O hInitial hConstants hepsilon hC hmodel W H base Q r ht hbase hQ
    hpinch hpast hthreshold x hscale hlarge hsmall e hbased K hscalar hcontact
  obtain ⟨hT, hcontact⟩ := zero_contact_of_based e hbased hcontact
  refine ⟨hscalar, hT, ?_⟩
  intro hn
  obtain ⟨i, y, hy, hycap⟩ := hcontact
  exact birth F O hInitial hConstants hepsilon hC hmodel W H ht hbase hQ
    hpinch hpast hthreshold x hscale hlarge hT hsmall i y hy hycap

end PoincareConjecture.M47

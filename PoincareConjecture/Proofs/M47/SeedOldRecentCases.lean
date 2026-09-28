import PoincareConjecture.Proofs.M47.SeedOldHistoryVolume
import PoincareConjecture.Proofs.M47.SeedComponentBirth
import PoincareConjecture.Proofs.M47.SeedPositiveOnset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_old_volume_or_recent_ancestry
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    {g0 : ℝ} (hg0 : 0 < g0) :
    ∃ k : ℝ, 0 < k ∧ ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
      SurgeryPrefixControls p F O → SurgeryFlowPinched F →
      SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) →
      ∀ (T : ℝ), 0 < T → T ∈ F.time_domain → surgeryEpochStart p.i ≤ T →
        T ≤ O.H → T ≤ surgeryEpochStart (p.i + 1) →
        ∀ (x : (F.slice T).carrier), SurgeryPositiveComponentAt F T x →
          ∀ (r : ℝ), 0 < r → r ≤ p.setup.epsilon →
            ∀ test : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
              ((F.metric T).ball x r),
              (∀ hs y, y ∈ (F.metric T).ball x r → HEq (test.forward 0 hs y) y) →
              (∀ s (hs : s ∈ Icc (-r ^ 2) 0), ∀ y ∈ (F.metric T).ball x r,
                (F.connection (T + s / 1)).curvatureTensorNorm (test.forward s hs y) ≤
                  r⁻¹ ^ 2) →
              ENNReal.ofReal (k * r ^ 3) ≤
                  calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) ∨
                ∃ U : TopologicalSpace.Opens (F.slice T).carrier,
                  (U : Set (F.slice T).carrier) = connectedComponent x ∧
                  IsCompact (U : Set (F.slice T).carrier) ∧
                  IsConnected (U : Set (F.slice T).carrier) ∧
                  ∃ (b : ℝ) (hb : b ∈ Icc (-T) 0),
                    ∃ e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U,
                      (∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y) ∧
                      (T + b / 1 = 0 ∨ ∃ hbirth : T + b / 1 ∈ F.surgery_times,
                        ∀ [Nonempty (F.slice (T + b / 1)).carrier],
                          ∃ i : Fin (F.event (T + b / 1) hbirth).cap_count,
                            (e.forward b ⟨le_rfl, hb.2⟩ ''
                              (U : Set (F.slice T).carrier) ∩
                                ((F.event (T + b / 1) hbirth).caps i).carrier).Nonempty) ∧
                      ∃ (a : ℝ) (ha : a ∈ Icc b 0),
                        surgeryEpochStart p.i - g0 < T + a / 1 ∧
                        (a = b ∨ ∀ y : U,
                          ¬ SurgeryPositiveComponentAt F (T + a / 1)
                            (e.forward a ha y.val)) := by
  obtain ⟨k, hk, volume⟩ := exists_old_history_volume_constant P S p compatible hg0
  refine ⟨k, hk, ?_⟩
  intro F O old hpinch hpolicy T hT hTF hTi hTH hTmax x hpositive r hr hrEps
    test testBased testCurv
  obtain ⟨U, hU, hcompact, hconnected, hx, b, hb, e, hbased, hbirth⟩ :=
    exists_seed_component_birth F hTF x
  rcases lt_or_eq_of_le hb.2 with hbneg | hbzero
  · obtain ⟨a, ha, G, d, agree, based, readout, nonnegative, _before, onset⟩ :=
      exists_seed_positive_onset P hbneg U hcompact hconnected ⟨x, hx⟩ e hbased hpositive
    by_cases hOld : T + a ≤ surgeryEpochStart p.i - g0
    · apply Or.inl
      have hage : g0 ≤ -a := by linarith only [hOld, hTi]
      exact volume F O old hpinch hpolicy T a hTH hTmax hage hOld U hcompact hconnected
        d based G (fun s hs y => (readout s hs y).1)
        (fun s hs y => (readout s hs y).2.1) (fun s hs y => (readout s hs y).2.2)
        nonnegative (seed_onset_birth_alternative U hcompact hconnected e d hb.2
          agree onset hbirth) ⟨x, hx⟩ r hr hrEps test testBased testCurv
    · have ha' : a ∈ Icc b 0 := ⟨ha.1, ha.2.le⟩
      refine Or.inr ⟨U, hU, hcompact, hconnected, b, hb, e, hbased, hbirth,
        a, ha', ?_, ?_⟩
      · simpa only [div_one] using lt_of_not_ge hOld
      · rcases onset with heq | hnot
        · exact Or.inl heq
        · apply Or.inr
          intro y
          have h := hnot ⟨le_rfl, ha.2.le⟩ y
          rw [agree a ⟨le_rfl, ha.2.le⟩ ha' y.val] at h
          exact h
  · subst b
    refine Or.inr ⟨U, hU, hcompact, hconnected, 0, hb, e, hbased, hbirth,
      0, ⟨le_rfl, le_rfl⟩, ?_, Or.inl rfl⟩
    simp only [zero_div, add_zero]
    linarith only [hTi, hg0]

end PoincareConjecture.Proofs.M47

import PoincareConjecture.Proofs.M47.InductionCounterexamples
import PoincareConjecture.Proofs.M47.FirstFailureActual
import PoincareConjecture.Proofs.M47.SeedBufferedHorizonVolume

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_seed_buffered_counterexample_sequence
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (hno : ¬ Nonempty (SurgeryCanonicalExtension p (Classical.choice (N.induction p hp)))) :
    ∃ k : ℝ, 0 < k ∧ ∀ c : ℕ → ℝ, (∀ n, 0 < c n) →
      ∃ (r delta : ℕ → ℝ) (F : ℕ → SurgeryFlowData.{u})
        (O : ∀ n, SurgeryObservation (F n)) (t : ℕ → ℝ)
        (x : ∀ n, ((F n).slice (t n)).carrier),
        (∀ n, r n = p.r (Fin.last p.i) / ((n : ℝ) + 1)) ∧
        Tendsto r atTop (𝓝 0) ∧ Tendsto delta atTop (𝓝 0) ∧
        Tendsto (fun n => ((F n).connection (t n)).scalarCurvature (x n)) atTop atTop ∧
        ∀ n, 0 < r n ∧ r n ≤ p.r (Fin.last p.i) ∧
          0 < delta n ∧ delta n ≤ c n ∧
          delta n ≤ (Classical.choice (N.induction p hp)).cutoff (r n) ∧
          SurgeryObservationIsNextEpoch p (O n) ∧ SurgeryPrefixControls p (F n) (O n) ∧
          SurgeryFlowAdmissible (F n) ∧ SurgeryFlowPinched (F n) ∧
          SurgeryFlowTerminalPolicyOn (F n) (surgeryObservationInterval (O n)) ∧
          SurgeryPostPrefixScales p (F n) (O n) (r n) (delta n) ∧
          (∀ s ∈ surgeryObservationInterval (O n) ∩
            Ico (surgeryEpochStart (p.i - 1)) (O n).H, (F n).parameters.delta s ≤ delta n) ∧
          t n ∈ Ico (surgeryEpochStart p.i) (O n).H ∧
          t n = sInf (canonicalFailureTimes (F n) (O n) (r n)) ∧
          SurgeryCanonicalOn (F n) (Ico 0 (t n)) (r n) ∧
          (r n)⁻¹ ^ 2 ≤ ((F n).connection (t n)).scalarCurvature (x n) ∧
          ¬ SurgeryCanonicalControl (F n) (t n) (x n)
            (F n).parameters.epsilon (F n).parameters.C ∧
          SurgeryVolumeControlOn (F n) (Icc (surgeryEpochStart p.i - 1 / 128) (t n)) k
            (fun _ _ => True) := by
  classical
  obtain ⟨k, hk, volume⟩ := exists_seed_buffered_firstFailure_volume_constant P S N p hp
  refine ⟨k, hk, ?_⟩
  intro c hc
  let r : ℕ → ℝ := fun n => p.r (Fin.last p.i) / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n ∧ r n ≤ p.r (Fin.last p.i) :=
    canonicalInduction_radius_bounds (p.r_pos _) n
  have one (n : ℕ) : ∃ (delta : ℝ) (F : SurgeryFlowData.{u})
      (O : SurgeryObservation F) (t : ℝ) (x : (F.slice t).carrier),
      0 < delta ∧ delta ≤ c n ∧ delta ≤ 1 / ((n : ℝ) + 1) ∧
      delta ≤ (Classical.choice (N.induction p hp)).cutoff (r n) ∧
      SurgeryObservationIsNextEpoch p O ∧ SurgeryPrefixControls p F O ∧
      SurgeryFlowAdmissible F ∧ SurgeryFlowPinched F ∧
      SurgeryFlowTerminalPolicyOn F (surgeryObservationInterval O) ∧
      SurgeryPostPrefixScales p F O (r n) delta ∧
      (∀ s ∈ surgeryObservationInterval O ∩
        Ico (surgeryEpochStart (p.i - 1)) O.H, F.parameters.delta s ≤ delta) ∧
      t ∈ Ico (surgeryEpochStart p.i) O.H ∧ t = sInf (canonicalFailureTimes F O (r n)) ∧
      SurgeryCanonicalOn F (Ico 0 t) (r n) ∧
      (r n)⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x ∧
      ¬ SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C ∧
      SurgeryVolumeControlOn F (Icc (surgeryEpochStart p.i - 1 / 128) t) k (fun _ _ => True) := by
    obtain ⟨deltaA, hdeltaA, _hLastA, attain⟩ :=
      firstFailure_attained_infimum P S p hp (r n) (hr n).1 (hr n).2
    obtain ⟨deltaV, hdeltaV, _hLastV, hQ, applyVolume⟩ := volume (r n) (hr n).1 (hr n).2
    let delta := min deltaA (min deltaV (min (c n) (1 / ((n : ℝ) + 1))))
    have hdelta : 0 < delta :=
      lt_min hdeltaA (lt_min hdeltaV (lt_min (hc n) (by positivity)))
    have hA : delta ≤ deltaA := min_le_left _ _
    have hV : delta ≤ deltaV := (min_le_right _ _).trans (min_le_left _ _)
    have hrest : delta ≤ min (c n) (1 / ((n : ℝ) + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hQ' := hV.trans hQ
    obtain ⟨F, O, hnext, old, admissible, pinched, policy, scales, overlap, hbad⟩ :=
      canonicalInduction_counterexample p (Classical.choice (N.induction p hp))
        hno (hr n).1 (hr n).2 hdelta hQ'
    obtain ⟨t, ht, hinf, past, x, hscalar, hfailure⟩ := attain F O hnext old admissible
      pinched policy (scales.mono_delta hA) (fun s hs => (overlap s hs).trans hA) hbad
    have hv := applyVolume F O hnext old admissible pinched policy
      (scales.mono_delta hV) (fun s hs => (overlap s hs).trans hV) t ht past
    exact ⟨delta, F, O, t, x, hdelta, hrest.trans (min_le_left _ _),
      hrest.trans (min_le_right _ _), hQ', hnext, old, admissible, pinched, policy,
      scales, overlap, ht, hinf, past, hscalar, hfailure, hv⟩
  choose delta F O t x hd hc' hn hcut hnext old admissible pinched policy scales
    overlap ht hinf past high bad vol using one
  have hdelta : Tendsto delta atTop (𝓝 0) :=
    squeeze_zero (fun n => (hd n).le) hn tendsto_one_div_add_atTop_nhds_zero_nat
  have hscalar := canonicalInduction_scalar_diverges (p.r_pos _) high
  refine ⟨r, delta, F, O, t, x, fun _ => rfl,
    canonicalInduction_radius_tendsto _, hdelta, hscalar, ?_⟩
  intro n
  exact ⟨(hr n).1, (hr n).2, hd n, hc' n, hcut n, hnext n, old n, admissible n,
    pinched n, policy n, scales n, overlap n, ht n, hinf n, past n, high n, bad n, vol n⟩

end PoincareConjecture.Proofs.M47

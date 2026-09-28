import PoincareConjecture.Proofs.M47.SeedNearAncestor
import PoincareConjecture.Proofs.M47.SeedVolumeAlternatives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open M46

theorem exists_volume_or_small_component_positive_ancestry
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k : ℝ, 0 < k ∧ ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
      ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
        cutoff ≤ (Classical.choice (N.induction p hp)).cutoff rNext ∧
        ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
          ObservedInputs p rNext cutoff F O →
          ∀ T : ℝ, T ∈ surgeryObservationInterval O → surgeryEpochStart p.i ≤ T →
            ∀ x : (F.slice T).carrier, ∀ r : ℝ, 0 < r → r ≤ p.setup.epsilon →
              ∀ test : SurgeryFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
                ((F.metric T).ball x r),
                (∀ hs y, y ∈ (F.metric T).ball x r → HEq (test.forward 0 hs y) y) →
                (∀ s hs y, y ∈ (F.metric T).ball x r →
                  (F.connection (T + s / 1)).curvatureTensorNorm
                    (test.forward s hs y) ≤ r⁻¹ ^ 2) →
                ENNReal.ofReal (k * r ^ 3) ≤
                  calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) ∨
                (r < rNext ∧ rNext⁻¹ ^ 2 < (F.connection T).scalarCurvature x ∧
                  ((∃ C : SingularCComponent (F.metric T) (F.connection T) F.parameters.C,
                    x ∈ C.carrier) ∨
                    ∃ C : SingularRoundComponent (F.metric T) F.parameters.epsilon,
                      x ∈ C.carrier) ∧
                  ∀ (s : ℝ) (hs : s ∈ Icc (-r ^ 2) 0), -r ^ 2 / 8 ≤ s →
                    SurgeryPositiveComponentAt F (T + s / 1) (test.forward s hs x)) := by
  classical
  let Q := Classical.choice (N.induction p hp)
  obtain ⟨k0, hk0, volumeOrComponent⟩ := exists_positive_volume_or_small_component P S p hp
  let k := min k0 (Q.kappaNew / 512)
  have hk : 0 < k := lt_min hk0 (div_pos Q.kappa_pos (by norm_num))
  have hkQ : k ≤ Q.kappaNew := (min_le_right _ _).trans (by linarith only [Q.kappa_pos])
  refine ⟨k, hk, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨delta0, hdelta0, hlast, cases0⟩ := volumeOrComponent rNext hrNext hrLast
  let cutoff := min delta0 (Q.cutoff rNext)
  have hsmall0 : cutoff ≤ delta0 := min_le_left _ _
  have hsmallQ : cutoff ≤ Q.cutoff rNext := min_le_right _ _
  refine ⟨cutoff, lt_min hdelta0 (Q.cutoff_bounds rNext hrNext hrLast).1,
    hsmall0.trans hlast, hsmallQ, ?_⟩
  intro F O inputs T hTO hTi x r hr hrEpsilon test hbased hcurv
  let inputsQ := inputs.cutoff_mono hsmallQ
  have hnoncollapse := Q.noncollapsed rNext hrNext hrLast F O inputsQ.next_epoch
    inputsQ.old inputsQ.admissible inputsQ.pinched inputsQ.terminal_policy
    inputsQ.scales inputsQ.canonical inputsQ.overlap
  have hre : r ≤ F.parameters.epsilon := by rwa [inputs.old.epsilon_eq]
  have hmono (k' : ℝ) (hle : k ≤ k')
      (hv : ENNReal.ofReal (k' * r ^ 3) ≤
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r)) :
      ENNReal.ofReal (k * r ^ 3) ≤
        calibratedMetricVolume (F.metric T) ((F.metric T).ball x r) :=
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (pow_nonneg hr.le 3))).trans hv
  by_cases hvolume : ENNReal.ofReal (k * r ^ 3) ≤
      calibratedMetricVolume (F.metric T) ((F.metric T).ball x r)
  · exact Or.inl hvolume
  have hpositive : SurgeryPositiveComponentAt F T x := by
    by_contra hnot
    exact hvolume (hmono Q.kappaNew hkQ
      (hnoncollapse T hTO (O.interval_subset hTO) x hnot r hr hre test hbased hcurv))
  rcases cases0 F O (inputs.cutoff_mono hsmall0) T hTO hTi x hpositive r hr hrEpsilon
      test hbased hcurv with hvol0 | hcomponent
  · exact (hvolume (hmono k0 (min_le_left _ _) hvol0)).elim
  · refine Or.inr ⟨hcomponent.1, hcomponent.2.1, hcomponent.2.2, ?_⟩
    intro s hs hnear
    by_contra hnot
    have hsF : T + s / 1 ∈ F.time_domain := test.time_subset (mem_image_of_mem _ hs)
    have hsO : T + s / 1 ∈ surgeryObservationInterval O := by
      refine ⟨F.time_domain_nonnegative hsF, ?_⟩
      simp only [div_one]
      linarith only [hs.2, hTO.2]
    exact hvolume (hmono (Q.kappaNew / 512) (min_le_right _ _)
      (seed_volume_of_near_nonpositive_ancestor P hnoncollapse x hr hre test
        hbased hcurv hs hnear hsO hnot))

end PoincareConjecture.Proofs.M47

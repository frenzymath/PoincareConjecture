import PoincareConjecture.Proofs.M47.SeedObservedSearchVolume
import PoincareConjecture.Proofs.M47.SeedObservedSearchScales

set_option autoImplicit false

open Set
open scoped ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open M46

theorem exists_seed_observed_scaled_birth_density
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p) :
    ∃ k sigma lambda : ℝ, 0 < k ∧ 0 < sigma ∧ 0 < lambda ∧ lambda ≤ 1 / 8 ∧
      ∀ rNext : ℝ, 0 < rNext → rNext ≤ p.r (Fin.last p.i) →
        ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ p.Delta (Fin.last p.i) ∧
          ∀ H : ℝ, 0 < H → rNext⁻¹ ^ 2 ≤ H →
            let d := sigma / H
            let r := lambda / Real.sqrt H
            0 < d ∧ 0 < r ∧ r ≤ rNext ∧ d ≤ rNext ^ 2 / 624 ∧
            ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
              ObservedInputs p rNext cutoff F O →
              ∀ origin : ℝ,
                Icc (origin - d) origin ⊆
                  surgeryObservationInterval O ∩ Ici (surgeryEpochStart (p.i - 1)) →
              ∀ q : (F.slice origin).carrier,
                (∀ y ∈ (F.metric origin).ball q r,
                  (F.connection origin).scalarCurvature y ≤ 2 * H) →
                (¬ SurgeryPositiveComponentAt F origin q ∨
                  ∃ hT : origin ∈ F.surgery_times,
                    ∀ [Nonempty (F.slice origin).carrier],
                      ∃ i : Fin (F.event origin hT).cap_count,
                        (connectedComponent q ∩
                          ((F.event origin hT).caps i).carrier).Nonempty) →
                ENNReal.ofReal (k * (r / 2) ^ 3) ≤
                  calibratedMetricVolume (F.metric origin)
                    ((F.metric origin).ball q (r / 2)) := by
  obtain ⟨k, hk, hvolume⟩ := exists_seed_observed_search_volume P S N p hp
  obtain ⟨B, sigma, lambda, hB, _, hsigma, hlambda, hsmall, hscales⟩ :=
    exists_seed_observed_search_scales S p
  refine ⟨k, sigma, lambda, hk, hsigma, hlambda, hsmall, ?_⟩
  intro rNext hrNext hrLast
  obtain ⟨cutoff, hcutoff, hcutoffLast, hsearch⟩ := hvolume rNext hrNext hrLast
  refine ⟨cutoff, hcutoff, hcutoffLast, ?_⟩
  intro H hH hlevel
  obtain ⟨hd, hr, hroot, hscalarTime, hmetricTime, hrEpsilon, hbudget, hrd,
      htest, hrNext, hdNext⟩ := hscales rNext hrNext hrLast H hH hlevel
  refine ⟨hd, hr, hrNext, hdNext, ?_⟩
  exact hsearch H B (sigma / H) (lambda / Real.sqrt H) hH hB hd hr hlevel
    hroot hscalarTime hmetricTime hrEpsilon hbudget hrd htest

end PoincareConjecture.Proofs.M47

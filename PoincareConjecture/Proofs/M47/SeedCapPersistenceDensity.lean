import PoincareConjecture.Proofs.M47.SeedCapBirthDensity
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_TrackedBall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_seed_cap_persistence_density (g0 : StandardInitialMetric)
    {Rtip Rmax : ℝ} (htip : 0 < Rtip) (hmax : 0 < Rmax) :
    ∃ k : ℝ, 0 < k ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (O : SurgeryObservation F) (t : ℝ) (hT : t ∈ F.surgery_times)
        (_hn : Nonempty (F.slice t).carrier) (i : Fin (F.event t hT).cap_count)
        (A eta theta : ℝ),
        2 * Rtip + Rmax ≤ A → 0 < eta → eta ≤ 1 / 2 →
        0 < theta → t < O.H →
        SurgeryCapPersistenceAlternative F O t hT i A eta theta →
          ∀ z ∈ (F.metric t).ball ((F.event t hT).caps i).tip (Rtip * F.parameters.h t),
            ∀ r : ℝ, 0 < r → r ≤ Rmax * F.parameters.h t →
              ENNReal.ofReal (k * r ^ 3) ≤
                calibratedMetricVolume (F.metric t) ((F.metric t).ball z r) := by
  obtain ⟨k, hk, hbirth⟩ := exists_seed_cap_birth_density g0 htip hmax
  refine ⟨k, hk, ?_⟩
  intro F hinitial O t hT hn i A eta theta hA heta hetaHalf htheta htH hpersist
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  rcases hpersist with ⟨e, initial, comparison, hidentity⟩ |
    ⟨tPlus, htPlus, _, _, e, initial, comparison, hidentity, _⟩
  · have hzero : (0 : ℝ) ∈ Ico 0 (surgeryCapDuration t O.H (F.parameters.h t) theta) :=
      ⟨le_rfl, surgeryCapDuration_pos htH hh htheta⟩
    exact hbirth F hinitial O.standard_flow t hT hn i A eta hA heta hetaHalf _ e
      initial comparison hzero (hidentity hzero)
  · have hzero : (0 : ℝ) ∈ Ico 0 ((tPlus - t) / (F.parameters.h t) ^ 2) :=
      ⟨le_rfl, div_pos (sub_pos.mpr htPlus) (sq_pos_of_pos hh)⟩
    exact hbirth F hinitial O.standard_flow t hT hn i A eta hA heta hetaHalf _ e
      initial comparison hzero (hidentity hzero)

end PoincareConjecture.Proofs.M47

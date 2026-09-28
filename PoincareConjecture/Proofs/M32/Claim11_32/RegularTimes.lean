import PoincareConjecture.Proofs.M31.RegularCanonical

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem terminalTime_pos (H : SingularTimeAssumptions F T M) : 0 < T := by
  obtain ⟨s, hs⟩ := F.interval_nontrivial.nonempty
  exact (H.interval_preterminal hs).1.trans_lt (H.interval_preterminal hs).2

theorem existsRegularTimeAbove (H : SingularTimeAssumptions F T M)
    {s a : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T) (has : a < s) :
    ∃ r, r ∈ F.interval ∧ a < r ∧ r ≤ s ∧ (r = 0 ∨ r ∉ H.singularTimes) := by
  by_cases hs : s = 0
  · exact ⟨0, H.interval_exhausts_preterminal ⟨le_rfl, terminalTime_pos H⟩,
      by simpa only [hs] using has, hs0, Or.inl rfl⟩
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
  obtain ⟨b, hb, hbs⟩ := exists_between (max_lt has hspos)
  have hbF : b ∈ F.interval := H.interval_exhausts_preterminal
    ⟨(le_max_right a 0).trans hb.le, hbs.trans_le hsT⟩
  obtain ⟨r, hr, har, hrb, hregular⟩ :=
    H.regularTimes_left_dense hbF a ((le_max_left a 0).trans_lt hb)
  exact ⟨r, hr, har, hrb.trans hbs.le, hregular⟩

theorem terminalAccuracy_pos (H : SingularTimeAssumptions F T M) :
    0 < terminalAccuracyFactor * H.epsilon :=
  mul_pos terminalAccuracyFactor_pos H.epsilon_pos

theorem terminalAccuracy_lt_half (H : SingularTimeAssumptions F T M) :
    terminalAccuracyFactor * H.epsilon < 1 / 2 :=
  H.terminal_epsilon_le_threshold.trans_lt (by norm_num)

end PoincareConjecture.M32

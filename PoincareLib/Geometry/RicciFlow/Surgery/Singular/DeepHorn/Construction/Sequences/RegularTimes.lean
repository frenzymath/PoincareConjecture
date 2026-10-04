import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.Sequences.RegularCanonical

/-!
# Regular times for terminal blowup controls

Morgan--Tian Claim 11.32, printed pp. 287-288, uses canonical controls at
earlier regular times, including for terminal basepoints. We extend M31's
`SingularTimeAssumptions.regularTimes_left_dense` to the terminal endpoint.
The donor declarations are `SingularTimeAssumptions.terminal_time_pos` and
`SingularTimeAssumptions.exists_regular_time_above` in Horizon
`Surgery/Singular/DeepHorn/Extension/Canonical.lean`; that module is not
imported. Terminal accuracy uses the corrected factor from the frozen
contract, without its numeric value.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M32

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

/-- The nontrivial preterminal interval has a positive terminal time.
Morgan--Tian Assumptions 11.18 and Claim 11.32, printed pp. 279, 287-288. -/
theorem terminalTime_pos (H : SingularTimeAssumptions F T M) : 0 < T := by
  obtain ⟨s, hs⟩ := F.interval_nontrivial.nonempty
  exact (H.interval_preterminal hs).1.trans_lt (H.interval_preterminal hs).2

/-- The earlier regular times also approach the terminal endpoint in the
precise non-strict form used in Claim 11.32, printed pp. 287-288. -/
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

/-- The terminal neck accuracy in Claim 11.32, printed pp. 287-288, is
positive with the corrected universal factor. -/
theorem terminalAccuracy_pos (H : SingularTimeAssumptions F T M) :
    0 < terminalAccuracyFactor * H.epsilon :=
  mul_pos terminalAccuracyFactor_pos H.epsilon_pos

/-- The corrected terminal accuracy satisfies the smallness needed by the
neck noncollapse step of Claim 11.32, printed p. 288. -/
theorem terminalAccuracy_lt_half (H : SingularTimeAssumptions F T M) :
    terminalAccuracyFactor * H.epsilon < 1 / 2 :=
  H.terminal_epsilon_le_threshold.trans_lt (by norm_num)

end PoincareMT.M32

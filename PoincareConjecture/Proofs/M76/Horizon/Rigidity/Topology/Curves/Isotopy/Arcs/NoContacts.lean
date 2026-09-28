import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.TerminalLift
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open Set Geometry PLAnnularStrip Topology unitInterval

namespace PoincareConjecture.M76.Dehn

theorem mem_open_period_strip_of_no_contacts
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hf0 : f 0 = 0)
    {period c : ℝ} (hc : 0 < c) (hcp : c < period)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k : ℤ, f t ≠ c + period * (k : ℝ)) :
    ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ Ioo (c - period) c := by
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 :=
    fun x hx => ⟨hx.1, hx.2.trans ht.2⟩
  constructor
  · by_contra hn
    have hft : f t ≤ c - period := le_of_not_gt hn
    obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc' ht.1 (hf.mono hsub)
      (show c - period ∈ Icc (f t) (f 0) from ⟨hft, by rw [hf0]; linarith⟩)
    apply havoid u (hsub hu) (-1)
    simpa only [Int.cast_neg, Int.cast_one, mul_neg, mul_one, ← sub_eq_add_neg] using hfu
  · by_contra hn
    have hft : c ≤ f t := le_of_not_gt hn
    obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc ht.1 (hf.mono hsub)
      (show c ∈ Icc (f 0) (f t) from ⟨by rw [hf0]; exact hc.le, hft⟩)
    apply havoid u (hsub hu) 0
    simpa only [Int.cast_zero, mul_zero, add_zero] using hfu

theorem exists_short_interval_of_no_periodic_contacts
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hf0 : f 0 = 0)
    {period c : ℝ} (hc : 0 < c) (hcp : c < period)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k : ℤ, f t ≠ c + period * (k : ℝ)) :
    ∃ a b : ℝ, c - period < a ∧ a ≤ 0 ∧ 0 ≤ b ∧ b < c ∧ b - a < period ∧
      ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ Icc a b := by
  have hne : (Icc (0 : ℝ) 1).Nonempty := ⟨0, le_rfl, zero_le_one⟩
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf
  have hbounds := mem_open_period_strip_of_no_contacts hf hf0 hc hcp havoid
  have hmin0 : f s ≤ 0 := by
    simpa only [hf0] using (show f s ≤ f 0 from hmin ⟨le_rfl, zero_le_one⟩)
  have hmax0 : 0 ≤ f t := by
    simpa only [hf0] using (show f 0 ≤ f t from hmax ⟨le_rfl, zero_le_one⟩)
  refine ⟨f s, f t, (hbounds s hs).1, hmin0, hmax0, (hbounds t ht).2, ?_, ?_⟩
  · linarith [(hbounds s hs).1, (hbounds t ht).2]
  · intro u hu
    exact ⟨hmin hu, hmax hu⟩

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem hasJointPLRadialStraightening_of_no_periodic_contacts
    (gamma : C(I, Ann)) {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    (hr0 : r 0 = (0, -1)) (hr1 : r 1 = (0, 1))
    (hproj : ∀ t : I, annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) = gamma t)
    (hheight : ∀ t : I, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1)
    {c : ℝ} (hc : 0 < c) (hc32 : c < 32)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k : ℤ, (r t).1 ≠ c + 32 * (k : ℝ)) :
    HasJointPLRadialStraightening gamma := by
  have hangle : ContinuousOn (fun t => (r t).1) (Icc (0 : ℝ) 1) :=
    continuous_fst.comp_continuousOn hr.continuousOn
  have hzero : (r 0).1 = 0 := congrArg Prod.fst hr0
  obtain ⟨a, b, _, _, _, _, hwidth, hbound⟩ :=
    exists_short_interval_of_no_periodic_contacts hangle hzero hc hc32 havoid
  exact hasJointPLRadialStraightening_of_terminal_lift gamma hr hi hr0 hr1 hproj
    hheight hproper hwidth (fun t => hbound t t.property)

end PoincareConjecture.M76.Dehn

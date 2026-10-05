import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Last scalar level on a compact interval

The intermediate-value selection used at the start of Morgan--Tian
section 10.3, printed p. 247. The same exact-level selection handles the
threshold margin in the dense-time bounded-distance argument.
-/

set_option autoImplicit false

open Set

/-- A continuous function crossing a level has a last point at that level,
and stays strictly above it afterwards. This is the real-variable
truncation in Morgan--Tian section 10.3, printed p. 247. -/
theorem exists_last_eq_of_continuousOn {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (ha : f a ≤ c) (hb : c < f b) :
    ∃ s ∈ Icc a b, f s = c ∧ ∀ t ∈ Ioc s b, c < f t := by
  let K : Set ℝ := Icc a b ∩ f ⁻¹' {c}
  have hclosed : IsClosed K := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  obtain ⟨s₀, hs₀, heq₀⟩ := intermediate_value_Icc hab hf ⟨ha, hb.le⟩
  have hnonempty : K.Nonempty := ⟨s₀, hs₀, heq₀⟩
  obtain ⟨s, hs, hgreatest⟩ := hcompact.exists_isGreatest hnonempty
  refine ⟨s, hs.1, hs.2, ?_⟩
  intro t ht
  by_contra h
  have hft : f t ≤ c := le_of_not_gt h
  have hsubset : Icc t b ⊆ Icc a b := Icc_subset_Icc (hs.1.1.trans ht.1.le) le_rfl
  obtain ⟨v, hv, heq⟩ := intermediate_value_Icc ht.2 (hf.mono hsubset) ⟨hft, hb.le⟩
  have hvs : v ≤ s := hgreatest ⟨hsubset hv, heq⟩
  exact (not_lt_of_ge hvs) (ht.1.trans_le hv.1)

import PoincareConjecture.Definitions.Ch11.BlowupLimits
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

open Set Filter
open scoped ENNReal Topology

universe u v

namespace PoincareConjecture.M30

theorem eventually_closed_time_interval_eq {T : ℝ}
    {L : BlowupLimitFlow.{u} (Icc (-T) 0)} (E : BlowupExhaustion L) :
    ∀ᶠ k : ℕ in atTop, Icc (-(E.time k)) 0 = Icc (-T) 0 := by
  filter_upwards [E.time_cofinal (Icc (-T) 0) isCompact_Icc Subset.rfl] with k hk
  exact Subset.antisymm (E.time_subset k) hk

theorem eventually_backward_time_domain_germs {T₀ : ℝ≥0∞}
    {L : BlowupLimitFlow.{u} (blowupBackwardInterval T₀)}
    (E : BlowupExhaustion L) {Y : Type v} [TopologicalSpace Y]
    (V : Set Y) (K : Set (ℝ × Y)) (hK : IsCompact K)
    (hKJ : K ⊆ blowupBackwardInterval T₀ ×ˢ V) :
    ∀ᶠ k : ℕ in atTop,
      K ⊆ Icc (-(E.time k)) 0 ×ˢ V ∧
      ∀ z ∈ K, (Icc (-(E.time k)) 0 ×ˢ V) =ᶠ[𝓝 z]
        (blowupBackwardInterval T₀ ×ˢ V) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact Eventually.of_forall fun _ => ⟨empty_subset _, fun _ hz => False.elim hz⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
  let O : Set ℝ := {t | ENNReal.ofReal (-t) < T₀}
  have hO : IsOpen O :=
    isOpen_Iio.preimage (ENNReal.continuous_ofReal.comp continuous_neg)
  have hz₀O : z₀.1 ∈ O := (hKJ hz₀).1.2
  obtain ⟨b, hb, hbO⟩ := Filter.Eventually.exists_lt (hO.mem_nhds hz₀O)
  have hbJ : b ∈ blowupBackwardInterval T₀ :=
    ⟨hb.le.trans (hKJ hz₀).1.1, hbO⟩
  filter_upwards [E.time_cofinal {b} isCompact_singleton
    (singleton_subset_iff.mpr hbJ)] with k hk
  have hkb : -(E.time k) ≤ b := (hk (mem_singleton b)).1
  have hlow (z : ℝ × Y) (hz : z ∈ K) : -(E.time k) < z.1 :=
    hkb.trans_lt (hb.trans_le (hmin hz))
  refine ⟨fun z hz => ⟨⟨(hlow z hz).le, (hKJ hz).1.1⟩, (hKJ hz).2⟩, ?_⟩
  intro z hz
  have hlo : ∀ᶠ w : ℝ × Y in 𝓝 z, -(E.time k) < w.1 :=
    continuousAt_fst.eventually (Ioi_mem_nhds (hlow z hz))
  have ho : ∀ᶠ w : ℝ × Y in 𝓝 z, w.1 ∈ O :=
    continuousAt_fst.eventually (hO.mem_nhds (hKJ hz).1.2)
  filter_upwards [hlo, ho] with w hw hwo
  apply propext
  change ((-(E.time k) ≤ w.1 ∧ w.1 ≤ 0) ∧ w.2 ∈ V) ↔
    ((w.1 ≤ 0 ∧ ENNReal.ofReal (-w.1) < T₀) ∧ w.2 ∈ V)
  have hwh : ENNReal.ofReal (-w.1) < T₀ := hwo
  simp only [hw.le, hwh, true_and, and_true]

end PoincareConjecture.M30

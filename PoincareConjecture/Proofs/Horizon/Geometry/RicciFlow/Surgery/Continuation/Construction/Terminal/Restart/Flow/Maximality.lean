import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Maximality


set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.TerminalRestart

theorem excluded_endpoint_eq_toReal {B : ℝ≥0∞} {a b : ℝ}
    (ha : a ∈ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B}) (hab : a < b)
    (hJ : Ico a b ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B})
    (hb : b ∉ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B}) : B ≠ ⊤ ∧ b = B.toReal := by
  have hb0 : 0 ≤ b := ha.1.trans hab.le
  have hbB : B ≤ ENNReal.ofReal b := le_of_not_gt (fun h => hb ⟨hb0, h⟩)
  have hfinite : B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbB
  have hlo : B.toReal ≤ b := ENNReal.toReal_le_of_le_ofReal hb0 hbB
  have haB : a < B.toReal := (ENNReal.ofReal_lt_iff_lt_toReal ha.1 hfinite).mp ha.2
  refine ⟨hfinite, le_antisymm ?_ hlo⟩
  by_contra h
  have hBb : B.toReal < b := lt_of_not_ge h
  let t := (B.toReal + b) / 2
  have ht : t ∈ Ico a b := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
  have hbound := (ENNReal.ofReal_lt_iff_lt_toReal (hJ ht).1 hfinite).mp (hJ ht).2
  dsimp [t] at hbound
  linarith

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  (C : GeneralizedSliceCarrier.{u}) {B : ℝ≥0∞}
  (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})

include I

theorem maximal_intervals (hB : ENNReal.ofReal T < B)
    (hblow : B ≠ ⊤ → ∀ L s : ℝ, s < B.toReal →
      ∃ t ∈ Ioo (max T s) B.toReal, ∃ x : C.carrier,
        L < (R.connection t).curvatureTensorNorm x)
    (a b : ℝ) (ha : a ∈ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B})
    (hstart : a = 0 ∨ a ∈ Splice.eventTimes F T) (hab : a < b)
    (hJ : Ico a b ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B})
    (hfree : Disjoint (Splice.eventTimes F T) (Ioo a b))
    (hend : b ∈ Splice.eventTimes F T ∨ b ∉ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B}) :
    ∀ L s : ℝ, s < b → ∃ t ∈ Ioo (max a s) b,
      ∃ x : (Splice.slice F T C R t).carrier,
        L < (Splice.connection F T C R t).curvatureTensorNorm x := by
  rcases hend with hevent | hout
  · exact Splice.maximal_intervals_before F T C R I a b ha.1 hstart hab hfree
      (mem_insert_iff.mp hevent).symm
  · obtain ⟨hfinite, rfl⟩ := excluded_endpoint_eq_toReal ha hab hJ hout
    have hTB : T < B.toReal := (ENNReal.ofReal_lt_iff_lt_toReal I.terminal_pos.le hfinite).mp hB
    have hTa : T ≤ a := by
      by_contra h
      exact disjoint_left.mp hfree (mem_insert T F.surgery_times) ⟨lt_of_not_ge h, hTB⟩
    have haT : a ≤ T := by
      rcases hstart with rfl | hevent
      · exact I.terminal_pos.le
      · rcases mem_insert_iff.mp hevent with rfl | hold
        · exact le_rfl
        · exact (I.time_domain_eq ▸ F.surgery_times_subset hold).2.le
    have heq : a = T := le_antisymm haT hTa
    subst a
    intro L s hs
    obtain ⟨t, ht, x, hx⟩ := hblow hfinite L s hs
    have htT : T ≤ t := ((le_max_left T s).trans_lt ht.1).le
    refine ⟨t, ht, Splice.identifyAfter F T C R t htT x, ?_⟩
    rw [Splice.curvature_after F T C R t htT]
    exact hx

end PoincareConjecture.Surgery.TerminalRestart

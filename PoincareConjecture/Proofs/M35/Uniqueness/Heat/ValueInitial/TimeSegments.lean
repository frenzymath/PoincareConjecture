import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.FormLift
import Mathlib.Topology.Piecewise
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

def joinTime {E : Type*} (f g : ℝ → E) (S t : ℝ) : E :=
  if t ≤ S then f t else g (t - S)

theorem measurePreserving_sub_time (S T : ℝ) :
    MeasurePreserving (fun t : ℝ => t - S)
      (volume.restrict (Ioc S (S + T))) (timeMeasure T) := by
  have hp : (fun t : ℝ => t + -S) ⁻¹' Ioc 0 T = Ioc S (S + T) := by
    ext t
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro ht <;> constructor <;> linarith only [ht.1, ht.2]
  simpa only [hp, sub_eq_add_neg] using
    (measurePreserving_add_right volume (-S)).restrict_preimage
      (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) T))

theorem memLp_sub_time {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {S T : ℝ} (hf : MemLp f 2 (timeMeasure T)) :
    MemLp (fun t => f (t - S)) 2 (volume.restrict (Ioc S (S + T))) :=
  hf.comp_measurePreserving (measurePreserving_sub_time S T)

theorem memLp_joinTime {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → E} {S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hf : MemLp f 2 (timeMeasure S)) (hg : MemLp g 2 (timeMeasure T)) :
    MemLp (joinTime f g S) 2 (timeMeasure (S + T)) := by
  classical
  have hl : (timeMeasure (S + T)).restrict (Iic S) = timeMeasure S := by
    change (volume.restrict (Ioc 0 (S + T))).restrict (Iic S) = volume.restrict (Ioc 0 S)
    rw [Measure.restrict_restrict measurableSet_Iic]
    congr 1
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor <;> intro ht
    · exact ⟨ht.2.1, ht.1⟩
    · exact ⟨ht.2, ht.1, by linarith only [ht.2, hT]⟩
  have hr : (timeMeasure (S + T)).restrict (Iic S)ᶜ =
      volume.restrict (Ioc S (S + T)) := by
    change (volume.restrict (Ioc 0 (S + T))).restrict (Iic S)ᶜ = _
    rw [Measure.restrict_restrict measurableSet_Iic.compl]
    congr 1
    ext t
    simp only [mem_inter_iff, mem_compl_iff, mem_Iic, not_le, mem_Ioc]
    constructor <;> intro ht
    · exact ⟨ht.1, ht.2.2⟩
    · exact ⟨ht.1, hS.trans_lt ht.1, ht.2⟩
  exact MemLp.piecewise measurableSet_Iic (hl.symm ▸ hf) (hr.symm ▸ memLp_sub_time hg)

theorem continuousOn_joinTime {E : Type*} [TopologicalSpace E]
    {f g : ℝ → E} {S T : ℝ}
    (hf : ContinuousOn f (Icc 0 S)) (hg : ContinuousOn g (Icc 0 T))
    (hjoin : f S = g 0) : ContinuousOn (joinTime f g S) (Icc 0 (S + T)) := by
  have hl : Icc 0 (S + T) ∩ closure {t : ℝ | t ≤ S} ⊆ Icc 0 S := by
    change Icc 0 (S + T) ∩ closure (Iic S) ⊆ Icc 0 S
    rw [isClosed_Iic.closure_eq]
    intro t ht
    exact ⟨ht.1.1, ht.2⟩
  have hr : MapsTo (fun t : ℝ => t - S)
      (Icc 0 (S + T) ∩ closure {t : ℝ | ¬t ≤ S}) (Icc 0 T) := by
    have he : {t : ℝ | ¬t ≤ S} = Ioi S := by ext t; simp
    rw [he, closure_Ioi]
    intro t ht
    change 0 ≤ t - S ∧ t - S ≤ T
    have hSt : S ≤ t := ht.2
    have htop : t ≤ S + T := ht.1.2
    constructor <;> linarith only [htop, hSt]
  apply ContinuousOn.if _ (hf.mono hl)
    (hg.comp (continuous_id.sub continuous_const).continuousOn hr)
  intro t ht
  have he : t = S := by
    have h : t ∈ frontier (Iic S) := ht.2
    simpa only [frontier_Iic, mem_singleton_iff] using h
  subst t
  change f S = g (S - S)
  simpa only [sub_self] using hjoin

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

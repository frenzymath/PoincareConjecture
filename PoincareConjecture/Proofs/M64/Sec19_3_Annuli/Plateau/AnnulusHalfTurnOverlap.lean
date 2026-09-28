import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnMeasure
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "D" => Set.ofPred (fun p : LoopPlane =>
  p 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ p 1 ∈ Icc (0 : ℝ) 1)
local notation "half" => curvePeriod / 2
local notation "v" => annulusPoint (curvePeriod / 2) 0
local notation "T" => m64AnnulusHalfTurn

theorem m64RadialStrip_subset_closure (a b : ℝ) :
    {p : LoopPlane | p 0 ∈ Ioo a b ∧ p 1 ∈ Icc (0 : ℝ) 1} ⊆
      closure {p : LoopPlane | p 0 ∈ Ioo a b ∧ p 1 ∈ Ioo (0 : ℝ) 1} := by
  intro p hp
  have hc : Continuous (annulusPoint (p 0)) := by unfold annulusPoint; fun_prop
  have hp1 : p 1 ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    exact hp.2
  have ht : MapsTo (annulusPoint (p 0)) (Ioo (0 : ℝ) 1)
      {q : LoopPlane | q 0 ∈ Ioo a b ∧ q 1 ∈ Ioo (0 : ℝ) 1} :=
    fun t ht => ⟨hp.1, ht⟩
  have h := hc.continuousWithinAt.mem_closure hp1 ht
  have heq : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  rwa [heq] at h

theorem m64AnnulusHalfTurn_ae_reverse {M : Type*} {f g : LoopPlane → M}
    (h : g =ᵐ[volume.restrict S] f ∘ T) :
    g ∘ T =ᵐ[volume.restrict S] f := by
  filter_upwards [m64AnnulusHalfTurn_measurePreserving.quasiMeasurePreserving.ae h,
    m64AnnulusHalfTurn_involutive_ae] with p hp hT
  simpa only [Function.comp_apply, hT] using hp

theorem m64AnnulusHalfTurn_left_overlap {M : Type*} [TopologicalSpace M] [T2Space M]
    {f g : LoopPlane → M} (hf : ContinuousOn f D) (hg : ContinuousOn g D)
    (hae : g =ᵐ[volume.restrict S] f ∘ T) :
    EqOn f (fun p => g (p + v))
      {p : LoopPlane | p 0 ∈ Ioo (0 : ℝ) half ∧ p 1 ∈ Icc (0 : ℝ) 1} := by
  let O := m64AnnulusHalfLeft
  let C : Set LoopPlane := {p | p 0 ∈ Ioo (0 : ℝ) half ∧ p 1 ∈ Icc (0 : ℝ) 1}
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hCD : C ⊆ D := fun p hp => ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩
  have hOC : O ⊆ C := fun p hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2.1.le, hp.2.2.2.le⟩
  have hm : MapsTo (fun p : LoopPlane => p + v) C D := by
    intro p hp
    change (p + v) 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ (p + v) 1 ∈ Icc (0 : ℝ) 1
    simp only [PiLp.add_apply, annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero, add_zero]
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩
  have hgc : ContinuousOn (fun p => g (p + v)) C :=
    hg.comp (continuous_id.add continuous_const).continuousOn hm
  have hOS : O ⊆ S := fun p hp => (m64AnnulusInterior_coordinates p).mpr
    ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩
  have hga : (fun p => g (p + v)) =ᵐ[volume.restrict O] f := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hOS
      (m64AnnulusHalfTurn_ae_reverse hae),
      ae_restrict_mem m64AnnulusHalfLeft_isOpen.measurableSet] with p hp hpO
    simpa only [Function.comp_apply, m64AnnulusHalfTurn, if_pos hpO.2.1] using hp
  have heq : EqOn f (fun p => g (p + v)) O :=
    (Measure.eqOn_open_of_ae_eq hga m64AnnulusHalfLeft_isOpen
      (hgc.mono hOC) (hf.mono (hOC.trans hCD))).symm
  apply heq.of_subset_closure (hf.mono hCD) hgc hOC
  simpa only [O, m64AnnulusHalfLeft, C, mem_Ioo, mem_Icc, and_assoc] using
    m64RadialStrip_subset_closure 0 half

theorem m64AnnulusHalfTurn_right_overlap {M : Type*} [TopologicalSpace M] [T2Space M]
    {f g : LoopPlane → M} (hf : ContinuousOn f D) (hg : ContinuousOn g D)
    (hae : g =ᵐ[volume.restrict S] f ∘ T) :
    EqOn f (fun p => g (p - v))
      {p : LoopPlane | p 0 ∈ Ioo half curvePeriod ∧ p 1 ∈ Icc (0 : ℝ) 1} := by
  let O := m64AnnulusHalfRight
  let C : Set LoopPlane := {p | p 0 ∈ Ioo half curvePeriod ∧ p 1 ∈ Icc (0 : ℝ) 1}
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hCD : C ⊆ D := fun p hp => ⟨⟨by linarith [hp.1.1], hp.1.2⟩, hp.2⟩
  have hOC : O ⊆ C := fun p hp => ⟨⟨hp.1, hp.2.1⟩, hp.2.2.1.le, hp.2.2.2.le⟩
  have hm : MapsTo (fun p : LoopPlane => p - v) C D := by
    intro p hp
    change (p - v) 0 ∈ Ioo (0 : ℝ) curvePeriod ∧ (p - v) 1 ∈ Icc (0 : ℝ) 1
    simp only [PiLp.sub_apply, annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero, sub_zero]
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩
  have hgc : ContinuousOn (fun p => g (p - v)) C :=
    hg.comp (continuous_id.sub continuous_const).continuousOn hm
  have hOS : O ⊆ S := fun p hp => (m64AnnulusInterior_coordinates p).mpr
    ⟨by linarith [hp.1], hp.2⟩
  have hga : (fun p => g (p - v)) =ᵐ[volume.restrict O] f := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hOS
      (m64AnnulusHalfTurn_ae_reverse hae),
      ae_restrict_mem m64AnnulusHalfRight_isOpen.measurableSet] with p hp hpO
    simpa only [Function.comp_apply, m64AnnulusHalfTurn,
      if_neg (not_lt.mpr hpO.1.le)] using hp
  have heq : EqOn f (fun p => g (p - v)) O :=
    (Measure.eqOn_open_of_ae_eq hga m64AnnulusHalfRight_isOpen
      (hgc.mono hOC) (hf.mono (hOC.trans hCD))).symm
  apply heq.of_subset_closure (hf.mono hCD) hgc hOC
  simpa only [O, m64AnnulusHalfRight, C, mem_Ioo, mem_Icc, and_assoc] using
    m64RadialStrip_subset_closure half curvePeriod

end PoincareConjecture

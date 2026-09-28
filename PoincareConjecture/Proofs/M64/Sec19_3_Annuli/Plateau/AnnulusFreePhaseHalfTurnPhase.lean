import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfTurnMeasure
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementIntegration
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusFreePhaseHalfTurnLabels
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusFreePhaseSeamObservation

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

open Proofs.M58

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "K" => m64AnnulusHalfLeft
local notation "T" => m64AnnulusHalfTurn
local notation "a" => curvePeriod / 2

local instance (p : LoopPlane) : Decidable (p ∈ m64AnnulusHalfLeft) :=
  Classical.propDecidable _

def m64FreePhaseHalfTurn (u : LoopPlane → ℝ) (D : ℝ) (p : LoopPlane) : ℝ :=
  if p 0 < a then u (T p) else u (T p) + D

theorem m64AnnulusHalfLeft_subset_interior :
    m64AnnulusHalfLeft ⊆ S := by
  intro p hp
  apply (m64AnnulusInterior_coordinates p).mpr
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  exact ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩

theorem m64FreePhaseHalfTurn_eq_piecewise
    {u : LoopPlane → ℝ} {D : ℝ} :
    ∀ᵐ p ∂mu,
      m64FreePhaseHalfTurn u D p =
        m64AnnulusHalfLeft.piecewise (u ∘ T) (fun q => u (T q) + D) p := by
  classical
  have hcoord : ∀ᵐ p ∂mu, p ∈ S ∧ (p 0 < a ↔ p ∈ K) := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    refine ⟨hp, ?_⟩
    constructor
    · intro hleft
      exact ⟨(m64AnnulusInterior_coordinates p).mp hp |>.1, hleft,
        (m64AnnulusInterior_coordinates p).mp hp |>.2.2⟩
    · intro hpK
      exact hpK.2.1
  filter_upwards [hcoord] with p hp
  by_cases hk : p ∈ K
  · have hlt : p 0 < a := hp.2.mpr hk
    simp only [m64FreePhaseHalfTurn, Set.piecewise, hk, hlt,
      Function.comp_apply]
  · have hlt : ¬p 0 < a := fun h => hk (hp.2.mp h)
    simp only [m64FreePhaseHalfTurn, Set.piecewise, hk, hlt,
      Function.comp_apply]

theorem m64FreePhaseHalfTurn_memLp
    {u : LoopPlane → ℝ} (hu : MemLp u 2 mu) (D : ℝ) :
    MemLp (m64FreePhaseHalfTurn u D) 2 mu := by
  classical
  let _ : IsFiniteMeasure mu := isFiniteMeasure_restrict.mpr
    ((measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top).ne
  have huT : MemLp (u ∘ T) 2 mu := m64AnnulusHalfTurn_memLp hu
  have huTD : MemLp (fun p => u (T p) + D) 2 mu :=
    huT.add (memLp_const D)
  have hleft : MemLp (u ∘ T) 2 (volume.restrict K) := by
    simpa only [Measure.restrict_restrict, inter_eq_left.mpr
      m64AnnulusHalfLeft_subset_interior] using
      huT.mono_measure (Measure.restrict_mono
        m64AnnulusHalfLeft_subset_interior le_rfl)
  have hpw := m64MemLp_piecewise_of_subset
    m64AnnulusHalfLeft_isOpen.measurableSet m64AnnulusHalfLeft_subset_interior
    hleft huTD
  have heq :
      m64AnnulusHalfLeft.piecewise (u ∘ T) (fun q => u (T q) + D) =ᵐ[mu]
        m64FreePhaseHalfTurn u D := by
    filter_upwards [m64FreePhaseHalfTurn_eq_piecewise (u := u) (D := D)] with p hp
    exact hp.symm
  exact MemLp.ae_eq heq hpw

theorem m64FreePhaseHalfTurn_left
    {u : LoopPlane → ℝ} {D : ℝ} {p : LoopPlane} (hp : p ∈ K) :
    m64FreePhaseHalfTurn u D p = u (T p) := by
  simp only [m64FreePhaseHalfTurn, hp.2.1, ↓reduceIte]

theorem m64FreePhaseHalfTurn_right
    {u : LoopPlane → ℝ} {D : ℝ} {p : LoopPlane}
    (hp : p ∈ m64AnnulusHalfRight) :
    m64FreePhaseHalfTurn u D p = u (T p) + D := by
  simp only [m64FreePhaseHalfTurn]
  rw [if_neg]
  linarith [hp.1]

theorem m64FreePhaseHalfTurn_observation
    {u : LoopPlane → ℝ} {k : ℝ} {D : ℝ}
    (hperiod : angularPoint (k * D) = angularPoint 0)
    {F : LoopPlane → LoopPlane}
    (hobs : F =ᵐ[mu] fun p => angularPoint (k * u p)) :
    (fun p => F (T p)) =ᵐ[mu]
      fun p => angularPoint (k * m64FreePhaseHalfTurn u D p) := by
  have hT := m64AnnulusHalfTurn_measurePreserving.quasiMeasurePreserving.ae hobs
  filter_upwards [hT] with p hp
  rw [hp]
  by_cases hleft : p 0 < a
  · simp [m64FreePhaseHalfTurn, hleft]
  · have hshift := m64AngularPoint_sub_phase_period hperiod (u (T p) + D)
    simpa [m64FreePhaseHalfTurn, hleft] using hshift

end PoincareConjecture

import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.HalfTurnMeasure
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.ReplacementIntegration
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.FreePhaseHalfTurnLabels
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.FreePhaseSeamObservation

/-! The affine phase correction that moves the angular cut through a half-turn.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareMT

open Proofs.M58

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "K" => m64AnnulusHalfLeft
local notation "T" => m64AnnulusHalfTurn
local notation "a" => curvePeriod / 2

local instance (p : LoopPlane) : Decidable (p ∈ m64AnnulusHalfLeft) :=
  Classical.propDecidable _

/-- Rotate the real phase by half a period and add its winding increment on the second half.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
def m64FreePhaseHalfTurn (u : LoopPlane → ℝ) (D : ℝ) (p : LoopPlane) : ℝ :=
  if p 0 < a then u (T p) else u (T p) + D

/-- The left open half-rectangle lies in the open annular rectangle. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
theorem m64AnnulusHalfLeft_subset_interior :
    m64AnnulusHalfLeft ⊆ S := by
  intro p hp
  apply (m64AnnulusInterior_coordinates p).mpr
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  exact ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩

/-- Represent the corrected phase almost everywhere by its two actual half-rectangle
formulas. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
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

/-- Half-turn rotation with a constant winding correction preserves L2 phase integrability.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
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

/-- On the left open half-rectangle the corrected phase is the rotated original phase. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
theorem m64FreePhaseHalfTurn_left
    {u : LoopPlane → ℝ} {D : ℝ} {p : LoopPlane} (hp : p ∈ K) :
    m64FreePhaseHalfTurn u D p = u (T p) := by
  simp only [m64FreePhaseHalfTurn, hp.2.1, ↓reduceIte]

/-- On the right open half-rectangle the corrected phase adds the winding increment. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
theorem m64FreePhaseHalfTurn_right
    {u : LoopPlane → ℝ} {D : ℝ} {p : LoopPlane}
    (hp : p ∈ m64AnnulusHalfRight) :
    m64FreePhaseHalfTurn u D p = u (T p) + D := by
  simp only [m64FreePhaseHalfTurn]
  rw [if_neg]
  linarith [hp.1]

/-- The winding-corrected phase retains the rotated circle observation almost everywhere.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-free-phase-cut-rotation.md. -/
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

end PoincareMT

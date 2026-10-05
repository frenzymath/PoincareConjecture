import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Terminal.Source.TerminalSourceCountableCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Collar.Coordinates.ClosedTimeJets

/-!
# Smooth coefficients before every countable stage is available

Available indices use the original closed source flow and chart. Early
indices use only a smooth coefficient extension of the actual terminal
pullback. No Ricci-flow assertion is made about that extension.
MT Theorem 5.11 and Proposition 5.14, pp. 89-91;
terminal-source-countable-coefficients.md, B.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

variable (j : ℕ) (M : {k : ℕ // j ≤ k} → Type u)
  [∀ a, TopologicalSpace (M a)] [∀ a, ChartedSpace E (M a)]
  [∀ a, IsManifold (𝓡 3) ∞ (M a)]
  {tau R : ℝ}
  (F : ∀ a, RicciFlow 3 (M a) (Icc (-tau) 0))
  (C : ∀ a, TerminalSourceChart ((F a).metric 0) R)

/-- The original good-index flow coefficients, with smooth terminal
coefficients at early indices where that source is unavailable. -/
noncomputable def terminalSourceCountableNegative
    (f0 : ℕ → E → V) (k : ℕ) : ℝ × E → V :=
  if hjk : j ≤ k then fun p =>
    ((F ⟨k, hjk⟩).metric p.1).pullbackCoefficients (C ⟨k, hjk⟩).chart p.2
  else fun p => f0 k p.2

/-- Every available index retains the full original flow coefficient
function, including its actual source chart and included time clock. -/
theorem terminalSourceCountableNegative_good (f0 : ℕ → E → V)
    {k : ℕ} (hjk : j ≤ k) :
    terminalSourceCountableNegative j M F C f0 k =
      fun p : ℝ × E =>
        ((F ⟨k, hjk⟩).metric p.1).pullbackCoefficients (C ⟨k, hjk⟩).chart p.2 := by
  simp only [terminalSourceCountableNegative, dif_pos hjk]

/-- The total family is smooth within the original closed product at
every index; early indices assert smoothness of coefficients only. -/
theorem terminalSourceCountableNegative_smooth
    (U : Opens E) (hUR : (U : Set E) ⊆ Metric.ball 0 R)
    (f0 : ℕ → E → V) (hf0 : ∀ k, ContDiffOn ℝ ∞ (f0 k) U) :
    ∀ k, ContDiffOn ℝ ∞ (terminalSourceCountableNegative j M F C f0 k)
      (Icc (-tau) 0 ×ˢ (U : Set E)) := by
  intro k
  by_cases hjk : j ≤ k
  · rw [terminalSourceCountableNegative_good j M F C f0 hjk]
    exact (M44.contDiffOn_pullbackCoefficients_within (F ⟨k, hjk⟩)
      Metric.isOpen_ball (C ⟨k, hjk⟩).smooth).mono
        (prod_mono (Subset.refl _) hUR)
  · simp only [terminalSourceCountableNegative, dif_neg hjk]
    exact (hf0 k).comp contDiffOn_snd (fun _ hp => hp.2)

/-- Included zero agrees with the actual physical terminal coefficients
on the open domain in both the good and early branches. -/
theorem terminalSourceCountableNegative_zero
    (U : Opens E) (f0 : ℕ → E → V)
    (hread : ∀ a, EqOn (f0 a.val)
      (((F a).metric 0).pullbackCoefficients (C a).chart) U) :
    ∀ k, EqOn (fun x => terminalSourceCountableNegative j M F C f0 k (0, x))
      (f0 k) U := by
  intro k x hx
  by_cases hjk : j ≤ k
  · rw [terminalSourceCountableNegative_good j M F C f0 hjk]
    exact (hread ⟨k, hjk⟩ hx).symm
  · simp only [terminalSourceCountableNegative, dif_neg hjk]

/-- Every fixed stage eventually uses its genuine original source;
the eventual statement includes the actual good-index witness. -/
theorem terminalSourceCountableNegative_eventually_good (f0 : ℕ → E → V) :
    ∀ᶠ k in atTop, ∃ hjk : j ≤ k,
      terminalSourceCountableNegative j M F C f0 k =
        fun p : ℝ × E =>
          ((F ⟨k, hjk⟩).metric p.1).pullbackCoefficients (C ⟨k, hjk⟩).chart p.2 := by
  filter_upwards [eventually_ge_atTop j] with k hk
  exact ⟨hk, terminalSourceCountableNegative_good j M F C f0 hk⟩

/-- The unchanged good-index coefficient function retains every mixed
derivative, without a time extension or a new metric realization. -/
theorem terminalSourceCountableNegative_good_jets (f0 : ℕ → E → V)
    {k : ℕ} (hjk : j ≤ k) (m : ℕ) (p : ℝ × E) :
    iteratedFDeriv ℝ m (terminalSourceCountableNegative j M F C f0 k) p =
      iteratedFDeriv ℝ m
        (fun q : ℝ × E => ((F ⟨k, hjk⟩).metric q.1).pullbackCoefficients
          (C ⟨k, hjk⟩).chart q.2) p := by
  rw [terminalSourceCountableNegative_good j M F C f0 hjk]

end PoincareMT.M47

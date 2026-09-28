import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialCompletion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusContinuity

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory
open scoped Topology Manifold

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k degree : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem with_radial_completion
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k degree) :
    ∃ W : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k degree,
      W.annulus.map = m64AnnulusRadialCompletion A.annulus.map
        (c0 ∘ A.label0) (c1 ∘ A.label1) ∧
      W.label0 = A.label0 ∧ W.label1 = A.label1 ∧ W.annulus.column = A.annulus.column ∧
      W.phase = A.phase ∧ W.phaseColumn = A.phaseColumn ∧ W.offset = A.offset ∧
      ∀ (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (s : ℝ),
        W.annulus.weightedEnergy Q s = A.annulus.weightedEnergy Q s := by
  let f := m64AnnulusRadialCompletion A.annulus.map (c0 ∘ A.label0) (c1 ∘ A.label1)
  have hfae : f =ᵐ[mu] A.annulus.map := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    have hc := (m64AnnulusInterior_coordinates p).mp hp
    exact m64AnnulusRadialCompletion_interior _ _ _ ⟨hc.2.2.1, hc.2.2.2⟩
  obtain ⟨O, hmap, hcolumn, -⟩ := A.annulus.with_map_ae f hfae
  have hOae : O.map =ᵐ[mu] A.annulus.map := hmap ▸ hfae
  let W : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k degree := {
    A with
    annulus := O
    phase_observation := by
      filter_upwards [hOae, A.phase_observation] with p hp ho
      simpa only [hp] using ho }
  exact ⟨W, hmap, rfl, rfl, hcolumn, rfl, rfl, rfl,
    A.annulus.weightedEnergy_eq_of_map_ae O hOae hcolumn⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus

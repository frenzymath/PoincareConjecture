import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ClosedC1Admission
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeRadialCompletion

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k degree : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem with_map_ae
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k degree)
    (f : LoopPlane → M) (hfae : f =ᵐ[mu] A.annulus.map) :
    ∃ W : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k degree,
      W.annulus.map = f ∧ W.label0 = A.label0 ∧ W.label1 = A.label1 ∧
      W.annulus.column = A.annulus.column ∧ W.phase = A.phase ∧
      W.phaseColumn = A.phaseColumn ∧ W.offset = A.offset ∧
      ∀ (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (s : ℝ),
        W.annulus.weightedEnergy Q s = A.annulus.weightedEnergy Q s := by
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

variable [T2Space M] [IsManifold (𝓡 n) ∞ M]

theorem exists_classical_completion
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k degree)
    (g : RiemannianMetric n M)
    (hc0 : Function.Periodic c0 curvePeriod) (hc1 : Function.Periodic c1 curvePeriod)
    (f : LoopPlane → M) (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain)
    (heq : EqOn f A.annulus.map S)
    (hseam : ∀ y ∈ Icc (0 : ℝ) 1,
      f (annulusPoint curvePeriod y) = f (annulusPoint 0 y))
    (h0 : ∀ x ∈ Icc (0 : ℝ) curvePeriod, f (annulusPoint x 0) = c0 (A.label0 x))
    (h1 : ∀ x ∈ Icc (0 : ℝ) curvePeriod, f (annulusPoint x 1) = c1 (A.label1 x)) :
    ∃ B : M64Annulus g (c0 ∘ A.label0) (c1 ∘ A.label1),
      ContMDiffOn (𝓡 2) (𝓡 n) 1 B.map m64AnnulusDomain ∧
      EqOn B.map A.annulus.map S ∧
      ∃ W : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k degree,
        W.annulus.map = B.map ∧ W.label0 = A.label0 ∧ W.label1 = A.label1 ∧
        W.annulus.column = A.annulus.column ∧ W.phase = A.phase ∧
        W.phaseColumn = A.phaseColumn ∧ W.offset = A.offset ∧
        ∀ (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (s : ℝ),
          W.annulus.weightedEnergy Q s = A.annulus.weightedEnergy Q s := by
  have hp0 : Function.Periodic (c0 ∘ A.label0) curvePeriod := by
    intro x
    simp only [Function.comp_apply, A.label0_period]
    exact hc0 _
  have hp1 : Function.Periodic (c1 ∘ A.label1) curvePeriod := by
    intro x
    simp only [Function.comp_apply, A.label1_period]
    exact hc1 _
  obtain ⟨B, hB⟩ := m64Annulus_exists_eqOn_rectangle_of_contMDiffOn g hp0 hp1 f hf
    hseam h0 h1
  have hBA : EqOn B.map A.annulus.map S := (hB.mono interior_subset).trans heq
  have hBae : B.map =ᵐ[mu] A.annulus.map :=
    (ae_restrict_mem isOpen_interior.measurableSet).mono fun _ hp => hBA hp
  exact ⟨B, hf.congr hB, hBA, A.with_map_ae B.map hBae⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus

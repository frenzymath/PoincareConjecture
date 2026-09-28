import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseLowerReflection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakScalarCutoffGraph
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakPhaseCutoffGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.StrongGraphPhaseTrace

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "ei" i => EuclideanSpace.single (i : Fin 2) (1 : ℝ)

theorem localized_lower_phase_graph
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    (chi : LoopPlane → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hs : tsupport chi ⊆ O) :
    let F := fun p => chi p * A.lowerReflectedPhase p
    let W := fun i => (O).indicator (fun p => chi p * A.lowerReflectedPhaseColumn i p +
      fderiv ℝ chi p (ei i) * A.lowerReflectedPhase p)
    let b := fun x => chi (annulusPoint x 0) * H0 (A.label0 x)
    MemLp F 2 volume ∧ (∀ i, MemLp (W i) 2 volume) ∧
      ∃ f : ℕ → LoopPlane → ℝ, (∀ j, ContDiff ℝ ∞ (f j)) ∧
        Tendsto (fun j => eLpNorm (f j - F) 2 volume) atTop (𝓝 0) ∧
        (∀ i, Tendsto (fun j => eLpNorm (fun p => fderiv ℝ (f j) p (ei i) - W i p)
          2 volume) atTop (𝓝 0)) ∧
        Tendsto (fun j => eLpNorm (fun x => f j (annulusPoint x 0) - b x)
          2 (volume.restrict I)) atTop (𝓝 0) := by
  classical
  dsimp only
  let F := fun p => chi p * A.lowerReflectedPhase p
  let W := fun i => (O).indicator (fun p => chi p * A.lowerReflectedPhaseColumn i p +
    fderiv ℝ chi p (ei i) * A.lowerReflectedPhase p)
  let b := fun x => chi (annulusPoint x 0) * H0 (A.label0 x)
  obtain ⟨hF, hW, _, f, hf, hval, hcol⟩ := m64WeakScalar_cutoff_strong_graph
    m64AnnulusLowerDomain_isOpen A.lowerReflectedPhase A.lowerReflectedPhaseColumn
    A.lower_reflected_phase_memLp.1 A.lower_reflected_phase_memLp.2
    A.lower_reflected_phase_weak chi hchi hc hs
  refine ⟨hF, hW, f, hf, hval, hcol, ?_⟩
  have hFpoint (p : LoopPlane) (hp : p ∈ S) : F p = chi p * A.phase p := by
    simp only [F, lowerReflectedPhase, m64AnnulusLowerExtend_right _ _ hp]
  have hWpoint (p : LoopPlane) (hp : p ∈ S) : W 1 p =
      chi p * A.phaseColumn 1 p + fderiv ℝ chi p (ei 1) * A.phase p := by
    simp only [W, indicator_of_mem (m64AnnulusLower_rect_subset hp),
      lowerReflectedPhaseColumn, lowerReflectedPhase, m64AnnulusLowerExtend_right _ _ hp]
  have hbc : Continuous b := by
    have hline : Continuous (fun x : ℝ => annulusPoint x 0) := by
      have hd : ContDiff ℝ 1 (fun x : ℝ => annulusPoint x 0) := by
        apply contDiff_euclidean.mpr
        intro i
        fin_cases i
        · exact contDiff_id
        · exact contDiff_const
      exact hd.continuous
    exact (hchi.continuous.comp hline).mul
      (H0.continuous.comp (A.labels_continuous hH0 hH1).1)
  have hb : MemLp b 2 (volume.restrict I) :=
    (memLp_two_iff_integrable_sq hbc.aestronglyMeasurable).mpr
      ((hbc.pow 2).integrableOn_Icc)
  have hvs : Tendsto (fun j => eLpNorm (f j - F) 2 (volume.restrict S))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hval
      (fun _ => bot_le) (fun j => eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hds : Tendsto (fun j => eLpNorm
      (fun p => fderiv ℝ (f j) p (ei 1) - W 1 p) 2 (volume.restrict S))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hcol 1)
      (fun _ => bot_le) (fun j => eLpNorm_mono_measure _ Measure.restrict_le_self)
  apply m64WeakPhase_strong_graph_trace f (fun j => (hf j).of_le (by simp))
    (hF.mono_measure Measure.restrict_le_self) ((hW 1).mono_measure Measure.restrict_le_self)
    hvs hds b hb
  intro phi hphi htop
  have hg := m64WeakPhase_cutoff_green (Lp.memLp A.phase) (Lp.memLp (A.phaseColumn 1))
    (fun x => H0 (A.label0 x)) (fun psi hpsi hpsiTop => by
      simpa [hpsiTop, integral_neg] using A.phase_boundary psi hpsi)
    (hchi.of_le (by simp)) hphi htop
  have hvalEq : (∫ p in S, fderiv ℝ phi p (ei 1) * F p) =
      ∫ p in S, fderiv ℝ phi p (ei 1) * (chi p * A.phase p) := by
    apply setIntegral_congr_fun isOpen_interior.measurableSet
    intro p hp
    dsimp only
    rw [hFpoint p hp]
  have hcolEq : (∫ p in S, phi p * W 1 p) =
      ∫ p in S, phi p * (chi p * A.phaseColumn 1 p +
        fderiv ℝ chi p (ei 1) * A.phase p) := by
    apply setIntegral_congr_fun isOpen_interior.measurableSet
    intro p hp
    dsimp only
    rw [hWpoint p hp]
  rw [hvalEq, hcolEq]
  exact hg

end PoincareConjecture.M64FreeWeakPhaseAnnulus

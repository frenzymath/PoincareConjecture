import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialIntegration
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialTests
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RadialFlipGeometry














noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain
local notation "T" => m64AnnulusRadialFlip
local notation "v" => m64AnnulusRadialTranslation
local notation "ei" i => EuclideanSpace.single (i : Fin 2) (1 : ℝ)




def lowerReflectedPhase (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D) :
    LoopPlane → ℝ := m64AnnulusLowerExtend (A.phase ∘ T) A.phase




def lowerReflectedPhaseColumn
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D) (i : Fin 2) :
    LoopPlane → ℝ := m64AnnulusLowerExtend
      (fun p => (if i = 0 then (1 : ℝ) else -1) * A.phaseColumn i (T p)) (A.phaseColumn i)




theorem lower_reflected_phase_memLp
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D) :
    MemLp A.lowerReflectedPhase 2 (volume.restrict O) ∧
      ∀ i, MemLp (A.lowerReflectedPhaseColumn i) 2 (volume.restrict O) := by
  refine ⟨m64AnnulusLowerExtend_memLp
    ((Lp.memLp A.phase).comp_measurePreserving m64AnnulusRadialFlip_restrict_measurePreserving)
    (Lp.memLp A.phase), ?_⟩
  intro i
  exact m64AnnulusLowerExtend_memLp
    (((Lp.memLp (A.phaseColumn i)).comp_measurePreserving
      m64AnnulusRadialFlip_restrict_measurePreserving).const_mul _) (Lp.memLp (A.phaseColumn i))

private theorem phase_lower_green
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi)
    (ht : ∀ x, phi (annulusPoint x 1) = 0)
    (hl : ∀ s, phi (annulusPoint 0 s) = 0)
    (hr : ∀ s, phi (annulusPoint curvePeriod s) = 0) (i : Fin 2) :
    (∫ p in S, phi p * A.phaseColumn i p) +
      (∫ p in S, fderiv ℝ phi p (ei i) * A.phase p) =
      if i = 1 then -(∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 0) * H0 (A.label0 x)) else 0 := by
  fin_cases i
  · simpa [hr] using
      A.phase_seam phi hp (fun s _ => by rw [hl, hr])
  · simpa [ht, integral_neg] using A.phase_boundary phi hp





theorem lower_reflected_phase_weak
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D) (i : Fin 2) :
    HasWeakPartialDeriv i (A.lowerReflectedPhaseColumn i) A.lowerReflectedPhase O := by
  intro phi hps hc hs
  have hp : ContDiff ℝ 1 phi := hps.of_le (by simp)
  let dphi := fun p => fderiv ℝ phi p (ei i)
  let psi := fun p => phi (p - v)
  have hpsi : ContDiff ℝ 1 psi := hp.comp (contDiff_id.sub contDiff_const)
  have hder (p : LoopPlane) : fderiv ℝ psi p (ei i) = dphi (p - v) :=
    m64FDeriv_sub_translation hp v p (ei i)
  obtain ⟨htop, hbottom, hleft, hright⟩ := m64LowerTest_boundary_zero hs
  have hpM : MemLp phi 2 (volume.restrict O) :=
    (hp.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
  have hdM : MemLp dphi 2 (volume.restrict O) :=
    (((hp.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).mono_measure Measure.restrict_le_self
  have hF := (Lp.memLp A.phase).comp_measurePreserving
    m64AnnulusRadialFlip_restrict_measurePreserving
  have hW := ((Lp.memLp (A.phaseColumn i)).comp_measurePreserving
    m64AnnulusRadialFlip_restrict_measurePreserving).const_mul
      (if i = 0 then (1 : ℝ) else -1)
  have hbelow : (∫ p in S, psi p * ((if i = 0 then (1 : ℝ) else -1) * A.phaseColumn i (T p))) +
      (∫ p in S, dphi (p - v) * A.phase (T p)) =
      if i = 1 then ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 0) * H0 (A.label0 x) else 0 := by
    have hflip := m64AnnulusRadialFlip_green A.phase (A.phaseColumn i) hpsi i
    have heta : ContDiff ℝ 1 (psi ∘ T) :=
      hpsi.comp (m64AnnulusRadialFlip_contDiff.of_le (by simp))
    have he := A.phase_lower_green heta
      (fun x => by simp only [Function.comp_apply, psi, m64AnnulusRadialFlip_point,
        m64AnnulusPoint_sub_radialTranslation, sub_self, zero_sub, hbottom])
      (fun s => by simp only [Function.comp_apply, psi, m64AnnulusRadialFlip_point,
        m64AnnulusPoint_sub_radialTranslation, hleft])
      (fun s => by simp only [Function.comp_apply, psi, m64AnnulusRadialFlip_point,
        m64AnnulusPoint_sub_radialTranslation, hright]) i
    simp only [smul_eq_mul, hder] at hflip
    rw [he] at hflip
    fin_cases i <;> simpa [Function.comp_apply, psi, m64AnnulusRadialFlip_point,
      m64AnnulusPoint_sub_radialTranslation] using hflip
  have hsum : (∫ p in O, phi p * A.lowerReflectedPhaseColumn i p) +
      (∫ p in O, dphi p * A.lowerReflectedPhase p) = 0 := by
    have hcol := m64AnnulusLowerExtend_integral_smul hW (Lp.memLp (A.phaseColumn i)) hpM
    have hval := m64AnnulusLowerExtend_integral_smul hF (Lp.memLp A.phase) hdM
    simp only [smul_eq_mul, Function.comp_apply] at hcol hval
    rw [lowerReflectedPhaseColumn, lowerReflectedPhase, hcol, hval]
    have habove := A.phase_lower_green hp htop hleft hright i
    dsimp only [Function.comp_apply] at *
    change (∫ p in S, phi p * A.phaseColumn i p) +
      (∫ p in S, psi p * ((if i = 0 then (1 : ℝ) else -1) * A.phaseColumn i (T p))) +
      ((∫ p in S, dphi p * A.phase p) + ∫ p in S, dphi (p - v) * A.phase (T p)) = 0
    dsimp only [dphi] at hbelow ⊢
    by_cases hi : i = 1
    · rw [if_pos hi] at habove hbelow
      linarith
    · rw [if_neg hi] at habove hbelow
      linarith
  change (∫ p in O, A.lowerReflectedPhase p * dphi p) =
    -(∫ p in O, A.lowerReflectedPhaseColumn i p * phi p)
  simp only [mul_comm] at hsum ⊢
  linarith

end PoincareConjecture.M64FreeWeakPhaseAnnulus

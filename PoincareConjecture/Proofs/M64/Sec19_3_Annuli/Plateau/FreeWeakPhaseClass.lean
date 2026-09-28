import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryObservedPhaseEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryRealTwoTraceCompactness













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)




structure M64FreeWeakPhaseAnnulus (e : M → E) (R : E →L[ℝ] LoopPlane)
    (c0 c1 : ℝ → M) (H0 H1 : ℝ ≃o ℝ) (k D : ℝ) where
  label0 : ℝ → ℝ
  label1 : ℝ → ℝ
  label0_monotone : Monotone label0
  label1_monotone : Monotone label1
  label0_period : ∀ x, label0 (x + curvePeriod) = label0 x + curvePeriod
  label1_period : ∀ x, label1 (x + curvePeriod) = label1 x + curvePeriod
  label0_normalized : label0 0 ∈ Icc (0 : ℝ) curvePeriod
  label1_normalized : label1 0 ∈ Icc (0 : ℝ) curvePeriod
  annulus : M64ObservedWeakAnnulus (n := n) e (c0 ∘ label0) (c1 ∘ label1)
  phase : Lp ℝ 2 mu
  phaseColumn : Fin 2 → Lp ℝ 2 mu
  phase_weak : ∀ i, HasWeakPartialDeriv i (phaseColumn i) phase S
  phase_observation : (fun p => R (e (annulus.map p))) =ᵐ[mu]
    fun p => angularPoint (k * phase p)
  offset : ℝ
  offset_circle : angularPoint (k * offset) = angularPoint 0
  phase_boundary : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
    (∫ p in S, phi p * phaseColumn 1 p) + (∫ p in S, fderiv ℝ phi p e1 * phase p) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) * (H1 (label1 x) + offset) -
          phi (annulusPoint x 0) * H0 (label0 x)
  phase_seam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
    (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
    (∫ p in S, phi p * phaseColumn 0 p) + (∫ p in S, fderiv ℝ phi p e0 * phase p) =
      D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)

namespace M64FreeWeakPhaseAnnulus

variable {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}




theorem labels_continuous
    (A : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D) :
    Continuous A.label0 ∧ Continuous A.label1 := by
  let b0 := fun x => H0 (A.label0 x)
  let b1 := fun x => H1 (A.label1 x) + A.offset
  have hb0 : Monotone b0 := H0.monotone.comp A.label0_monotone
  have hb1 : Monotone b1 := (H1.monotone.comp A.label1_monotone).add_const _
  have hp0 (x : ℝ) : b0 (x + curvePeriod) = b0 x + D := by
    dsimp only [b0]
    rw [A.label0_period, hH0]
  have hp1 (x : ℝ) : b1 (x + curvePeriod) = b1 x + D := by
    dsimp only [b1]
    rw [A.label1_period, hH1]
    ring
  have hc0 : Continuous b0 := by
    apply m64WeakPhase_monotone_affine_trace_continuous A.phase
      (fun i => A.phaseColumn i) b0 D (fun i => Lp.memLp (A.phaseColumn i)) hb0 hp0 A.phase_seam
    intro phi hphi htop
    simpa only [htop, zero_mul, zero_sub, integral_neg, b0] using A.phase_boundary phi hphi
  have hc1 : Continuous b1 := by
    apply m64WeakPhase_monotone_affine_upper_trace_continuous A.phase
      (fun i => A.phaseColumn i) b1 D (fun i => Lp.memLp (A.phaseColumn i)) hb1 hp1 A.phase_seam
    intro phi hphi hbottom
    simpa only [hbottom, zero_mul, sub_zero, b1] using A.phase_boundary phi hphi
  constructor
  · have h := H0.symm.continuous.comp hc0
    simpa only [Function.comp_def, b0, OrderIso.symm_apply_apply] using h
  · have h := H1.symm.continuous.comp
      (hc1.sub (continuous_const : Continuous (fun _ : ℝ => A.offset)))
    simpa only [Function.comp_def, b1, Pi.sub_apply, add_sub_cancel_right,
      OrderIso.symm_apply_apply] using h

end M64FreeWeakPhaseAnnulus
end PoincareConjecture

import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakPhaseFlux
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseBoundaryStressTrace














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain






theorem auxiliaryCircle_free_phase_mixed_boundary_equation
    (A : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D)
    {eta : LoopPlane → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hleft : ∀ s : ℝ,
      fderiv ℝ eta (annulusPoint 0 s) (EuclideanSpace.single 1 1) = 0)
    (hright : ∀ s : ℝ,
      fderiv ℝ eta (annulusPoint curvePeriod s) (EuclideanSpace.single 1 1) = 0)
    (htop : ∀ x : ℝ,
      fderiv ℝ eta (annulusPoint x 1) (EuclideanSpace.single 0 1) = 0) :
    (∫ x in Icc (0 : ℝ) curvePeriod,
        fderiv ℝ eta (annulusPoint x 0) (EuclideanSpace.single 0 1) *
          H0 (A.label0 x)) =
      (∫ p in S,
        fderiv ℝ eta p (EuclideanSpace.single 1 1) * A.phaseColumn 0 p) -
        ∫ p in S,
          fderiv ℝ eta p (EuclideanSpace.single 0 1) * A.phaseColumn 1 p := by
  let u : LoopPlane → ℝ := A.phase
  let V : Fin 2 → LoopPlane → ℝ := fun i => A.phaseColumn i
  let b : ℝ → ℝ := fun x => H0 (A.label0 x)
  have hgreen0 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s : ℝ, phi (annulusPoint 0 s) = 0) →
      (∀ s : ℝ, phi (annulusPoint curvePeriod s) = 0) →
      (∫ p in S, phi p * V 0 p) +
          (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single 0 1) * u p) = 0 := by
    intro phi hphi hleft0 hright0
    have hseam : ∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s) := by
      intro s hs
      rw [hright0 s, hleft0 s]
    have hphase := A.phase_seam phi hphi hseam
    have htopzero :
        (fun s : ℝ => phi (annulusPoint curvePeriod s)) = fun _ => 0 := by
      funext s
      exact hright0 s
    rw [htopzero, integral_zero, mul_zero] at hphase
    simpa only [u, V] using hphase
  have hgreen1 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V 1 p) +
          (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single 1 1) * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod,
          phi (annulusPoint x 0) * b x) := by
    intro phi hphi htop0
    have hphase := A.phase_boundary phi hphi
    have hrhs :
        (∫ x in Icc (0 : ℝ) curvePeriod,
          phi (annulusPoint x 1) * (H1 (A.label1 x) + A.offset) -
            phi (annulusPoint x 0) * H0 (A.label0 x)) =
          -(∫ x in Icc (0 : ℝ) curvePeriod,
            phi (annulusPoint x 0) * H0 (A.label0 x)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [htop0 x, zero_mul, zero_sub]
    rw [hrhs] at hphase
    simpa only [u, V, b] using hphase
  have hrot := m64WeakPhase_rotated_test_identity u V b hgreen0 hgreen1
    eta heta hleft hright htop
  simpa only [u, V, b] using hrot

end PoincareConjecture.M64FreeWeakPhaseAnnulus

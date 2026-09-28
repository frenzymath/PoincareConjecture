import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakPhaseFlux















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)






theorem m64WeakPhase_affine_bottom_test_identity
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ)
    (hgreen0 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s : ℝ, phi (annulusPoint 0 s) = 0) →
      (∀ s : ℝ, phi (annulusPoint curvePeriod s) = 0) →
      (∫ p in S, phi p * V 0 p) +
          (∫ p in S, fderiv ℝ phi p e0 * u p) = 0)
    (hgreen1 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V 1 p) +
          (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod,
          phi (annulusPoint x 0) * b x)) :
    (∫ x in Icc (0 : ℝ) curvePeriod, (curvePeriod - 2 * x) * b x) =
      -(∫ p in S, (p 0 * (curvePeriod - p 0)) * V 0 p) -
        ∫ p in S, ((curvePeriod - 2 * p 0) * (1 - p 1)) * V 1 p := by
  let eta : LoopPlane → ℝ := fun p => p 0 * (curvePeriod - p 0) * (1 - p 1)
  have heta : ContDiff ℝ ∞ eta := by
    dsimp only [eta]
    fun_prop
  have hderiv_apply (p v : LoopPlane) :
      fderiv ℝ eta p v =
        ((curvePeriod - 2 * p 0) * (1 - p 1)) * v 0 -
          (p 0 * (curvePeriod - p 0)) * v 1 := by
    have hp0 : HasFDerivAt (fun q : LoopPlane => q 0)
        (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ) p :=
      (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).hasFDerivAt
    have hp1 : HasFDerivAt (fun q : LoopPlane => q 1)
        (EuclideanSpace.proj (1 : Fin 2) : LoopPlane →L[ℝ] ℝ) p :=
      (EuclideanSpace.proj (1 : Fin 2) : LoopPlane →L[ℝ] ℝ).hasFDerivAt
    have hbase := hp0.mul
      ((hasFDerivAt_const (x := p) (c := (curvePeriod : ℝ))).sub hp0)
    have h := hbase.mul ((hasFDerivAt_const (x := p) (c := (1 : ℝ))).sub hp1)
    have hfun : (fun q : LoopPlane => q 0 * (curvePeriod - q 0) * (1 - q 1)) =
        (fun q : LoopPlane => q 0) * ((fun _ : LoopPlane => curvePeriod) -
          (fun q : LoopPlane => q 0)) *
          ((fun _ : LoopPlane => (1 : ℝ)) - (fun q : LoopPlane => q 1)) := by
      funext q
      simp only [Pi.mul_apply, Pi.sub_apply]
    have hfd := h.fderiv
    rw [← hfun] at hfd
    change (fderiv ℝ (fun q : LoopPlane => q 0 * (curvePeriod - q 0) * (1 - q 1)) p) v = _
    rw [hfd]
    simp only [add_apply, smul_apply, sub_apply, zero_apply, Pi.mul_apply, Pi.sub_apply,
      smul_eq_mul, PiLp.proj_apply]
    ring
  have hleft : ∀ s : ℝ,
      fderiv ℝ eta (annulusPoint 0 s) e1 = 0 := by
    intro s
    rw [hderiv_apply]
    simp [annulusPoint]
  have hright : ∀ s : ℝ,
      fderiv ℝ eta (annulusPoint curvePeriod s) e1 = 0 := by
    intro s
    rw [hderiv_apply]
    simp [annulusPoint]
  have htop : ∀ x : ℝ,
      fderiv ℝ eta (annulusPoint x 1) e0 = 0 := by
    intro x
    rw [hderiv_apply]
    simp [annulusPoint]
  have hmain := m64WeakPhase_rotated_test_identity u V b hgreen0 hgreen1
    eta heta hleft hright htop
  have hbottom : ∀ x : ℝ,
      fderiv ℝ eta (annulusPoint x 0) e0 = curvePeriod - 2 * x := by
    intro x
    rw [hderiv_apply]
    simp [annulusPoint]
  simp only [hbottom] at hmain
  have hV0 : ∀ p : LoopPlane,
      fderiv ℝ eta p e1 = -(p 0 * (curvePeriod - p 0)) := by
    intro p
    rw [hderiv_apply]
    simp
  have hV1 : ∀ p : LoopPlane,
      fderiv ℝ eta p e0 = (curvePeriod - 2 * p 0) * (1 - p 1) := by
    intro p
    rw [hderiv_apply]
    simp
  simp only [hV0, hV1] at hmain
  calc
    (∫ x in Icc (0 : ℝ) curvePeriod, (curvePeriod - 2 * x) * b x) =
        (∫ p in S, -(p 0 * (curvePeriod - p 0)) * V 0 p) -
          ∫ p in S, ((curvePeriod - 2 * p 0) * (1 - p 1)) * V 1 p := by
      simpa only [eta, annulusPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
        zero_mul, mul_one, one_mul, sub_zero, mul_assoc] using hmain
    _ = -(∫ p in S, (p 0 * (curvePeriod - p 0)) * V 0 p) -
          ∫ p in S, ((curvePeriod - 2 * p 0) * (1 - p 1)) * V 1 p := by
      rw [← integral_neg]
      apply congrArg (fun z : ℝ => z -
        ∫ p in S, ((curvePeriod - 2 * p 0) * (1 - p 1)) * V 1 p)
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => by ring)

end PoincareConjecture

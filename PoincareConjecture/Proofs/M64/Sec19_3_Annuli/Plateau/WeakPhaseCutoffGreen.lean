import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementIntegration

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "I" => Icc (0 : ℝ) curvePeriod
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

theorem m64WeakPhase_cutoff_green
    {u V : LoopPlane → ℝ} (hu : MemLp u 2 (volume.restrict S))
    (hV : MemLp V 2 (volume.restrict S)) (b : ℝ → ℝ)
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in I, phi (annulusPoint x 0) * b x))
    {chi phi : LoopPlane → ℝ} (hchi : ContDiff ℝ 1 chi)
    (hphi : ContDiff ℝ 1 phi) (htop : ∀ x : ℝ, phi (annulusPoint x 1) = 0) :
    (∫ p in S, phi p * (chi p * V p + fderiv ℝ chi p e1 * u p)) +
      (∫ p in S, fderiv ℝ phi p e1 * (chi p * u p)) =
        -(∫ x in I, phi (annulusPoint x 0) * (chi (annulusPoint x 0) * b x)) := by
  have hprod (p : LoopPlane) : fderiv ℝ (fun q => chi q * phi q) p e1 =
      chi p * fderiv ℝ phi p e1 + phi p * fderiv ℝ chi p e1 := by
    have hd := ((hchi.differentiable one_ne_zero p).hasFDerivAt.mul
      (hphi.differentiable one_ne_zero p).hasFDerivAt).fderiv
    exact congrArg (fun L : LoopPlane →L[ℝ] ℝ => L e1) hd
  have hDchi : Continuous (fun p => fderiv ℝ chi p e1) :=
    (hchi.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDphi : Continuous (fun p => fderiv ℝ phi p e1) :=
    (hphi.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hA : IntegrableOn (fun p => phi p * chi p * V p) S :=
    (m64Annulus_continuous_memLp_two (hphi.continuous.mul hchi.continuous)).integrable_mul hV
  have hB : IntegrableOn (fun p => phi p * fderiv ℝ chi p e1 * u p) S :=
    (m64Annulus_continuous_memLp_two (hphi.continuous.mul hDchi)).integrable_mul hu
  have hC : IntegrableOn (fun p => chi p * fderiv ℝ phi p e1 * u p) S :=
    (m64Annulus_continuous_memLp_two (hchi.continuous.mul hDphi)).integrable_mul hu
  have hg := hgreen (fun p => chi p * phi p) (hchi.mul hphi)
    (fun x => by rw [htop, mul_zero])
  have hleft : (∫ p in S, phi p * (chi p * V p + fderiv ℝ chi p e1 * u p)) =
      (∫ p in S, phi p * chi p * V p) + ∫ p in S, phi p * fderiv ℝ chi p e1 * u p := by
    rw [← integral_add hA hB]
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by ring)
  have hmiddle : (∫ p in S, fderiv ℝ (fun q => chi q * phi q) p e1 * u p) =
      (∫ p in S, chi p * fderiv ℝ phi p e1 * u p) +
        ∫ p in S, phi p * fderiv ℝ chi p e1 * u p := by
    rw [← integral_add hC hB]
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by dsimp only; rw [hprod]; ring)
  rw [hmiddle] at hg
  rw [hleft]
  have hpair : (∫ p in S, (chi p * phi p) * V p) =
      ∫ p in S, phi p * chi p * V p := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by ring)
  have hpairD : (∫ p in S, fderiv ℝ phi p e1 * (chi p * u p)) =
      ∫ p in S, chi p * fderiv ℝ phi p e1 * u p := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by ring)
  have hpairB : (∫ x in I, (chi (annulusPoint x 0) * phi (annulusPoint x 0)) * b x) =
      ∫ x in I, phi (annulusPoint x 0) * (chi (annulusPoint x 0) * b x) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by ring)
  rw [hpair, hpairB] at hg
  rw [hpairD]
  linarith

end PoincareConjecture

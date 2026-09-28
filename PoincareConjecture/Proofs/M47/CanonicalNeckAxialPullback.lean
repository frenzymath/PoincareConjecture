import PoincareConjecture.Proofs.M47.CanonicalNeckAxialCovariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

def neckAxialSpaceMap (lambda c : ℝ) (z : RoundCylinderSpace) : RoundCylinderSpace :=
  (z.1, lambda * z.2 + c)

theorem neckAxialSpaceMap_contMDiff (lambda c : ℝ) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (neckAxialSpaceMap lambda c) := by
  have h : ContDiff ℝ ∞ (fun s : ℝ => lambda * s + c) :=
    (contDiff_const.mul contDiff_id).add contDiff_const
  exact contMDiff_fst.prodMk (h.contMDiff.comp contMDiff_snd)

theorem neckAxialSpaceMap_mfderiv (lambda c : ℝ) (z : RoundCylinderSpace)
    (v : RoundCylinderTangent z) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (neckAxialSpaceMap lambda c) z v = neckAxialLinearMap lambda v := by
  have hs : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun q : RoundCylinderSpace => lambda * q.2 + c) z :=
    (mdifferentiableAt_const.mul mdifferentiableAt_snd).add mdifferentiableAt_const
  have hd : mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (fun q : RoundCylinderSpace => lambda * q.2 + c) z =
        lambda • mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd z := by
    change mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun q : RoundCylinderSpace => lambda * q.2 + c) z =
        lambda • mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) Prod.snd z
    have hmul : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (fun q : RoundCylinderSpace => lambda * q.2) z :=
      mdifferentiableAt_const.mul mdifferentiableAt_snd
    erw [mvfderiv_fun_add hmul mdifferentiableAt_const, mvfderiv_const, add_zero,
      mvfderiv_fun_mul mdifferentiableAt_const mdifferentiableAt_snd]
    simp only [mvfderiv_const, smul_zero, add_zero]
  erw [neckAxialSpaceMap, mfderiv_prodMk mdifferentiableAt_fst hs,
    hd, mfderiv_fst, mfderiv_snd]
  rfl

noncomputable def neckAxialTensorPullback (lambda c : ℝ) (B : RoundCylinderTwoTensor) :
    RoundCylinderTwoTensor := fun z v w =>
  B (neckAxialSpaceMap lambda c z) (neckAxialLinearMap lambda v) (neckAxialLinearMap lambda w)

theorem roundCylinderTensorCoefficient_neckAxialTensorPullback
    (lambda c : ℝ) (B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (q : UnitTwoSphere) (p : V) (a b : Fin 3) :
    roundCylinderTensorCoefficient
        (neckAxialTensorPullback lambda c (fun z v w => B z v w)) (chartAt E₂ q) p a b =
      neckAxialWeight lambda a * neckAxialWeight lambda b *
        roundCylinderTensorCoefficient (fun z v w => B z v w) (chartAt E₂ q)
          (neckAxialCoordinate lambda c p) a b := by
  let L := mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm p.1
  have hL (i : Fin 3) :
      neckAxialLinearMap lambda (L (roundCylinderCoordinateBasis i).1,
          (roundCylinderCoordinateBasis i).2) =
        neckAxialWeight lambda i •
          (L (roundCylinderCoordinateBasis i).1, (roundCylinderCoordinateBasis i).2) := by
    fin_cases i <;> simp [neckAxialLinearMap, neckAxialWeight, roundCylinderCoordinateBasis]
  change B ((chartAt E₂ q).symm p.1, lambda * p.2 + c)
      (neckAxialLinearMap lambda (L (roundCylinderCoordinateBasis a).1,
        (roundCylinderCoordinateBasis a).2))
      (neckAxialLinearMap lambda (L (roundCylinderCoordinateBasis b).1,
        (roundCylinderCoordinateBasis b).2)) = _
  rw [hL, hL]
  simp only [map_smul, smul_apply, smul_eq_mul]
  change _ = neckAxialWeight lambda a * neckAxialWeight lambda b *
    B ((chartAt E₂ q).symm p.1, lambda * p.2 + c)
      (L (roundCylinderCoordinateBasis a).1, (roundCylinderCoordinateBasis a).2)
      (L (roundCylinderCoordinateBasis b).1, (roundCylinderCoordinateBasis b).2)
  ring

theorem roundCylinderGram_neckAxialWeight (lambda c u : ℝ) (q : UnitTwoSphere)
    (p : V) (a b : Fin 3) :
    neckAxialWeight lambda a * neckAxialWeight lambda b *
        roundCylinderGram u (chartAt E₂ q) (neckAxialCoordinate lambda c p) a b -
      roundCylinderGram u (chartAt E₂ q) p a b =
        (lambda ^ 2 - 1) * (if a = 2 ∧ b = 2 then (1 : ℝ) else 0) := by
  rw [roundCylinderGram_chosenChart, roundCylinderGram_chosenChart]
  fin_cases a <;> fin_cases b <;>
    simp [neckAxialWeight, neckAxialCoordinate, Matrix.diagonal]
  ring

theorem roundCylinderIteratedDerivative_neckAxialTensorPullback_zero
    (lambda c u : ℝ) (B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (q : UnitTwoSphere) (p : V) (a : Fin 2 → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt E₂ q)
        (neckAxialTensorPullback lambda c (fun z v w => B z v w)) 0 p a =
      neckAxialTensorArray lambda c
        (roundCylinderIteratedDerivative u (chartAt E₂ q) (fun z v w => B z v w) 0) p a +
      (lambda ^ 2 - 1) * (if a 0 = 2 ∧ a 1 = 2 then (1 : ℝ) else 0) := by
  simp only [roundCylinderIteratedDerivative,
    roundCylinderTensorCoefficient_neckAxialTensorPullback, neckAxialTensorArray,
    Nat.add_zero, Fin.prod_univ_two]
  have h := roundCylinderGram_neckAxialWeight lambda c u q p (a 0) (a 1)
  nlinarith only [h]

end PoincareConjecture.Proofs.M47

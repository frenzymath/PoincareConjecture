import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingAffine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

open Proofs.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

theorem source_recent_translation_smooth {epsilon epsilon' c : ℝ}
    (hdom : ∀ r ∈ Ioo (-epsilon'⁻¹) epsilon'⁻¹,
      r + c ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : RoundCylinderTensorSmoothOn epsilon (fun z v w => B z v w)) :
    RoundCylinderTensorSmoothOn epsilon'
      (neckAxialTensorPullback 1 c (fun z v w => B z v w)) := by
  intro q a b
  have hA : ContDiff ℝ ∞ (neckAxialCoordinate 1 c) :=
    contDiff_fst.prodMk ((contDiff_const.mul contDiff_snd).add contDiff_const)
  have hmaps : MapsTo (neckAxialCoordinate 1 c)
      ((chartAt E₂ q).target ×ˢ Ioo (-epsilon'⁻¹) epsilon'⁻¹)
      ((chartAt E₂ q).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) := by
    intro p hp
    exact ⟨hp.1, by simpa only [neckAxialCoordinate, one_mul] using hdom p.2 hp.2⟩
  have hcomp := (hB q a b).comp hA.contDiffOn hmaps
  have hprod : ContDiffOn ℝ ∞ (fun p : V =>
      neckAxialWeight 1 a * neckAxialWeight 1 b *
        roundCylinderTensorCoefficient (fun z v w => B z v w) (chartAt E₂ q)
          (neckAxialCoordinate 1 c p) a b)
      ((chartAt E₂ q).target ×ˢ Ioo (-epsilon'⁻¹) epsilon'⁻¹) :=
    contDiffOn_const.mul hcomp
  exact hprod.congr fun p _ =>
    roundCylinderTensorCoefficient_neckAxialTensorPullback 1 c B q p a b

theorem source_recent_translation_coefficient_error_bound
    {epsilon epsilon' c K : ℝ}
    (hdom : ∀ r ∈ Icc (-epsilon'⁻¹) epsilon'⁻¹,
      r + c ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (B D : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (hB : RoundCylinderTensorSmoothOn epsilon (fun z v w => B z v w))
    (hD : RoundCylinderTensorSmoothOn epsilon (fun z v w => D z v w))
    (m : ℕ)
    (herror : ∀ q : UnitTwoSphere, ∀ r ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient (fun z v w => B z v w) (chartAt E₂ q) y a b -
          roundCylinderTensorCoefficient (fun z v w => D z v w) (chartAt E₂ q) y a b)
            (0, r)‖ ≤ K) :
    ∀ q : UnitTwoSphere, ∀ r ∈ Icc (-epsilon'⁻¹) epsilon'⁻¹,
      ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient
            (neckAxialTensorPullback 1 c (fun z v w => B z v w)) (chartAt E₂ q) y a b -
          roundCylinderTensorCoefficient
            (neckAxialTensorPullback 1 c (fun z v w => D z v w)) (chartAt E₂ q) y a b)
            (0, r)‖ ≤ K := by
  intro q r hr j hj a b
  let f : V → ℝ := fun y =>
    roundCylinderTensorCoefficient (fun z v w => B z v w) (chartAt E₂ q) y a b -
      roundCylinderTensorCoefficient (fun z v w => D z v w) (chartAt E₂ q) y a b
  have hpoint : neckAxialCoordinate 1 c (0, r) = (0, r + c) := by
    simp only [neckAxialCoordinate, one_mul]
  have hmem : (0, r + c) ∈ (chartAt E₂ q).target ×ˢ
      Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    refine ⟨?_, hdom r hr⟩
    rw [roundCylinder_sphereChart_target]
    trivial
  have hf : ContDiffAt ℝ ∞ f (neckAxialCoordinate 1 c (0, r)) := by
    rw [hpoint]
    exact ((hB q a b).contDiffAt
      (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hmem)).sub
      ((hD q a b).contDiffAt
        (((chartAt E₂ q).open_target.prod isOpen_Ioo).mem_nhds hmem))
  have hweight (i : Fin 3) : neckAxialWeight 1 i = 1 := by
    simp [neckAxialWeight]
  have heq : (fun y =>
      roundCylinderTensorCoefficient
        (neckAxialTensorPullback 1 c (fun z v w => B z v w)) (chartAt E₂ q) y a b -
      roundCylinderTensorCoefficient
        (neckAxialTensorPullback 1 c (fun z v w => D z v w)) (chartAt E₂ q) y a b) =
      (fun y => (1 : ℝ) * f (neckAxialCoordinate 1 c y)) := by
    funext y
    rw [roundCylinderTensorCoefficient_neckAxialTensorPullback,
      roundCylinderTensorCoefficient_neckAxialTensorPullback, hweight a, hweight b]
    simp only [one_mul, f]
  rw [heq]
  have h := source_neck_affine_weighted_jet_le (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    c 1 (by norm_num) f (0, r) j hf
  rw [hpoint] at h
  exact h.trans (herror q _ (hdom r hr) j hj a b)

end PoincareConjecture.M47

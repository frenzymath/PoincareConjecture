import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

open Proofs.M47 M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

theorem source_initial_translated_coefficient (k c : ℝ) (B : RoundCylinderTwoTensor)
    (theta : UnitTwoSphere) (a b : Fin 3) (p : V) :
    roundCylinderTensorCoefficient
        (fun z v w => k * neckAxialTensorPullback 1 c B z v w)
        (chartAt E₂ theta) p a b =
      k * roundCylinderTensorCoefficient B (chartAt E₂ theta) (p.1, p.2 + c) a b := by
  simp only [roundCylinderTensorCoefficient, neckAxialTensorPullback,
    neckAxialSpaceMap, neckAxialLinearMap]
  congr 2 <;> simp

theorem source_initial_translated_tensor_smooth
    {epsilon R c : ℝ} (k : ℝ) (B : RoundCylinderTwoTensor)
    (hB : ∀ (theta : UnitTwoSphere) (a b : Fin 3), ContDiffOn ℝ ∞
      (fun p : V => roundCylinderTensorCoefficient B (chartAt E₂ theta) p a b)
      ((chartAt E₂ theta).target ×ˢ Ioo (-R) R))
    (hband : ∀ r ∈ Ioo (-epsilon⁻¹) epsilon⁻¹, r + c ∈ Ioo (-R) R) :
    RoundCylinderTensorSmoothOn epsilon
      (fun z v w => k * neckAxialTensorPullback 1 c B z v w) := by
  intro theta a b
  have hshift : ContDiff ℝ ∞ (fun p : V => (p.1, p.2 + c)) :=
    contDiff_fst.prodMk (contDiff_snd.add contDiff_const)
  have hmap : MapsTo (fun p : V => (p.1, p.2 + c))
      ((chartAt E₂ theta).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)
      ((chartAt E₂ theta).target ×ˢ Ioo (-R) R) :=
    fun p hp => ⟨hp.1, hband p.2 hp.2⟩
  simpa only [source_initial_translated_coefficient] using
    (contDiffOn_const.mul ((hB theta a b).comp hshift.contDiffOn hmap) :
      ContDiffOn ℝ ∞ (fun p : V => k * roundCylinderTensorCoefficient B
        (chartAt E₂ theta) (p.1, p.2 + c) a b)
        ((chartAt E₂ theta).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹))

end PoincareConjecture.M47

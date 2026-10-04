import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Blowup.Controls.BlowupControlsSourceInitialNormalization

/-!
# True-domain smoothness of the translated old-neck tensor

The actual open old band is retained explicitly. The affine map changes
no horizontal chart and uses only the displayed translated heights.
Morgan--Tian Lemma 17.7, pp. 405-406; old-normalization G2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M47

open Proofs.M47 M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

/-- The full native coefficient is the old coefficient at its actual
translated point; both unit-slope tangent factors are retained. -/
theorem source_initial_translated_coefficient (k c : ℝ) (B : RoundCylinderTwoTensor)
    (theta : UnitTwoSphere) (a b : Fin 3) (p : V) :
    roundCylinderTensorCoefficient
        (fun z v w => k * neckAxialTensorPullback 1 c B z v w)
        (chartAt E₂ theta) p a b =
      k * roundCylinderTensorCoefficient B (chartAt E₂ theta) (p.1, p.2 + c) a b := by
  simp only [roundCylinderTensorCoefficient, neckAxialTensorPullback,
    neckAxialSpaceMap, neckAxialLinearMap]
  congr 2 <;> simp

/-- Smoothness uses precisely the old open band. No smoothness of
the added-past tensor outside its actual source is required. -/
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

end PoincareMT.M47

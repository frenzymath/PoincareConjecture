import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeLevel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLStripEmbedding

set_option autoImplicit false

open Set Geometry PLStrip

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def apexStripCoordinates (A : E →ᵃ[ℝ] ℝ)
    (v u w : E) (α β : ℝ) : (ℝ × ℝ) →ᴬ[ℝ] E :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (A.heightRay v w - A.heightRay v u) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight ((β - α) • A.heightRay v u)).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ (ℝ × ℝ) ((α - A v) • A.heightRay v u + v)

theorem apexStripCoordinates_apply (A : E →ᵃ[ℝ] ℝ) (v u w : E) (α β : ℝ) (q : ℝ × ℝ) :
    A.apexStripCoordinates v u w α β q =
      q.1 • (A.heightRay v w - A.heightRay v u) +
        (α - A v + (β - α) * q.2) • A.heightRay v u + v := by
  change q.1 • (A.heightRay v w - A.heightRay v u) +
    q.2 • ((β - α) • A.heightRay v u) + ((α - A v) • A.heightRay v u + v) = _
  module

theorem apply_apexStripCoordinates (A : E →ᵃ[ℝ] ℝ) {v u w : E}
    (hu : A u ≠ A v) (hw : A w ≠ A v) (α β : ℝ) (q : ℝ × ℝ) :
    A (A.apexStripCoordinates v u w α β q) = α + (β - α) * q.2 := by
  rw [apexStripCoordinates_apply]
  change A ((q.1 • (A.heightRay v w - A.heightRay v u) +
    (α - A v + (β - α) * q.2) • A.heightRay v u) +ᵥ v) = _
  rw [map_vadd, map_add, map_smul, map_sub, map_smul,
    linear_heightRay A hu, linear_heightRay A hw]
  change q.1 * (1 - 1) + (α - A v + (β - α) * q.2) * 1 + A v = _
  ring

theorem apexStripCoordinates_injective (A : E →ᵃ[ℝ] ℝ) {v u w : E}
    (hi : AffineIndependent ℝ ![v, u, w])
    (hu : A u ≠ A v) (hw : A w ≠ A v) {α β : ℝ} (hαβ : α ≠ β) :
    Function.Injective (A.apexStripCoordinates v u w α β) := by
  intro p q hpq
  have ht := congrArg A hpq
  rw [apply_apexStripCoordinates A hu hw, apply_apexStripCoordinates A hu hw] at ht
  have hts : p.2 = q.2 :=
    (mul_left_cancel₀ (sub_ne_zero.mpr hαβ.symm)) (add_left_cancel ht)
  rw [apexStripCoordinates_apply, apexStripCoordinates_apply, hts] at hpq
  have hd : A.heightRay v w - A.heightRay v u ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (A.heightRay_ne_of_affineIndependent hi hu))
  exact Prod.ext (smul_left_injective ℝ hd (add_right_cancel (add_right_cancel hpq))) hts

theorem apexStripCoordinates_left (A : E →ᵃ[ℝ] ℝ) (v u w : E) (α β t : ℝ) :
    A.apexStripCoordinates v u w α β (0, t) =
      A.edgeLevel v u (α + (β - α) * t) := by
  rw [apexStripCoordinates_apply, edgeLevel]
  simp only [zero_smul, zero_add]
  congr 2
  ring

theorem apexStripCoordinates_right (A : E →ᵃ[ℝ] ℝ) (v u w : E) (α β t : ℝ) :
    A.apexStripCoordinates v u w α β
        ((β - A v) * t + (α - A v) * (1 - t), t) =
      A.edgeLevel v w (α + (β - α) * t) := by
  rw [apexStripCoordinates_apply, edgeLevel]
  module

end AffineMap

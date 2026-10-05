import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.FinitePLStripEmbedding

/-!
# Reflecting a finite PL strip's height parameter

The affine reflection of the parameter square reverses its
vertical coordinate and exchanges its top and bottom. It
converts lower-apex strip constructions to upper-apex ones.
See Alexander 1924, pp. 6--8 and M76 derivation 160.
-/

set_option autoImplicit false

open Set Geometry

namespace PLStrip

/-- The height-reflecting homeomorphism of the unit square.
See M76 derivation 160. -/
def flipHeight : square ≃ₜ square where
  toFun p := ⟨((p : ℝ × ℝ).1, 1 - (p : ℝ × ℝ).2), p.property.1,
    by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩
  invFun p := ⟨((p : ℝ × ℝ).1, 1 - (p : ℝ × ℝ).2), p.property.1,
    by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩
  left_inv p := by
    apply Subtype.ext
    change ((p : ℝ × ℝ).1, 1 - (1 - (p : ℝ × ℝ).2)) = p
    simp
  right_inv p := by
    apply Subtype.ext
    change ((p : ℝ × ℝ).1, 1 - (1 - (p : ℝ × ℝ).2)) = p
    simp
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).prodMk
    (continuous_const.sub (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  continuous_invFun := ((continuous_fst.comp continuous_subtype_val).prodMk
    (continuous_const.sub (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- The square reflection is affine on an actual finite
triangulation of its whole domain. See M76 derivation 160. -/
theorem isFinitePL_flipHeight : flipHeight.IsFinitePL := by
  let X : (ℝ × ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let Y : (ℝ × ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  let C := ContinuousAffineMap.const ℝ (ℝ × ℝ) (1 : ℝ)
  obtain ⟨K, hK, hspace⟩ := exists_finite_triangulation_square
  exact ⟨X.prod (C - Y), ⟨K, hK, hspace, K.affineOnFaces_affine _⟩, fun _ => rfl⟩

end PLStrip

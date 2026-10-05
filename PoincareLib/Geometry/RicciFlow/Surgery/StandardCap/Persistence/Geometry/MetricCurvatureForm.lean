import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Geometry.SectionalPolarization

/-!
# The algebraic curvature form of a symmetric bilinear form

The Gram expression is a four-linear curvature form. Together with
orthonormal-plane polarization it identifies the curvature-one model
of Morgan--Tian, Definition 9.76; see M44 derivation 28.
-/

set_option autoImplicit false
-- The four-linear codomain requires nested module instances.
set_option maxSynthPendingDepth 8

namespace PoincareMT.M44

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The Gram curvature form associated with a bilinear form, with the
positive-sphere sign convention of Morgan--Tian pp. 5-7. -/
def metricCurvatureForm (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] E →ₗ[ℝ] ℝ where
  toFun a :=
    { toFun := fun b =>
        { toFun := fun c => (B a c) • B b - (B b c) • B a
          map_add' := by
            intro c d
            ext z
            simp only [map_add, LinearMap.sub_apply, LinearMap.smul_apply,
              LinearMap.add_apply, smul_eq_mul]
            ring
          map_smul' := by
            intro r c
            ext z
            simp only [map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
              smul_eq_mul, RingHom.id_apply]
            ring }
      map_add' := by
        intro b c
        ext d z
        simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
        ring
      map_smul' := by
        intro r b
        ext d z
        simp only [map_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
          LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' := by
    intro a b
    ext c d z
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    ring
  map_smul' := by
    intro r a
    ext b c d
    simp only [map_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Evaluation of the Gram curvature form. Source: Morgan--Tian pp. 5-7. -/
theorem metricCurvatureForm_apply (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a b c d : E) :
    metricCurvatureForm B a b c d = B a c * B b d - B b c * B a d := rfl

end PoincareMT.M44

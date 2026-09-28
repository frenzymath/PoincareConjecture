import PoincareConjecture.Proofs.M44.Mathlib.SectionalPolarization









set_option autoImplicit false

set_option maxSynthPendingDepth 8

namespace PoincareConjecture.M44

variable {E : Type*} [AddCommGroup E] [Module ℝ E]



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


theorem metricCurvatureForm_apply (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (a b c d : E) :
    metricCurvatureForm B a b c d = B a c * B b d - B b c * B a d := rfl

end PoincareConjecture.M44

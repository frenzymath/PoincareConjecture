import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereRegionChart
import Mathlib.Geometry.Manifold.Diffeomorph










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]



noncomputable def normPreservingSphereDiffeomorph
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hF : ∀ y, ‖F y‖ = ‖y‖) :
    Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : E) 1) (sphere (0 : E) 1) ∞ where
  toEquiv := (normPreservingSphereHomeomorph F.toHomeomorph hF).toEquiv
  contMDiff_toFun := (F.contMDiff_toFun.comp
    (contMDiff_coe_sphere (E := E) (n := n))).codRestrict_sphere _
  contMDiff_invFun := (F.contMDiff_invFun.comp
    (contMDiff_coe_sphere (E := E) (n := n))).codRestrict_sphere _

omit [FiniteDimensional ℝ E] in

@[simp] theorem normPreservingSphereDiffeomorph_apply
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hF : ∀ y, ‖F y‖ = ‖y‖)
    (q : sphere (0 : E) 1) :
    (normPreservingSphereDiffeomorph (n := n) F hF q : E) = F q := rfl

omit [FiniteDimensional ℝ E] in

@[simp] theorem normPreservingSphereDiffeomorph_symm_apply
    (F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (hF : ∀ y, ‖F y‖ = ‖y‖)
    (q : sphere (0 : E) 1) :
    ((normPreservingSphereDiffeomorph (n := n) F hF).symm q : E) = F.symm q := rfl

end PoincareConjecture.M25.Topology3D

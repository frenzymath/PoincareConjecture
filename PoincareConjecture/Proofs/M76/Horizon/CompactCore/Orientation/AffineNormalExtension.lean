import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.BoundarySign
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private def affineHeightVector (ell : E →ᴬ[ℝ] ℝ) (n : E) : E →ᴬ[ℝ] E :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight n).toContinuousAffineMap.comp ell

private theorem affineHeightVector_apply (ell : E →ᴬ[ℝ] ℝ) (n x : E) :
    affineHeightVector ell n x = ell x • n := rfl

def affineNormalExtension (ell : E →ᴬ[ℝ] ℝ) (n n' : E)
    (B : E →ᴬ[ℝ] E) : E →ᴬ[ℝ] E :=
  B.comp (ContinuousAffineMap.id ℝ E - affineHeightVector ell n) +
    affineHeightVector ell n'

theorem affineNormalExtension_apply (ell : E →ᴬ[ℝ] ℝ) (n n' : E)
    (B : E →ᴬ[ℝ] E) (x : E) :
    affineNormalExtension ell n n' B x = B (x - ell x • n) + ell x • n' := rfl

theorem affine_normal_projection_height (ell : E →ᴬ[ℝ] ℝ) (n : E)
    (hn : ell.contLinear n = 1) (x : E) : ell (x - ell x • n) = 0 := by
  have h := ell.map_vadd x (-ell x • n)
  simp only [vadd_eq_add, map_smul, hn, smul_eq_mul, mul_one] at h
  convert h using 1 <;> simp [sub_eq_add_neg, add_comm]

theorem affineNormalExtension_height (ell m : E →ᴬ[ℝ] ℝ) (n n' : E)
    (B : E →ᴬ[ℝ] E) (hn : ell.contLinear n = 1) (hn' : m.contLinear n' = 1)
    (hB : ∀ x, ell x = 0 → m (B x) = 0) (x : E) :
    m (affineNormalExtension ell n n' B x) = ell x := by
  rw [affineNormalExtension_apply, add_comm, ← vadd_eq_add, m.map_vadd]
  simp [map_smul, hn', hB _ (affine_normal_projection_height ell n hn x)]

theorem affineNormalExtension_eq_on_plane (ell : E →ᴬ[ℝ] ℝ) (n n' : E)
    (B : E →ᴬ[ℝ] E) {x : E} (hx : ell x = 0) :
    affineNormalExtension ell n n' B x = B x := by
  simp [affineNormalExtension_apply, hx]

theorem affineNormalExtension_contLinear_normal (ell : E →ᴬ[ℝ] ℝ) (n n' : E)
    (B : E →ᴬ[ℝ] E) (hn : ell.contLinear n = 1) :
    (affineNormalExtension ell n n' B).contLinear n = n' := by
  simp only [affineNormalExtension, affineHeightVector, ContinuousAffineMap.add_contLinear,
    ContinuousAffineMap.comp_contLinear, ContinuousAffineMap.sub_contLinear,
    ContinuousLinearMap.toContinuousAffineMap_contLinear,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, hn, one_smul]
  change B.contLinear (n - n) + n' = n'
  simp

theorem affineNormalExtension_boundary_det (b : Module.Basis (Fin 3) ℝ E)
    (ell : E →ᴬ[ℝ] ℝ) (n n' : E) (B : E →ᴬ[ℝ] E)
    (hn : ell.contLinear n = 1) (p : Fin 3 → E) (hp : ∀ i, ell (p i) = 0) :
    b.det ![B (p 1) - B (p 0), B (p 2) - B (p 0), n'] =
      LinearMap.det (affineNormalExtension ell n n' B).toAffineMap.linear *
        b.det ![p 1 - p 0, p 2 - p 0, n] := by
  let F := affineNormalExtension ell n n' B
  have htan (i : Fin 3) : F.toAffineMap.linear (p i - p 0) = B (p i) - B (p 0) := by
    change F.contLinear (p i -ᵥ p 0) = _
    rw [F.contLinear_map_vsub]
    change F (p i) - F (p 0) = _
    rw [affineNormalExtension_eq_on_plane ell n n' B (hp i),
      affineNormalExtension_eq_on_plane ell n n' B (hp 0)]
  have hnormal : F.toAffineMap.linear n = n' :=
    affineNormalExtension_contLinear_normal ell n n' B hn
  have hv : F.toAffineMap.linear ∘ ![p 1 - p 0, p 2 - p 0, n] =
      ![B (p 1) - B (p 0), B (p 2) - B (p 0), n'] := by
    funext i
    fin_cases i <;> simp [htan, hnormal]
  rw [← hv, b.det_comp]

theorem exists_affine_normal_extension (ell m : E →ᴬ[ℝ] ℝ) (n n' : E)
    (B : E →ᴬ[ℝ] E) (hn : ell.contLinear n = 1) (hn' : m.contLinear n' = 1)
    (hB : ∀ x, ell x = 0 → m (B x) = 0)
    (hi : InjOn B {x | ell x = 0}) :
    ∃ A : E ≃ᴬ[ℝ] E,
      (∀ x, A x = B (x - ell x • n) + ell x • n') ∧
      (∀ x, m (A x) = ell x) ∧
      (∀ x, ell x = 0 → A x = B x) := by
  let F := affineNormalExtension ell n n' B
  have hF (x : E) : m (F x) = ell x :=
    affineNormalExtension_height ell m n n' B hn hn' hB x
  have hFi : Function.Injective F := by
    intro x y hxy
    have hh : ell x = ell y := (hF x).symm.trans ((congrArg m hxy).trans (hF y))
    change B (x - ell x • n) + ell x • n' = B (y - ell y • n) + ell y • n' at hxy
    rw [hh, add_left_inj] at hxy
    have hp := hi (affine_normal_projection_height ell n hn x)
      (affine_normal_projection_height ell n hn y) (by simpa only [hh] using hxy)
    rw [hh, sub_left_inj] at hp
    exact hp
  have hFs : Function.Surjective F := F.toAffineMap.linear_surjective_iff.mp
    (LinearMap.surjective_of_injective (F.toAffineMap.linear_injective_iff.mpr hFi))
  let e := AffineEquiv.ofBijective (φ := F.toAffineMap) ⟨hFi, hFs⟩
  let A : E ≃ᴬ[ℝ] E :=
    { e with
      continuous_toFun := F.continuous
      continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional }
  refine ⟨A, fun _ => rfl, hF, ?_⟩
  exact fun x hx => affineNormalExtension_eq_on_plane ell n n' B hx

end Geometry

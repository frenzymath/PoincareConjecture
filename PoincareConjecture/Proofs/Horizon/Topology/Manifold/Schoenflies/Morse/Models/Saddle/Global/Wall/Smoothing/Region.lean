import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Order.DenselyOrdered

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing

private abbrev E3 := EuclideanSpace Real (Fin 3)

variable (h : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞)
    (x : Real → Real)

def cornerShear (hx : ContDiff Real ∞ x) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun p := p + x (h.symm (p 2 - (p 1)^2)) • EuclideanSpace.single 0 1
  invFun p := p - x (h.symm (p 2 - (p 1)^2)) • EuclideanSpace.single 0 1
  left_inv p := by
    ext i
    simp
  right_inv p := by
    ext i
    simp
  contMDiff_toFun := (contDiff_id.add
    ((hx.comp (h.symm.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff.sub
        ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff.pow 2)))).smul
      contDiff_const)).contMDiff
  contMDiff_invFun := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p : E3 =>
      p - x (h.symm (p 2 - (p 1)^2)) • EuclideanSpace.single 0 1)
    exact (contDiff_id.sub
      ((hx.comp (h.symm.contDiff.comp
        ((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff.sub
          ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff.pow 2)))).smul
        contDiff_const)).contMDiff

variable (hx : ContDiff Real ∞ x)

theorem cornerShear_apply (p : E3) :
    cornerShear h x hx p =
      p + x (h.symm (p 2 - (p 1)^2)) • EuclideanSpace.single 0 1 := rfl

theorem cornerShear_symm_apply (p : E3) :
    (cornerShear h x hx).symm p =
      p - x (h.symm (p 2 - (p 1)^2)) • EuclideanSpace.single 0 1 := rfl

@[simp] theorem cornerShear_zero (p : E3) :
    cornerShear h x hx p 0 = p 0 + x (h.symm (p 2 - (p 1)^2)) := by
  rw [cornerShear_apply]
  simp

@[simp] theorem cornerShear_one (p : E3) : cornerShear h x hx p 1 = p 1 := by
  rw [cornerShear_apply]
  simp

@[simp] theorem cornerShear_two (p : E3) : cornerShear h x hx p 2 = p 2 := by
  rw [cornerShear_apply]
  simp

@[simp] theorem cornerShear_symm_zero (p : E3) :
    (cornerShear h x hx).symm p 0 = p 0 - x (h.symm (p 2 - (p 1)^2)) := by
  rw [cornerShear_symm_apply]
  simp

@[simp] theorem cornerShear_symm_one (p : E3) :
    (cornerShear h x hx).symm p 1 = p 1 := by
  rw [cornerShear_symm_apply]
  simp

@[simp] theorem cornerShear_symm_two (p : E3) :
    (cornerShear h x hx).symm p 2 = p 2 := by
  rw [cornerShear_symm_apply]
  simp

def roundedRegion : Set E3 := {p | p 0 ≤ x (h.symm (p 2 - (p 1)^2))}

def roundedGraph : Set E3 := {p | p 0 = x (h.symm (p 2 - (p 1)^2))}

theorem cornerShear_image_halfspace :
    cornerShear h x hx '' {p : E3 | p 0 ≤ 0} = roundedRegion h x := by
  rw [Diffeomorph.image_eq_preimage_symm]
  ext p
  simp [roundedRegion]

theorem cornerShear_image_wall :
    cornerShear h x hx '' {p : E3 | p 0 = 0} = roundedGraph h x := by
  rw [Diffeomorph.image_eq_preimage_symm]
  ext p
  simp [roundedGraph, sub_eq_zero]

theorem frontier_halfspace :
    frontier {p : E3 | p 0 ≤ 0} = {p : E3 | p 0 = 0} := by
  let L := EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)
  have hopen : IsOpenMap L := L.isOpenMap (by
    intro s
    exact ⟨EuclideanSpace.single 0 s, by simp [L]⟩)
  change frontier (L ⁻¹' Iic 0) = L ⁻¹' {0}
  simpa only [frontier_Iic] using
    (hopen.preimage_frontier_eq_frontier_preimage L.continuous (Iic 0)).symm

theorem frontier_roundedRegion (hx : ContDiff Real ∞ x) :
    frontier (roundedRegion h x) = roundedGraph h x := by
  rw [← cornerShear_image_halfspace h x hx]
  change frontier ((cornerShear h x hx).toHomeomorph '' {p : E3 | p 0 ≤ 0}) = _
  rw [← (cornerShear h x hx).toHomeomorph.image_frontier, frontier_halfspace]
  exact cornerShear_image_wall h x hx

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing

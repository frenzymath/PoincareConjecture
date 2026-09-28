import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.FilledModel.Scaled
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.Filling.ProfileImage
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CappedCylinder



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Pointwise

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)



theorem exists_ambient_filling_of_quadraticMinimum_and_cap
    {v : E3} (hv : ‖v‖ = 1) (c : Real) {r b s : Real}
    (hr : 0 < r) (hb : c + 2 * r ^ 2 < b) (hs : 0 < s)
    (B : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 = sphere (0 : Hemisphere.Plane v) r) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 = quadraticMinimumCap v c r ∪
        (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
          (Icc (c + (7 * r / 8) ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) r) ∪
        liftPlaneDiffeomorph hv b s hs.ne' B '' boundedCylinderNorthernCap v := by
  obtain ⟨A, hA, F, hF⟩ := exists_ambient_scaled_quadraticMinimum_model hv c hr hb hs
  have hAsphere : A '' sphere (0 : Hemisphere.Plane v) 1 = sphere (0 : Hemisphere.Plane v) r := by
    have he : (A : Hemisphere.Plane v → Hemisphere.Plane v) = fun x => r • x := funext hA
    rw [he]
    change r • sphere (0 : Hemisphere.Plane v) 1 = _
    rw [smul_sphere' hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  obtain ⟨γ, hγ, hAγ⟩ := exists_smooth_circle_parametrization_of_plane_filling hv A
  have hγrange : range γ = sphere (0 : Hemisphere.Plane v) r := hAγ.symm.trans hAsphere
  have hBγ : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ := hB.trans hγrange.symm
  have hab : c + (7 * r / 8) ^ 2 < b := by nlinarith [sq_nonneg r]
  obtain ⟨D, hDlow, hDcylinder, hDcap⟩ := exists_complete_upper_cap_alignment
    hv γ hγ A B hAγ hBγ hab hs
  let Q := quadraticMinimumCap v c r
  let C := (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
    (Icc (c + (7 * r / 8) ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) r)
  let U := liftPlaneDiffeomorph hv b s hs.ne' B '' boundedCylinderNorthernCap v
  have hDQ : D '' Q = Q := by
    suffices he : EqOn D id Q by simpa only [image_id] using image_congr he
    intro y hy
    exact hDlow y (quadraticMinimumCap_height_le hv c hr hy)
  have hDC : D '' C = C := by
    suffices he : EqOn D id C by simpa only [image_id] using image_congr he
    rintro y ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩
    have hqγ : q ∈ range γ := by rw [hγrange]; exact hq
    obtain ⟨p, rfl⟩ := hqγ
    exact hDcylinder t p
  refine ⟨F.trans D.symm, ?_⟩
  apply D.injective.image_injective
  change D '' ((D.symm ∘ F) '' sphere (0 : E3) 1) = D '' (Q ∪ C ∪ U)
  rw [image_comp, image_image]
  simp only [D.apply_symm_apply, image_id']
  rw [image_union, image_union, hDQ, hDC, hDcap]
  exact hF

end Poincare.Manifold.Schoenflies

import PoincareLib.Topology.Homotopy.LoopSpace.Contraction.Extension
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops

/-!
# A regular neighborhood of a null loop's boundary

Morgan-Tian Definition 18.17, printed p. 430. A continuous disk extension
can be precomposed with a radial clamp which fixes the unit circle and
maps the region outside the half disk to that circle. The resulting map
is continuous everywhere and agrees with the C1 radial loop extension
outside the half disk. Subsequent smoothing can be supported in the
interior without changing the prescribed boundary.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

open Proofs.M58

/-- A radial clamp that fixes the circle and is nonsingular at zero.
Source: MT Definition 18.17, p. 430, relative disk-smoothing derivation. -/
noncomputable def m60DiskRadialClamp (z : LoopPlane) : LoopPlane :=
  (max (1 / 2 : ℝ) ‖z‖)⁻¹ • z

/-- The radial clamp is continuous on the entire plane.
Source: MT Definition 18.17, p. 430, relative disk-smoothing derivation. -/
theorem m60DiskRadialClamp_continuous : Continuous m60DiskRadialClamp :=
  ((continuous_const.max continuous_norm).inv₀
    (fun z => ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left (1 / 2 : ℝ) ‖z‖)))).smul
    continuous_id

/-- Outside the half disk the clamp is radial normalization.
Source: MT Definition 18.17, p. 430, relative disk-smoothing derivation. -/
theorem m60DiskRadialClamp_eq_radial {z : LoopPlane} (hz : 1 / 2 ≤ ‖z‖) :
    m60DiskRadialClamp z = radialNormalization z := by
  simp only [m60DiskRadialClamp, max_eq_right hz, radialNormalization]

/-- Every null loop has a continuous extension which is already C1
outside the half disk and retains the exact boundary parameter.
Source: MT Definition 18.17, p. 430, relative disk-smoothing derivation. -/
theorem m60_exists_boundary_regular_extension
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (γ : C1FreeLoopSpace (M := M)) (hnull : IsNullHomotopicLoop γ) :
    ∃ F : LoopPlane → M, Continuous F ∧
      (∀ z : LoopCircle, F z.val = γ z) ∧
      ∀ z : LoopPlane, 1 / 2 < ‖z‖ → ContMDiffAt (𝓡 2) (𝓡 3) 1 F z := by
  obtain ⟨e, he, hboundary⟩ := hnull
  refine ⟨e ∘ m60DiskRadialClamp, he.comp m60DiskRadialClamp_continuous, ?_, ?_⟩
  · intro z
    dsimp only [Function.comp_def]
    rw [m60DiskRadialClamp_eq_radial (by rw [z.property]; norm_num),
      radialNormalization_of_norm_eq_one z.property, hboundary]
  · intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      simp only [h, norm_zero] at hz
      norm_num at hz
    apply (contMDiffAt_radial_extension γ hz0).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := by
      intro h
      simp only [h, norm_zero] at hw
      norm_num at hw
    change e (m60DiskRadialClamp w) = γ.extension (radialNormalization w)
    rw [m60DiskRadialClamp_eq_radial hw.le]
    let q : LoopCircle := ⟨radialNormalization w, norm_radialNormalization hw0⟩
    exact (hboundary q).trans (γ.boundary q).symm

end PoincareMT

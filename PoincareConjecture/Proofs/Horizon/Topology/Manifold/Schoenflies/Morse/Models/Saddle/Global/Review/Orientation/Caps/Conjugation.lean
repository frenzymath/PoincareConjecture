import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Transport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.TerminalInputs

noncomputable section
set_option autoImplicit false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Caps

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem reflected_lift
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y) (y : E3) :
    ((Rz.trans H).trans Rz) y =
      planarHeightMap (reflectedPlanarFamily Φ) (χ (-y 2)) y := by
  change Rz (H (Rz y)) = _
  rw [hH, Rz_two]
  have h := reflectedPlanarHeightMap Φ (χ (-y 2)) (Rz y)
  simpa only [Rz_involutive] using h.symm

theorem conjugate_replacement
    (H F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (C D : Fin 3 → Set E3) (W : Set E3)
    (hfix : EqOn F id (Rz '' W))
    (hcap : ∀ i, F '' (((Rz.trans H).trans Rz) '' (Rz '' C i)) = Rz '' D i) :
    ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      EqOn G id W ∧ ∀ i, G '' (H '' C i) = D i := by
  refine ⟨(Rz.trans F).trans Rz, ?_, ?_⟩
  · intro y hy
    change Rz (F (Rz y)) = y
    rw [hfix (mem_image_of_mem Rz hy)]
    exact Rz_involutive y
  · intro i
    have hinner : ((Rz.trans H).trans Rz) '' (Rz '' C i) = Rz '' (H '' C i) := by
      simp only [image_image, Diffeomorph.coe_trans, comp_apply, Rz_involutive]
    have h := congrArg (fun S : Set E3 => Rz '' S) (hcap i)
    rw [hinner] at h
    simpa only [image_image, Diffeomorph.coe_trans, comp_apply, Rz_involutive,
      image_id'] using h

theorem exists_reflected_path
    {f : S2 → E3} (M : SphereMorseReduction f) {g : S2 → E3}
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (R : SphereMorseReduction M.reflectedOriginal) (hv : R.v = M.v)
    (hinit : ∀ q, R.D (M.reflectedOriginal q) =
      Poincare.Geometry.Euclidean.heightReflection
        (mem_sphere_zero_iff_norm.mp M.v.property) (M.D (f q))) :
    ∃ Q : SphereSurgeryPath (R.v : E3) (fun q => R.D (M.reflectedOriginal q))
      (Poincare.Geometry.Euclidean.heightReflection
        (mem_sphere_zero_iff_norm.mp M.v.property) ∘ g), Q.core = P.core := by
  rw [hv, funext hinit]
  exact ⟨P.reflected (mem_sphere_zero_iff_norm.mp M.v.property),
    P.reflected_core (mem_sphere_zero_iff_norm.mp M.v.property)⟩

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Caps

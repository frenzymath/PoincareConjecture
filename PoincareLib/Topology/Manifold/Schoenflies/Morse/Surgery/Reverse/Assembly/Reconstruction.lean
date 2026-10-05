import PoincareLib.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Explicit
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Innermost
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Transport.Plus
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Transport.Minus

/-! # Ambient ball reconstruction under reversal of sphere surgery

Replace the innermost supplied child ball by an explicit thin lens, preserving
the surgery annulus and the other child. Stretch the other child's cap across
that annulus to obtain exactly the same sphere, then undo both ambient maps
and the original straightening. This is the reverse-surgery step in Hatcher,
*Notes on Basic 3-Manifold Topology* (2014), Theorem 1.1, pp. 4-5.
-/

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem ambient_ball_of_matching_prepared_range
    {f g : S2 → E3} (D F H B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range g)
    (hmatch : F '' range (fun p => D (f p)) = H '' range g) :
    ∃ B' : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      B' '' sphere (0 : E3) 1 = range f := by
  refine ⟨((B.trans H).trans F.symm).trans D.symm, ?_⟩
  calc
    _ = D.symm '' (F.symm '' (H '' (B '' sphere (0 : E3) 1))) := by
      rw [image_image, image_image, image_image]
      rfl
    _ = D.symm '' (F.symm '' (F '' range (fun p => D (f p)))) := by
      rw [hB, ← hmatch]
    _ = range f := by
      simp only [Diffeomorph.symm_apply_apply, ← range_comp, Function.comp_def]

/-- If both children of a regular sphere surgery have ambient ball fillings,
then so does the original sphere, with exact equality of the entire boundary. -/
theorem SphereSurgeryStep.exists_ambient_ball_of_children
    {f : sphere (0 : EuclideanSpace Real (Fin 3)) 1 →
      EuclideanSpace Real (Fin 3)}
    {v : EuclideanSpace Real (Fin 3)} {c R : Real}
    (S : SphereSurgeryStep f v c R)
    (Bminus Bplus : Diffeomorph (𝓡 3) (𝓡 3)
      (EuclideanSpace Real (Fin 3)) (EuclideanSpace Real (Fin 3)) ∞)
    (hminus : Bminus '' sphere (0 : EuclideanSpace Real (Fin 3)) 1 =
      range S.fMinus)
    (hplus : Bplus '' sphere (0 : EuclideanSpace Real (Fin 3)) 1 =
      range S.fPlus) :
    ∃ B : Diffeomorph (𝓡 3) (𝓡 3)
        (EuclideanSpace Real (Fin 3)) (EuclideanSpace Real (Fin 3)) ∞,
      B '' sphere (0 : EuclideanSpace Real (Fin 3)) 1 = range f := by
  rcases S.child_filling_avoids_other_boundary_or Bminus Bplus hminus hplus with hm | hp
  · obtain ⟨u, hu, hus, F, hF⟩ := S.exists_explicit_lower_replacement Bminus hminus hm
    obtain ⟨_, _, _, H, _, _, hH⟩ := S.exists_capPlus_transport_across hu hus.le
    exact ambient_ball_of_matching_prepared_range S.D F H Bplus hplus (hF.trans hH.symm)
  · obtain ⟨u, hu, hus, F, hF⟩ := S.exists_explicit_upper_replacement Bplus hplus hp
    obtain ⟨_, _, _, H, _, _, hH⟩ := S.exists_capMinus_transport_across hu hus.le
    apply ambient_ball_of_matching_prepared_range S.D F H Bminus hminus
    rw [hF, hH]
    ac_rfl

end Poincare.Manifold.Schoenflies

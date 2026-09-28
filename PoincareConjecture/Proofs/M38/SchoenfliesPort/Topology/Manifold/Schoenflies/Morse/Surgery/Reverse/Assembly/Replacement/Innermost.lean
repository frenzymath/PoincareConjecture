import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Reconstruction







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryStep

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem child_filling_avoids_other_boundary_or
    {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)
    (Bminus Bplus : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hminus : Bminus '' sphere (0 : E3) 1 = range S.fMinus)
    (hplus : Bplus '' sphere (0 : E3) 1 = range S.fPlus) :
    Disjoint (Bminus '' closedBall (0 : E3) 1) (range S.fPlus) ∨
      Disjoint (Bplus '' closedBall (0 : E3) 1) (range S.fMinus) := by
  have hballSphere (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
      Disjoint (B '' ball (0 : E3) 1) (B '' sphere (0 : E3) 1) := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, he⟩
    have he' := B.injective he
    subst z
    exact (ne_of_lt (mem_ball_zero_iff.mp hx)) (mem_sphere_zero_iff_norm.mp hz)
  rw [← hminus, ← hplus]
  rcases S.child_fillings_disjoint_or_nested Bminus Bplus hminus hplus with hd | hm | hp
  · exact Or.inl (hd.mono_right (image_mono sphere_subset_closedBall))
  · exact Or.inl ((hballSphere Bplus).mono_left hm)
  · exact Or.inr ((hballSphere Bminus).mono_left hp)

end Poincare.Manifold.Schoenflies.SphereSurgeryStep

end M38Schoenflies

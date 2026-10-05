import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.WhiskeredLoopSplit

/-!
# Marked loop classes under a stage projection

A continuous projection and the original basepoint path give a genuine
homomorphism on fundamental groups. Its subgroup preimage lets surgeries
in the pulled-back mark retain exclusion in the original marked space.
-/

set_option autoImplicit false

namespace PoincareMT.M76.Dehn

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Project loops and return to the original basepoint using its actual
path to the image of the source basepoint. -/
noncomputable def markedProjectionHom (f : C(X, Y)) {x : X} {b : Y}
    (q : Path b (f x)) : FundamentalGroup X x →* FundamentalGroup Y b :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath q.symm).toMonoidHom.comp
    (FundamentalGroup.map f x)

/-- The homomorphism uses the literal projected path and the original
basepoint path, with Mathlib's fundamental-group multiplication order. -/
theorem markedProjectionHom_loop (f : C(X, Y)) {x : X} {b : Y}
    (q : Path b (f x)) (l : Path x x) :
    markedProjectionHom f q (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk l)) =
      q.whiskeredLoopClass (l.map f.continuous) := by
  change (Path.Homotopic.Quotient.mk q.symm.symm).trans
      ((Path.Homotopic.Quotient.mk (l.map f.continuous)).trans
        (Path.Homotopic.Quotient.mk q.symm)) = _
  simp only [Path.symm_symm, Path.whiskeredLoopClass,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

/-- Projecting an arbitrary whiskered loop appends the projected whisker
to the original basepoint path. -/
theorem markedProjectionHom_whiskered (f : C(X, Y)) {x z : X} {b : Y}
    (q : Path b (f x)) (p : Path x z) (l : Path z z) :
    markedProjectionHom f q (p.whiskeredLoopClass l) =
      (q.trans (p.map f.continuous)).whiskeredLoopClass (l.map f.continuous) := by
  rw [Path.whiskeredLoopClass, markedProjectionHom_loop]
  simp only [Path.map_trans, ← Path.map_symm, Path.whiskeredLoopClass,
    Path.trans_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.trans_assoc]

/-- At the literal rim basepoint the initial lower whisker is constant. -/
theorem markedProjectionHom_refl_whiskered (f : C(X, Y)) {x : X} {b : Y}
    (q : Path b (f x)) (l : Path x x) :
    markedProjectionHom f q ((Path.refl x).whiskeredLoopClass l) =
      q.whiskeredLoopClass (l.map f.continuous) := by
  have heq : (Path.refl x).whiskeredLoopClass l =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk l) := by
    change ((Path.Homotopic.Quotient.refl x).trans (Path.Homotopic.Quotient.mk l)).trans
      (Path.Homotopic.Quotient.refl x) = _
    rw [Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl]
  rw [heq, markedProjectionHom_loop]

/-- Changing only the written endpoint of the rim and its whisker does
not change the actual based loop class. -/
theorem whiskeredLoopClass_cast_rim {b x y : Y} (h : x = y)
    (q : Path b y) (l : Path y y) :
    (q.cast rfl h).whiskeredLoopClass (l.cast h h) = q.whiskeredLoopClass l := by
  cases h
  rfl

end PoincareMT.M76.Dehn

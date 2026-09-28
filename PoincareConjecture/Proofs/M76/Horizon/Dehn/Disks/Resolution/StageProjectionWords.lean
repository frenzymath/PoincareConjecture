import PoincareConjecture.Proofs.M76.Dehn.Mathlib.WhiskeredLoopSplit

set_option autoImplicit false

namespace PoincareConjecture.M76.Dehn

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def markedProjectionHom (f : C(X, Y)) {x : X} {b : Y}
    (q : Path b (f x)) : FundamentalGroup X x →* FundamentalGroup Y b :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath q.symm).toMonoidHom.comp
    (FundamentalGroup.map f x)

theorem markedProjectionHom_loop (f : C(X, Y)) {x : X} {b : Y}
    (q : Path b (f x)) (l : Path x x) :
    markedProjectionHom f q (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk l)) =
      q.whiskeredLoopClass (l.map f.continuous) := by
  change (Path.Homotopic.Quotient.mk q.symm.symm).trans
      ((Path.Homotopic.Quotient.mk (l.map f.continuous)).trans
        (Path.Homotopic.Quotient.mk q.symm)) = _
  simp only [Path.symm_symm, Path.whiskeredLoopClass,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

theorem markedProjectionHom_whiskered (f : C(X, Y)) {x z : X} {b : Y}
    (q : Path b (f x)) (p : Path x z) (l : Path z z) :
    markedProjectionHom f q (p.whiskeredLoopClass l) =
      (q.trans (p.map f.continuous)).whiskeredLoopClass (l.map f.continuous) := by
  rw [Path.whiskeredLoopClass, markedProjectionHom_loop]
  simp only [Path.map_trans, ← Path.map_symm, Path.whiskeredLoopClass,
    Path.trans_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.trans_assoc]

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

theorem whiskeredLoopClass_cast_rim {b x y : Y} (h : x = y)
    (q : Path b y) (l : Path y y) :
    (q.cast rfl h).whiskeredLoopClass (l.cast h h) = q.whiskeredLoopClass l := by
  cases h
  rfl

end PoincareConjecture.M76.Dehn

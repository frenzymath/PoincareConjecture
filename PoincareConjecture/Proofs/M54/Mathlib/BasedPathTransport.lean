import PoincareConjecture.Proofs.M54.Mathlib.LocalPathTransport

set_option autoImplicit false

open Set
open scoped unitInterval

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X]

def toPath (p : C(unitInterval, X)) : Path (p 0) (p 1) where
  toContinuousMap := p
  source' := rfl
  target' := rfl

end ContinuousMap

namespace Path.Homotopic.Quotient

variable {X : Type*} [TopologicalSpace X] (b : X)
    (tails : ∀ x : X, Joined b x → Path.Homotopic.Quotient b x)

noncomputable def basedTransport {x y : X} (p : Path.Homotopic.Quotient x y) :
    (FundamentalGroup X b)ᵐᵒᵖ := by
  classical
  exact if hx : Joined b x then
    MulOpposite.op ((tails x hx).trans (p.trans (tails y (hx.trans ⟨p.out⟩)).symm))
  else 1

theorem basedTransport_of_joined {x y : X} (p : Path.Homotopic.Quotient x y)
    (hx : Joined b x) (hy : Joined b y) :
    basedTransport b tails p =
      MulOpposite.op ((tails x hx).trans (p.trans (tails y hy).symm)) := by
  simp only [basedTransport, dif_pos hx]

theorem basedTransport_of_not_joined {x y : X} (p : Path.Homotopic.Quotient x y)
    (hx : ¬ Joined b x) : basedTransport b tails p = 1 := by
  simp only [basedTransport, dif_neg hx]

@[simp] theorem basedTransport_cast {x y x' y' : X}
    (p : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y) :
    basedTransport b tails (p.cast hx hy) = basedTransport b tails p := by
  subst x'
  subst y'
  rw [cast_rfl_rfl]

@[simp] theorem basedTransport_refl (x : X) :
    basedTransport b tails (refl x) = 1 := by
  classical
  by_cases hx : Joined b x
  · rw [basedTransport_of_joined b tails _ hx hx]
    simp only [refl_trans, trans_symm]
    rfl
  · exact basedTransport_of_not_joined b tails _ hx

private theorem symm_trans_cancel {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) : p.symm.trans (p.trans q) = q := by
  rw [← trans_assoc, symm_trans, refl_trans]

theorem basedTransport_trans {x y z : X}
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    basedTransport b tails (p.trans q) = basedTransport b tails p * basedTransport b tails q := by
  classical
  by_cases hx : Joined b x
  · have hy : Joined b y := hx.trans ⟨p.out⟩
    have hz : Joined b z := hy.trans ⟨q.out⟩
    rw [basedTransport_of_joined b tails _ hx hz,
      basedTransport_of_joined b tails _ hx hy,
      basedTransport_of_joined b tails _ hy hz]
    apply MulOpposite.unop_injective
    change (tails x hx).trans ((p.trans q).trans (tails z hz).symm) =
      ((tails x hx).trans (p.trans (tails y hy).symm)).trans
        ((tails y hy).trans (q.trans (tails z hz).symm))
    simp only [trans_assoc, symm_trans_cancel]
  · have hy : ¬ Joined b y := fun hy => hx (hy.trans ⟨p.out.symm⟩)
    rw [basedTransport_of_not_joined b tails _ hx,
      basedTransport_of_not_joined b tails _ hx,
      basedTransport_of_not_joined b tails _ hy, one_mul]

end Path.Homotopic.Quotient

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency false in

theorem square_boundary_homotopic (H : C(unitInterval × unitInterval, X)) :
    ((H.horizontalPath 0).toPath.trans (H.verticalPath 1).toPath).Homotopic
      ((H.verticalPath 0).toPath.trans (H.horizontalPath 1).toPath) := by
  let : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  let bottom : Path ((0, 0) : unitInterval × unitInterval) (1, 0) :=
    Path.id.prod (Path.refl 0)
  let right : Path ((1, 0) : unitInterval × unitInterval) (1, 1) :=
    (Path.refl 1).prod Path.id
  let left : Path ((0, 0) : unitInterval × unitInterval) (0, 1) :=
    (Path.refl 0).prod Path.id
  let top : Path ((0, 1) : unitInterval × unitInterval) (1, 1) :=
    Path.id.prod (Path.refl 1)
  have hb : bottom.map H.continuous = (H.horizontalPath 0).toPath := by ext t; rfl
  have hr : right.map H.continuous = (H.verticalPath 1).toPath := by ext t; rfl
  have hl : left.map H.continuous = (H.verticalPath 0).toPath := by ext t; rfl
  have ht : top.map H.continuous = (H.horizontalPath 1).toPath := by ext t; rfl
  obtain ⟨K⟩ := SimplyConnectedSpace.paths_homotopic (bottom.trans right) (left.trans top)
  have h : ((bottom.trans right).map H.continuous).Homotopic
      ((left.trans top).map H.continuous) := ⟨K.map H⟩
  simpa only [Path.map_trans, hb, hr, hl, ht] using h

end ContinuousMap

namespace Path.Homotopic.Quotient

variable {X : Type*} [TopologicalSpace X] (b : X)
    (tails : ∀ x : X, Joined b x → Path.Homotopic.Quotient b x)

noncomputable def basedContinuousTransport (p : C(unitInterval, X)) :
    (FundamentalGroup X b)ᵐᵒᵖ := basedTransport b tails (mk p.toPath)

@[simp] theorem basedContinuousTransport_path {x y : X} (p : Path x y) :
    basedContinuousTransport b tails p.toContinuousMap = basedTransport b tails (mk p) := by
  have hp : p.toContinuousMap.toPath = p.cast p.source p.target := by ext t; rfl
  rw [basedContinuousTransport, hp, mk_cast, basedTransport_cast]

@[simp] theorem basedContinuousTransport_const (x : X) :
    basedContinuousTransport b tails (.const _ x) = 1 :=
  basedTransport_refl b tails x

set_option backward.isDefEq.respectTransparency false in

theorem basedContinuousTransport_square (H : C(unitInterval × unitInterval, X)) :
    basedContinuousTransport b tails (H.horizontalPath 0) *
        basedContinuousTransport b tails (H.verticalPath 1) =
      basedContinuousTransport b tails (H.verticalPath 0) *
        basedContinuousTransport b tails (H.horizontalPath 1) := by
  unfold basedContinuousTransport
  rw [← basedTransport_trans, ← basedTransport_trans, ← mk_trans, ← mk_trans,
    eq.mpr H.square_boundary_homotopic]

end Path.Homotopic.Quotient

import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PeriodCircleLoop
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected










set_option autoImplicit false

open Set

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]




theorem surjective_of_homotopy_id {h : C(AddCircle p, AddCircle p)}
    (H : (ContinuousMap.id (AddCircle p)).Homotopy h) : Function.Surjective h := by
  let F : (ContinuousMap.id (AddCircle p)).HomotopyRel h ∅ :=
    { H with prop' := by intro _ _ hx; exact False.elim hx }
  have hinj := (F.fundamentalGroup_map_bijective 0).1
  intro c
  by_contra hc
  have hmiss (x : AddCircle p) : h x ≠ c := fun he => hc ⟨x, he⟩
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective c
  let e := openPartialHomeomorphCoe p a
  have htarget (x : AddCircle p) : h x ∈ e.target := by
    change h x ∉ {((a : ℝ) : AddCircle p)}
    rw [ha]
    exact hmiss x
  let l : C(AddCircle p, ℝ) :=
    ⟨fun x => e.symm (h x),
      e.symm.continuousOn.comp_continuous h.continuous htarget⟩
  let q : C(ℝ, AddCircle p) := ⟨(↑), AddCircle.continuous_mk' p⟩
  have hfactor : q.comp l = h := by
    ext x
    exact e.right_inv (htarget x)
  let a0 : FundamentalGroup (AddCircle p) 0 :=
    Path.Homotopic.Quotient.mk (periodLoop p)
  have hreal : FundamentalGroup.map l 0 a0 = 1 := Subsingleton.elim _ _
  have hkill : FundamentalGroup.map h 0 a0 = 1 := by
    rw [← hfactor, FundamentalGroup.map_comp_apply, hreal, map_one]
  have ha0 : a0 = 1 := hinj (hkill.trans (map_one (FundamentalGroup.map h 0)).symm)
  exact periodLoop_class_ne_one p ha0

end AddCircle

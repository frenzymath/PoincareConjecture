import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

set_option autoImplicit false

namespace SimpleGraph.Walk

variable {V X : Type*} [TopologicalSpace X] {G : SimpleGraph V}
  (a : V → X) (edge : ∀ {u v : V}, G.Adj u v → _root_.Path (a u) (a v))

noncomputable def realizePath : {u v : V} → G.Walk u v → _root_.Path (a u) (a v)
  | _, _, .nil => Path.refl _
  | _, _, .cons h p => (edge h).trans (realizePath p)

theorem realizePath_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    Path.Homotopic.Quotient.mk (realizePath a edge (p.append q)) =
      (Path.Homotopic.Quotient.mk (realizePath a edge p)).trans
        (Path.Homotopic.Quotient.mk (realizePath a edge q)) := by
  induction p with
  | nil =>
    simp only [nil_append, realizePath, Path.Homotopic.Quotient.mk_refl,
      Path.Homotopic.Quotient.refl_trans]
  | cons h p ih =>
    change (Path.Homotopic.Quotient.mk (edge h)).trans
        (Path.Homotopic.Quotient.mk (realizePath a edge (p.append q))) =
      ((Path.Homotopic.Quotient.mk (edge h)).trans
        (Path.Homotopic.Quotient.mk (realizePath a edge p))).trans
        (Path.Homotopic.Quotient.mk (realizePath a edge q))
    rw [ih, Path.Homotopic.Quotient.trans_assoc]

theorem realizePath_short_closed
    (hreverse : ∀ {u v : V} (h : G.Adj u v), (edge h.symm).Homotopic (edge h).symm)
    {v : V} (p : G.Walk v v) (hp : p.length < 3) :
    Path.Homotopic.Quotient.mk (realizePath a edge p) =
      Path.Homotopic.Quotient.refl (a v) := by
  cases p with
  | nil => rfl
  | cons h p =>
    cases p with
    | nil => exact (G.loopless.irrefl _ h).elim
    | cons k p =>
      cases p with
      | nil =>
        have hr : Path.Homotopic.Quotient.mk (edge k) =
            (Path.Homotopic.Quotient.mk (edge h)).symm :=
          Path.Homotopic.Quotient.eq.mpr (hreverse h)
        simp only [realizePath, Path.Homotopic.Quotient.mk_trans,
          Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl,
          hr, Path.Homotopic.Quotient.trans_symm]
      | cons l p => simp only [length_cons] at hp; omega

end SimpleGraph.Walk

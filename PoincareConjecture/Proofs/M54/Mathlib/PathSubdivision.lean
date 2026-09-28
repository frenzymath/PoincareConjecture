import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Subpath










set_option autoImplicit false

open Set
open scoped unitInterval

namespace Path

variable {X : Type*} [TopologicalSpace X] {x y : X}



def parameterSegment (a b : unitInterval) : Path a b where
  toFun := Icc.convexComb a b
  continuous_toFun := Icc.continuous_convexComb a b
  source' := Icc.convexComb_zero a b
  target' := Icc.convexComb_one a b



@[simp] theorem subpath_apply (p : Path x y) (a b t : unitInterval) :
    p.subpath a b t = p (Icc.convexComb a b t) := rfl



theorem subpath_mem (p : Path x y) {a b : unitInterval} (hab : a ≤ b)
    {s : Set X} (h : MapsTo p (Icc a b) s) (t : unitInterval) :
    p.subpath a b t ∈ s :=
  h ⟨Icc.le_convexComb hab t, Icc.convexComb_le hab t⟩



theorem subpath_trans (p : Path x y) (a b c : unitInterval) :
    ((p.subpath a b).trans (p.subpath b c)).Homotopic (p.subpath a c) :=
  ⟨Path.Homotopy.subpathTransSubpath p a b c⟩



theorem homotopicQuotient_induction_of_open_cover
    {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ)
    (P : ∀ {a b : X}, Homotopic.Quotient a b → Prop)
    (hrefl : ∀ a, P (Homotopic.Quotient.refl a))
    (htrans : ∀ {a b c} (p : Homotopic.Quotient a b)
      (q : Homotopic.Quotient b c), P p → P q → P (p.trans q))
    (hlocal : ∀ {a b} (p : Path a b) (i : ι),
      (∀ t, p t ∈ U i) → P (Homotopic.Quotient.mk p))
    {a b : X} (q : Homotopic.Quotient a b) : P q := by
  induction q using Homotopic.Quotient.ind with
  | mk p =>
    obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval
        (fun i => (hU i).preimage p.continuous) (by
          intro t _
          have : p t ∈ ⋃ i, U i := hcover.symm ▸ mem_univ _
          simpa only [mem_iUnion, mem_preimage] using this)
    have hpref (k : ℕ) : P (Homotopic.Quotient.mk (p.subpath (t 0) (t k))) := by
      induction k with
      | zero => simpa using hrefl (p (t 0))
      | succ k ih =>
        obtain ⟨i, hi⟩ := hsub k
        have hseg := hlocal (p.subpath (t k) (t (k + 1))) i
          (p.subpath_mem (hmono (Nat.le_succ k)) hi)
        have hcomp := htrans _ _ ih hseg
        rw [← Homotopic.Quotient.mk_trans,
          Homotopic.Quotient.eq.mpr (p.subpath_trans (t 0) (t k) (t (k + 1)))] at hcomp
        exact hcomp
    have h := hpref n
    rw [ht0, hn n le_rfl] at h
    have hcast : ∀ {x y x' y' : X} (p : Path x y)
        (hx : x' = x) (hy : y' = y), P (Homotopic.Quotient.mk p) →
          P (Homotopic.Quotient.mk (p.cast hx hy)) := by
      intro x y x' y' p hx hy
      subst x'
      subst y'
      exact id
    simpa using hcast _ p.source.symm p.target.symm h

end Path

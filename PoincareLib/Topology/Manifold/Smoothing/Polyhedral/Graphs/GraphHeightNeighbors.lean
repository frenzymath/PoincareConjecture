import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.GraphHeightSublevels

/-!
# Strict neighboring heights from connected finite sublevels

A finite closed vertex sublevel is exactly a strict sublevel
at a higher threshold. Its connected graph joins a vertex
to any lower vertex and supplies a first lower neighbor.
See Alexander 1924, pp. 6--8 and M76 derivation 281.
-/

set_option autoImplicit false

open Set

/-- A closed sublevel of a finite ordered family is exactly
a strict sublevel at some higher threshold. Empty and full
sublevels are allowed. See M76 derivation 281. -/
theorem exists_strict_sublevel_eq_closed_sublevel
    {V R : Type*} [Finite V] [LinearOrder R] [NoMaxOrder R]
    (A : V → R) (c : R) :
    ∃ d : R, c < d ∧ {x | A x ≤ c} = {x | A x < d} := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let s : Finset V := Finset.univ.filter (fun x => c < A x)
  by_cases hne : s.Nonempty
  · obtain ⟨v, hv, hmin⟩ := s.exists_min_image A hne
    have hcv : c < A v := (Finset.mem_filter.mp hv).2
    refine ⟨A v, hcv, ?_⟩
    ext x
    constructor
    · exact fun hx => (show A x ≤ c from hx).trans_lt hcv
    · intro hx
      change A x ≤ c
      by_contra h
      have hxs : x ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩
      exact (not_lt_of_ge (hmin x hxs)) hx
  · obtain ⟨d, hcd⟩ := exists_gt c
    refine ⟨d, hcd, ?_⟩
    ext x
    have hx : A x ≤ c := by
      by_contra h
      exact hne ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩⟩
    exact ⟨fun _ => hx.trans_lt hcd, fun _ => hx⟩

namespace SimpleGraph

variable {V R : Type*} [Finite V] [LinearOrder R] [NoMaxOrder R]

/-- If every strict sublevel is preconnected, a vertex
with any lower vertex has an actual lower neighbor. The
genericity assumption is only injectivity on the vertices.
See Alexander pp. 6--8 and M76 derivation 281. -/
theorem exists_lower_neighbor_of_preconnected_sublevels
    (G : SimpleGraph V) (A : V → R) (hA : Function.Injective A)
    (hsub : ∀ c, (G.induce {x | A x < c}).Preconnected)
    {p q : V} (hqp : A q < A p) :
    ∃ v : V, G.Adj p v ∧ A v < A p := by
  obtain ⟨d, hpd, hset⟩ := exists_strict_sublevel_eq_closed_sublevel A (A p)
  have hqd : A q < d := hqp.trans hpd
  have hne : (⟨p, hpd⟩ : {x | A x < d}) ≠ ⟨q, hqd⟩ := by
    intro h
    exact hqp.ne (congrArg A (congrArg Subtype.val h)).symm
  obtain ⟨v, hv⟩ := (hsub d ⟨p, hpd⟩ ⟨q, hqd⟩).nonempty_neighborSet_left hne
  have hvp : A (v : V) ≤ A p := hset.symm.subset v.property
  have hpv : G.Adj p v := hv
  exact ⟨v, hpv, lt_of_le_of_ne hvp (fun h => hpv.ne (hA h).symm)⟩

end SimpleGraph

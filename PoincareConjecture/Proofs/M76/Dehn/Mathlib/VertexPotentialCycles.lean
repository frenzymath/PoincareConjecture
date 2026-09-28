import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChainCoordinates

set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} (A : PreAbstractSimplicialComplex ι)

theorem vertex_potential_eq_on_face (a : ι → ZMod 2)
    (ha : vertexCoboundary A a = 0) {s : Finset ι} (hs : s ∈ A.faces)
    {u v : ι} (hu : u ∈ s) (hv : v ∈ s) : a u = a v := by
  classical
  by_cases huv : u = v
  · rw [huv]
  · have hface := pair_mem_faces A hs hu hv
    have hz := congrFun ha (pairEdge A u v hface huv)
    rw [vertexCoboundary_pair] at hz
    exact CharTwo.add_eq_zero.mp hz

variable [Fintype ι]

theorem vertex_potential_triangle_cycle
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (v : Triangle A → ι) (hv : ∀ t, v t ∈ t.val)
    (a : ι → ZMod 2) (ha : vertexCoboundary A a = 0) :
    (edgeCoboundary A).dualMap
      (coordinateChainEquiv (Triangle A) (fun t => a (v t))) = 0 := by
  classical
  have hcoordinate (q : Triangle A) :
      coordinateChainEquiv (Triangle A) (fun t => a (v t)) (Pi.single q 1) = a (v q) := by
    convert coordinateChainEquiv_single (Triangle A) (fun t => a (v t)) q using 1
    congr 1
    funext t
    by_cases ht : t = q <;> simp [ht]
  apply (Pi.basisFun (ZMod 2) (Edge A)).ext
  intro e
  rw [Pi.basisFun_apply]
  change (edgeCoboundary A).dualMap
    (coordinateChainEquiv (Triangle A) (fun t => a (v t))) (Pi.single e 1) = 0
  obtain ⟨q, r, hqr, hpair⟩ := Finset.card_eq_two.mp (hcofaces e)
  have heq : e.val ⊆ q.val := (Finset.mem_filter.mp
    (show q ∈ triangleCofaces A e by rw [hpair]; simp)).2
  have her : e.val ⊆ r.val := (Finset.mem_filter.mp
    (show r ∈ triangleCofaces A e by rw [hpair]; simp)).2
  obtain ⟨p, hpe⟩ := Finset.card_pos.mp (show 0 < e.val.card by rw [e.property.2]; decide)
  rw [boundary2_single_eq_sum_coordinates, hpair, Finset.sum_pair hqr,
    hcoordinate, hcoordinate]
  rw [vertex_potential_eq_on_face A a ha q.property.1 (hv q) (heq hpe),
    vertex_potential_eq_on_face A a ha r.property.1 (hv r) (her hpe)]
  exact CharTwo.add_self_eq_zero (a p)

end PreAbstractSimplicialComplex.ModTwoCochains

import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TetrahedronCofaceConstancy









set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*}



def tetrahedronGraph (A : PreAbstractSimplicialComplex ι) : SimpleGraph (Tetrahedron A) where
  Adj q r := q ≠ r ∧ ∃ t : Triangle A, t.val ⊆ q.val ∧ t.val ⊆ r.val
  symm := ⟨by
    rintro q r ⟨hqr, t, htq, htr⟩
    exact ⟨Ne.symm hqr, t, htr, htq⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E)



theorem tetrahedronGraph_preconnected_of_links
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 4)
    (hconn : K.vertexAbstractComplex.edgeGraph.Preconnected)
    (hlinks : ∀ s ∈ K.faces, s.card < 3 →
      (K.faceLink s).vertexAbstractComplex.edgeGraph.Preconnected) :
    (tetrahedronGraph K.toPreAbstractSimplicialComplex).Preconnected := by
  intro q r
  let G := tetrahedronGraph K.toPreAbstractSimplicialComplex
  have heq : G.Reachable q q = G.Reachable q r := by
    apply K.tetrahedron_label_constant (fun u => G.Reachable q u) hpure hconn hlinks
    intro t ht htc u v htu htv
    by_cases huv : u = v
    · rw [huv]
    · have hadj : G.Adj u v := ⟨huv, ⟨t, ht, htc⟩, htu, htv⟩
      exact propext ⟨fun h => h.trans hadj.reachable,
        fun h => h.trans hadj.reachable.symm⟩
  exact heq ▸ SimpleGraph.Reachable.refl q



theorem tetrahedronGraph_connected_of_links
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 4)
    (hconn : K.vertexAbstractComplex.edgeGraph.Connected)
    (hlinks : ∀ s ∈ K.faces, s.card < 3 →
      (K.faceLink s).vertexAbstractComplex.edgeGraph.Preconnected) :
    (tetrahedronGraph K.toPreAbstractSimplicialComplex).Connected := by
  obtain ⟨v⟩ := hconn.nonempty
  obtain ⟨t, ht, _, htc⟩ := hpure _ v.property
  let : Nonempty (Tetrahedron K.toPreAbstractSimplicialComplex) := ⟨⟨t, ht, htc⟩⟩
  exact ⟨K.tetrahedronGraph_preconnected_of_links hpure hconn.preconnected hlinks⟩

variable [FiniteDimensional ℝ E]




theorem tetrahedronGraph_connected_of_isConnected
    (hK : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 4)
    (hconn : IsConnected K.space)
    (hlinks : ∀ s ∈ K.faces, s.card < 3 → IsConnected (K.faceLink s).space) :
    (tetrahedronGraph K.toPreAbstractSimplicialComplex).Connected := by
  apply K.tetrahedronGraph_connected_of_links hpure
    (K.connected_edgeGraph_of_isConnected hK hconn)
  intro s hs hsc
  exact ((K.faceLink s).connected_edgeGraph_of_isConnected
    (finite_faceLink_faces hK s) (hlinks s hs hsc)).preconnected

end Geometry.SimplicialComplex

import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleCofaceConstancy









set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*}



def triangleGraph (A : PreAbstractSimplicialComplex ι) : SimpleGraph (Triangle A) where
  Adj q r := q ≠ r ∧ ∃ e : Edge A, e.val ⊆ q.val ∧ e.val ⊆ r.val
  symm := ⟨by
    rintro q r ⟨hqr, e, heq, her⟩
    exact ⟨Ne.symm hqr, e, her, heq⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E)



theorem triangleGraph_preconnected_of_links
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hconn : K.vertexAbstractComplex.edgeGraph.Preconnected)
    (hlinks : ∀ p ∈ K.vertices,
      (K.faceLink {p}).vertexAbstractComplex.edgeGraph.Preconnected) :
    (triangleGraph K.toPreAbstractSimplicialComplex).Preconnected := by
  intro q r
  let G := triangleGraph K.toPreAbstractSimplicialComplex
  have heq : G.Reachable q q = G.Reachable q r := by
    apply K.triangle_label_constant (fun u => G.Reachable q u) hpure hconn hlinks
    intro e he hec u v heu hev
    by_cases huv : u = v
    · rw [huv]
    · have hadj : G.Adj u v := ⟨huv, ⟨e, he, hec⟩, heu, hev⟩
      exact propext ⟨fun h => h.trans hadj.reachable,
        fun h => h.trans hadj.reachable.symm⟩
  exact heq ▸ SimpleGraph.Reachable.refl q



theorem triangleGraph_connected_of_links
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hconn : K.vertexAbstractComplex.edgeGraph.Connected)
    (hlinks : ∀ p ∈ K.vertices,
      (K.faceLink {p}).vertexAbstractComplex.edgeGraph.Preconnected) :
    (triangleGraph K.toPreAbstractSimplicialComplex).Connected := by
  obtain ⟨v⟩ := hconn.nonempty
  obtain ⟨t, ht, _, htc⟩ := hpure _ v.property
  let : Nonempty (Triangle K.toPreAbstractSimplicialComplex) := ⟨⟨t, ht, htc⟩⟩
  exact ⟨K.triangleGraph_preconnected_of_links hpure hconn.preconnected hlinks⟩

variable [FiniteDimensional ℝ E]



theorem triangleGraph_connected_of_isConnected
    (hK : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hconn : IsConnected K.space)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space) :
    (triangleGraph K.toPreAbstractSimplicialComplex).Connected := by
  apply K.triangleGraph_connected_of_links hpure
    (K.connected_edgeGraph_of_isConnected hK hconn)
  intro p hp
  exact ((K.faceLink {p}).connected_edgeGraph_of_isConnected
    (finite_faceLink_faces hK {p}) (hlinks p hp)).preconnected

end Geometry.SimplicialComplex

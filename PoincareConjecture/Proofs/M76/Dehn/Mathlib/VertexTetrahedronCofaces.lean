import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TetrahedronBoundary
import PoincareConjecture.Proofs.M76.Mathlib.VertexAbstractComplex

set_option autoImplicit false

open Set
open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem tetrahedronCofaces_card_eq_original
    (K : SimplicialComplex ℝ G) [Fintype K.vertices]
    (t : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex) :
    (tetrahedronCofaces K.vertexAbstractComplex.toPreAbstractSimplicialComplex t).card =
      {q : Finset G | q ∈ K.faces ∧ q.card = 4 ∧
        t.val.map (Function.Embedding.subtype _) ⊆ q}.ncard := by
  classical
  let : DecidableEq K.vertices := Classical.decEq K.vertices
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let emb : K.vertices ↪ G := Function.Embedding.subtype _
  rw [← ncard_coe_finset (tetrahedronCofaces A t)]
  apply ncard_congr (fun q _ => q.val.map emb)
  · intro q hq
    have hsub : t.val ⊆ q.val := (Finset.mem_filter.mp hq).2
    refine ⟨q.property.1, ?_, Finset.map_subset_map.mpr hsub⟩
    simpa only [Finset.card_map] using q.property.2
  · intro q r _ _ hqr
    exact Subtype.ext (Finset.map_injective emb hqr)
  · rintro q ⟨hq, hqc, htq⟩
    have hv (x : G) (hx : x ∈ q) : x ∈ K.vertices :=
      K.down_closed hq (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)
    let b : Finset K.vertices := q.subtype (fun x => x ∈ K.vertices)
    have hbq : b.map emb = q := Finset.subtype_map_of_mem hv
    have hb : b ∈ A.faces := by
      change b.map emb ∈ K.faces
      rw [hbq]
      exact hq
    have hbc : b.card = 4 := by
      calc
        b.card = (b.map emb).card := by rw [Finset.card_map]
        _ = 4 := by rw [hbq]; exact hqc
    have htb : t.val ⊆ b := Finset.map_subset_map.mp (hbq.symm ▸ htq)
    refine ⟨⟨b, hb, hbc⟩, ?_, hbq⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htb⟩

end Geometry.SimplicialComplex

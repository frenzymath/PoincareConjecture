import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexCycleConstancy
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexPotentialCycles










set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.vertices]

local notation "L" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex

open Classical in



noncomputable def boundaryTopCycleEquiv
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hcofaces : ∀ e : Edge L, (triangleCofaces L e).card = 2)
    (hlinks : ∀ p : K.vertices,
      (K.faceLink {p.val}).vertexAbstractComplex.edgeGraph.Preconnected) :
    LinearMap.ker (vertexCoboundary L) ≃ₗ[ZMod 2]
      LinearMap.ker (edgeCoboundary L).dualMap := by
  classical
  have hface (s : Finset K.vertices) (hs : s ∈ K.vertexAbstractComplex.faces) :
      ∃ q : Triangle L, s ⊆ q.val := by
    obtain ⟨q, hq, hsq, hqc⟩ := hpure _ hs
    let qg : Triangle K.toPreAbstractSimplicialComplex := ⟨q, hq, hqc⟩
    refine ⟨(K.vertexFaceEquiv 3).symm qg, ?_⟩
    apply Finset.map_subset_map.mp
    change s.map (Function.Embedding.subtype _) ⊆
      ((K.vertexFaceEquiv 3).symm qg).val.map (Function.Embedding.subtype _)
    rw [K.vertexFaceEquiv_symm_map]
    exact hsq
  have htriangle (p : K.vertices) : ∃ q : Triangle L, p ∈ q.val := by
    obtain ⟨q, hq⟩ := hface {p} (K.vertexAbstractComplex.singleton_mem p)
    exact ⟨q, hq (Finset.mem_singleton_self p)⟩
  choose t ht using htriangle
  have hvertex (q : Triangle L) : ∃ p : K.vertices, p ∈ q.val :=
    Finset.card_pos.mp (by rw [q.property.2]; decide)
  choose v hv using hvertex
  have hcoordinate (b : Triangle L → ZMod 2) (q : Triangle L) :
      coordinateChainEquiv (Triangle L) b (Pi.single q 1) = b q := by
    convert coordinateChainEquiv_single (Triangle L) b q using 1
    congr 1
    funext s
    by_cases hs : s = q <;> simp [hs]
  have hforward (a : LinearMap.ker (vertexCoboundary L)) :
      (edgeCoboundary L).dualMap
        (coordinateChainEquiv (Triangle L) (fun q => a.val (v q))) = 0 :=
    vertex_potential_triangle_cycle L hcofaces v hv a.val a.property
  have hreverse (c : LinearMap.ker (edgeCoboundary L).dualMap) :
      vertexCoboundary L (fun p => c.val (Pi.single (t p) 1)) = 0 := by
    funext e
    rw [vertexCoboundary_apply]
    obtain ⟨u, w, huw, he⟩ := Finset.card_eq_two.mp e.property.2
    obtain ⟨q, heq⟩ := hface e.val e.property.1
    have huq : u ∈ q.val := heq (by rw [he]; simp)
    have hwq : w ∈ q.val := heq (by rw [he]; simp)
    have hu := K.boundary2_ker_coordinates_of_common_vertex hpure
      (fun e => (hcofaces e).le) u (hlinks u) c.val c.property (t u) q (ht u) huq
    have hw := K.boundary2_ker_coordinates_of_common_vertex hpure
      (fun e => (hcofaces e).le) w (hlinks w) c.val c.property (t w) q (ht w) hwq
    rw [he, Finset.sum_pair huw, hu, hw]
    exact CharTwo.add_self_eq_zero (c.val (Pi.single q 1))
  refine {
    toFun := fun a => ⟨coordinateChainEquiv (Triangle L) (fun q => a.val (v q)), hforward a⟩
    invFun := fun c => ⟨fun p => c.val (Pi.single (t p) 1), hreverse c⟩
    left_inv := by
      intro a
      apply Subtype.ext
      funext p
      change coordinateChainEquiv (Triangle L) (fun q => a.val (v q))
        (Pi.single (t p) 1) = a.val p
      rw [hcoordinate]
      exact vertex_potential_eq_on_face L a.val a.property (t p).property.1 (hv (t p)) (ht p)
    right_inv := by
      intro c
      apply Subtype.ext
      apply (Pi.basisFun (ZMod 2) (Triangle L)).ext
      intro q
      rw [Pi.basisFun_apply]
      change coordinateChainEquiv (Triangle L)
        (fun s => c.val (Pi.single (t (v s)) 1)) (Pi.single q 1) =
          c.val (Pi.single q 1)
      rw [hcoordinate]
      exact K.boundary2_ker_coordinates_of_common_vertex hpure
        (fun e => (hcofaces e).le) (v q) (hlinks (v q)) c.val c.property
        (t (v q)) q (ht (v q)) (hv q)
    map_add' := by
      intro a b
      apply Subtype.ext
      exact (coordinateChainEquiv (Triangle L)).map_add
        (fun q => a.val (v q)) (fun q => b.val (v q))
    map_smul' := by
      intro r a
      apply Subtype.ext
      exact (coordinateChainEquiv (Triangle L)).map_smul r (fun q => a.val (v q)) }



theorem finrank_boundary2_ker_eq_vertex_ker
    (hpure : ∀ t ∈ K.faces, ∃ q ∈ K.faces, t ⊆ q ∧ q.card = 3)
    (hcofaces : ∀ e : Edge L, (triangleCofaces L e).card = 2)
    (hlinks : ∀ p : K.vertices,
      (K.faceLink {p.val}).vertexAbstractComplex.edgeGraph.Preconnected) :
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary L).dualMap) =
      Module.finrank (ZMod 2) (LinearMap.ker (vertexCoboundary L)) :=
  (K.boundaryTopCycleEquiv hpure hcofaces hlinks).finrank_eq.symm

end Geometry.SimplicialComplex

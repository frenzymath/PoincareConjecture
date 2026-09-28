import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.RelativeCocycleExactness
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.RestrictionRanks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ModTwoCocycleOfClosed

set_option autoImplicit false

universe u v w

open Set

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  (A : PreAbstractSimplicialComplex ι) (B : PreAbstractSimplicialComplex κ)
  (f : κ ↪ ι) (hf : ∀ s ∈ B.faces, s.map f ∈ A.faces)

def includedEdge (e : Edge B) : Edge A :=
  ⟨e.val.map f, hf e.val e.property.1, (Finset.card_map _).trans e.property.2⟩

def edgeRestriction : (Edge A → ZMod 2) →ₗ[ZMod 2] (Edge B → ZMod 2) where
  toFun z e := z (includedEdge A B f hf e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype ι] [Fintype κ] in

theorem edgeValue_eq_of_restriction_potential (z : Edge A → ZMod 2)
    (a : κ → ZMod 2) (ha : vertexCoboundary B a = edgeRestriction A B f hf z)
    {s : Finset κ} (hs : s ∈ B.faces) {i j : κ} (hi : i ∈ s) (hj : j ∈ s) :
    edgeValue A z (f i) (f j) = a i + a j := by
  classical
  by_cases hij : i = j
  · subst j
    rw [edgeValue_self, CharTwo.add_self_eq_zero]
  have hface := pair_mem_faces B hs hi hj
  have hface' : {f i, f j} ∈ A.faces := by
    simpa only [Finset.map_insert, Finset.map_singleton] using hf _ hface
  have hval := congrFun ha (pairEdge B i j hface hij)
  rw [vertexCoboundary_pair] at hval
  rw [edgeValue_pair A z (f i) (f j) hface' (f.injective.ne hij)]
  have he : includedEdge A B f hf (pairEdge B i j hface hij) =
      pairEdge A (f i) (f j) hface' (f.injective.ne hij) := by
    apply Subtype.ext
    simp only [includedEdge, pairEdge, Finset.map_insert, Finset.map_singleton]
  exact (hval.trans (congrArg z he)).symm

end PreAbstractSimplicialComplex.ModTwoCochains

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

open PreAbstractSimplicialComplex.ModTwoCochains

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  {ι κ : Type v} [Fintype ι] [Fintype κ]
  {Z : Type w} [TopologicalSpace Z]

omit [Fintype κ] in

theorem restricted_closed_mem_range_of_marked_terminal
    (A : PreAbstractSimplicialComplex ι) (B : PreAbstractSimplicialComplex κ)
    (f : κ ↪ ι) (hf : ∀ s ∈ B.faces, s.map f ∈ A.faces)
    (hvertex : ∀ i : ι, {i} ∈ A.faces)
    {N D : Set X} (hDN : D ⊆ N)
    {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r D)
    (hr : ∀ x, r x ∈ D) {s : C(N, N)}
    (K : (ContinuousMap.id N).HomotopyRel s (Subtype.val ⁻¹' D))
    (hs : ∀ n, (s n : X) ∈ D) (J : A.barycentricSpace ≃ₜ N)
    (γ : C(Z, X)) (hγ : ∀ z, γ z ∈ D)
    (hmark : ∀ z, ∃ t ∈ B.faces,
      (J.symm ⟨γ z, hDN (hγ z)⟩).val ∈ StdSimplexCore.barycentricFace (t.map f))
    (hterminal : ∀ (Y : Type (max u v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → X),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
      ∀ lift : C(Z, Y), (∀ z, p (lift z) = γ z) → False)
    (z : Edge A → ZMod 2) (hz : edgeCoboundary A z = 0)
    (hrest : edgeRestriction A B f hf z ∈ LinearMap.range (vertexCoboundary B)) :
    z ∈ LinearMap.range (vertexCoboundary A) := by
  classical
  obtain ⟨a, ha⟩ := hrest
  let a' : ι → ZMod 2 := Function.extend f a (fun _ => 0)
  have ha' (i : κ) : a' (f i) = a i := f.injective.extend_apply _ _ i
  apply mem_range_vertexCoboundary_of_coboundary A z hz
  apply (cocycleOfClosed A z hz).isCoboundary_of_marked_terminal_common_deformation
    hvertex hDN H hr K hs J γ hγ a' ?_ hterminal
  intro q i j hi hj
  obtain ⟨t, ht, hqt⟩ := hmark q
  obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp (A.mem_face_of_mem_openVertexStar hqt hi)
  obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp (A.mem_face_of_mem_openVertexStar hqt hj)
  change edgeValue A z (f i') (f j') = a' (f i') + a' (f j')
  rw [ha', ha']
  exact edgeValue_eq_of_restriction_potential A B f hf z a ha ht hi' hj'

theorem finrank_closed_le_coboundaries_add_one_of_marked_terminal
    [DecidableEq κ]
    (A : AbstractSimplicialComplex ι) (B : AbstractSimplicialComplex κ)
    (f : κ ↪ ι) (hf : ∀ s ∈ B.faces, s.map f ∈ A.faces)
    (hconn : B.edgeGraph.Connected) (hdegree : ∀ v, (B.edgeGraph.neighborSet v).ncard = 2)
    {N D : Set X} (hDN : D ⊆ N)
    {r : C(X, X)} (H : (ContinuousMap.id X).HomotopyRel r D)
    (hr : ∀ x, r x ∈ D) {s : C(N, N)}
    (K : (ContinuousMap.id N).HomotopyRel s (Subtype.val ⁻¹' D))
    (hs : ∀ n, (s n : X) ∈ D) (J : A.toPreAbstractSimplicialComplex.barycentricSpace ≃ₜ N)
    (γ : C(Z, X)) (hγ : ∀ z, γ z ∈ D)
    (hmark : ∀ z, ∃ t ∈ B.faces,
      (J.symm ⟨γ z, hDN (hγ z)⟩).val ∈ StdSimplexCore.barycentricFace (t.map f))
    (hterminal : ∀ (Y : Type (max u v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → X),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) →
      ∀ lift : C(Z, Y), (∀ z, p (lift z) = γ z) → False) :
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary A.toPreAbstractSimplicialComplex)) ≤
      Module.finrank (ZMod 2) (LinearMap.range
        (vertexCoboundary A.toPreAbstractSimplicialComplex)) + 1 := by
  classical
  have h := (edgeRestriction A.toPreAbstractSimplicialComplex B.toPreAbstractSimplicialComplex
    f hf).finrank_le_of_relative_kernel
    (LinearMap.ker (edgeCoboundary A.toPreAbstractSimplicialComplex))
    (LinearMap.range (vertexCoboundary A.toPreAbstractSimplicialComplex))
    (LinearMap.range (vertexCoboundary B.toPreAbstractSimplicialComplex))
    (fun z hz hrest => restricted_closed_mem_range_of_marked_terminal
      A.toPreAbstractSimplicialComplex B.toPreAbstractSimplicialComplex f hf
      A.singleton_mem hDN H hr K hs J γ hγ hmark hterminal z hz hrest)
  rwa [B.finrank_edge_quotient_eq_one_of_two_neighbors hconn hdegree] at h

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle

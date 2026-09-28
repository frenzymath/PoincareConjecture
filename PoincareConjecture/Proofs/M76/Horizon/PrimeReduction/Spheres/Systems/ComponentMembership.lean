import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import PoincareConjecture.Proofs.M76.Mathlib.GeometricGraphComponents
import PoincareConjecture.Proofs.M76.PrimeReduction.ActualGraphCarrier
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_unique_member_of_preconnected_finite_closed_union
    {X κ : Type*} [TopologicalSpace X] [Finite κ]
    (S : κ → Set X) (hclosed : ∀ i, IsClosed (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {C : Set X} (hne : C.Nonempty) (hC : IsPreconnected C)
    (hsub : C ⊆ ⋃ i, S i) : ∃! i, C ⊆ S i := by
  classical
  obtain ⟨x, hx⟩ := hne
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hsub hx)
  let R : Set X := ⋃ j : {j : κ // j ≠ i}, S j.val
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hclosed j.val)
  have hdisR : Disjoint (S i) R := by
    apply disjoint_left.mpr
    intro y hyi hyr
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hyr
    exact disjoint_left.mp (hdis (Ne.symm j.property)) hyi hyj
  have hcover : C ⊆ S i ∪ R := by
    intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hsub hy)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hyj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)
  have hinter : C ∩ (S i ∩ R) = ∅ := by rw [hdisR.inter_eq, inter_empty]
  have hside := isPreconnected_iff_subset_of_disjoint_closed.mp hC
    (S i) R (hclosed i) hR hcover hinter
  have hCi : C ⊆ S i := hside.resolve_right
    (fun h => disjoint_left.mp hdisR hxi (h hx))
  refine ⟨i, hCi, ?_⟩
  intro j hj
  by_contra hji
  exact disjoint_left.mp (hdis hji) (hj hx) hxi

theorem exists_unique_sphere_member_of_preconnected
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {C : Set X} (hne : C.Nonempty) (hC : IsPreconnected C)
    (hsub : C ⊆ ⋃ i, S i) : ∃! i, C ⊆ S i :=
  exists_unique_member_of_preconnected_finite_closed_union S
    (fun i => (sS i).isCompact.isClosed) hdis hne hC hsub

theorem exists_unique_preimage_component_member
    {X Y κ : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite κ]
    (S : κ → Set Y) (hclosed : ∀ i, IsClosed (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (f : X → Y) (hf : Continuous f) (x : X) (hx : f x ∈ ⋃ i, S i) :
    ∃! i, f x ∈ S i ∧
      connectedComponentIn (f ⁻¹' ⋃ j, S j) x = connectedComponentIn (f ⁻¹' S i) x := by
  have hconn := isConnected_connectedComponentIn_iff.mpr
    (show x ∈ f ⁻¹' ⋃ i, S i from hx)
  obtain ⟨i,hi,_⟩ := exists_unique_member_of_preconnected_finite_closed_union S hclosed hdis
    (hconn.nonempty.image f) (hconn.isPreconnected.image f hf.continuousOn)
    (by rintro _ ⟨y,hy,rfl⟩; exact connectedComponentIn_subset (f ⁻¹' ⋃ i, S i) x hy)
  have hxi : f x ∈ S i := hi (mem_image_of_mem f (mem_connectedComponentIn hx))
  refine ⟨i,⟨hxi,Subset.antisymm ?_ ?_⟩,?_⟩
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx) (fun y hy => hi (mem_image_of_mem f hy))
  · exact connectedComponentIn_mono x (preimage_mono (subset_iUnion S i))
  · intro j hj
    by_contra hji
    exact disjoint_left.mp (hdis hji) hj.1 hxi

theorem exists_unique_moved_sphere_member_of_preconnected
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) (Phi : X ≃ₜ X)
    {C : Set X} (hne : C.Nonempty) (hC : IsPreconnected C)
    (hsub : C ⊆ Phi '' (⋃ i, S i)) : ∃! i, C ⊆ Phi '' S i := by
  have hdis' : Pairwise fun i j => Disjoint (Phi '' S i) (Phi '' S j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    exact disjoint_left.mp (hdis hij) hx ((Phi.injective heq) ▸ hz)
  apply exists_unique_member_of_preconnected_finite_closed_union (fun i => Phi '' S i)
    (fun i => ((sS i).isCompact.image Phi.continuous).isClosed) hdis' hne hC
  simpa only [image_iUnion] using hsub

private theorem isConnected_segmentCarrier
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : SimpleGraph V) (p : V → E) (hH : H.Connected)
    (hne : ∀ v, (H.neighborSet v).Nonempty) : IsConnected (H.segmentCarrier p) := by
  have hvertex (v : V) : p v ∈ H.segmentCarrier p := by
    obtain ⟨w, hvw⟩ := hne v
    exact ⟨v, w, hvw, left_mem_segment ℝ _ _⟩
  have hedge (u v : V) (huv : H.Adj u v) : JoinedIn (H.segmentCarrier p) (p u) (p v) :=
    JoinedIn.of_segment_subset (fun x hx => ⟨u, v, huv, hx⟩)
  have hwalk (u v : V) (w : H.Walk u v) : JoinedIn (H.segmentCarrier p) (p u) (p v) := by
    induction w with
    | nil => exact JoinedIn.refl (hvertex _)
    | cons huv w ih => exact (hedge _ _ huv).trans ih
  obtain ⟨u⟩ := hH.nonempty
  have hpath : IsPathConnected (H.segmentCarrier p) := by
    refine ⟨p u, hvertex u, ?_⟩
    rintro x ⟨v, w, hvw, hx⟩
    obtain ⟨walk⟩ := hH u v
    refine (hwalk u v walk).trans (JoinedIn.of_segment_subset ?_)
    intro y hy
    exact ⟨v, w, hvw, (convex_segment (p v) (p w)).segment_subset
      (left_mem_segment ℝ _ _) hx hy⟩
  exact hpath.isConnected

theorem isConnected_actual_graph_component_carrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (G : SimplicialComplex ℝ E)
    (hne : ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty)
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    IsConnected (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E))) := by
  apply isConnected_segmentCarrier C.toSimpleGraph (fun v => (v.val : E))
    C.connected_toSimpleGraph
  intro v
  obtain ⟨w, hvw⟩ := hne v.val
  exact ⟨⟨w, C.mem_supp_of_adj_mem_supp v.property hvw⟩, hvw⟩

theorem exists_unique_moved_sphere_member_of_graph_component
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) (Phi : X ≃ₜ X)
    (Q : OpenPartialHomeomorph X V3) (G : SimplicialComplex ℝ V3)
    (hGQ : G.space ⊆ Q.target)
    (hsub : Q.symm '' G.space ⊆ Phi '' (⋃ i, S i))
    (hne : ∀ v : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty)
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    ∃! i, Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ Phi '' S i := by
  classical
  have hCG : C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ G.space := by
    rintro x ⟨v, w, hvw, hx⟩
    have hs : ({(v.val : V3), (w.val : V3)} : Finset V3) ∈ G.faces := by
      have hh := hvw.2
      change ({v.val, w.val} : Finset G.vertices).map (Function.Embedding.subtype _) ∈ G.faces at hh
      simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using hh
    apply G.convexHull_subset_space hs
    simpa only [Finset.coe_pair, convexHull_pair] using hx
  have hconn := isConnected_actual_graph_component_carrier G hne C
  have himage := hconn.image Q.symm (Q.symm.continuousOn.mono (hCG.trans hGQ))
  exact exists_unique_moved_sphere_member_of_preconnected S sS hdis Phi
    himage.nonempty himage.isPreconnected ((image_mono hCG).trans hsub)

end PoincareConjecture.M76

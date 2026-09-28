import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalExceptionalComponents

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

def originalMarkedBoundaryComponents
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K J : SimplicialComplex ℝ E) (g : E → X) (S : Set X) :
    Set (ConnectedComponents (K.space \ g ⁻¹' S : Set E)) :=
  {c | ∃ x : (K.space \ g ⁻¹' S : Set E),
    (x : E) ∈ J.space ∧ ConnectedComponents.mk x = c}

theorem originalMarkedBoundaryComponents_finite_ncard
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hJK : J ≤ K)
    (g : E → X) (S : Set X) (hJS : Disjoint (g '' J.space) S) :
    (originalMarkedBoundaryComponents K J g S).Finite ∧
      (originalMarkedBoundaryComponents K J g S).ncard ≤ J.vertices.ncard := by
  classical
  have hJfinite : J.faces.Finite := hK.subset hJK
  have hV : J.vertices.Finite := by
    rw [J.vertices_eq]
    exact hJfinite.biUnion (fun a _ => a.finite_toSet)
  letI : Finite J.vertices := hV.to_subtype
  have hJP : J.space ⊆ K.space \ g ⁻¹' S := by
    intro x hx
    exact ⟨SimplicialComplex.space_subset_of_le hJK hx,
      fun hs => disjoint_left.mp hJS ⟨x,hx,rfl⟩ hs⟩
  let inc : J.vertices → (K.space \ g ⁻¹' S : Set E) :=
    fun p => ⟨p,hJP (J.vertices_subset_space p.property)⟩
  let mark := fun p : J.vertices => ConnectedComponents.mk (inc p)
  have hrange : range mark = originalMarkedBoundaryComponents K J g S := by
    ext c
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨inc p,J.vertices_subset_space p.property,rfl⟩
    · rintro ⟨x,hxJ,rfl⟩
      obtain ⟨t,ht,hxt⟩ := SimplicialComplex.mem_space_iff.mp hxJ
      obtain ⟨p,hpt⟩ := J.nonempty_of_mem_faces ht
      have hpt' : p ∈ convexHull ℝ (t : Set E) := subset_convexHull ℝ _ hpt
      have hconn := (convex_convexHull ℝ (t : Set E)).isPreconnected
      have hpc : p ∈ connectedComponentIn (K.space \ g ⁻¹' S) (x : E) :=
        hconn.subset_connectedComponentIn hxt
          ((J.convexHull_subset_space ht).trans hJP) hpt'
      refine ⟨⟨p,J.face_subset_vertices ht hpt⟩,?_⟩
      exact (Topology.mem_componentIn_iff_component_class x.property
        (hJP (J.vertices_subset_space (J.face_subset_vertices ht hpt)))).mp hpc
  rw [←hrange]
  refine ⟨finite_range mark,?_⟩
  have hbound : (range mark).ncard ≤ Nat.card J.vertices := by
    simpa only [image_univ,ncard_univ] using
      (ncard_image_le (s := (univ : Set J.vertices)) (f := mark))
  simpa only [Nat.card_coe_set_eq] using hbound

theorem mem_componentIn_of_mem_closure
    {Y : Type*} [TopologicalSpace Y] {P : Set Y} {x y : Y}
    (hx : x ∈ P) (hy : y ∈ P) (hyc : y ∈ closure (connectedComponentIn P x)) :
    y ∈ connectedComponentIn P x := by
  have heq : (Subtype.val : P → Y) ⁻¹' closure (connectedComponentIn P x) =
      connectedComponent (⟨x,hx⟩ : P) := by
    rw [connectedComponentIn_eq_image hx,
      ←Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
      isClosed_connectedComponent.closure_eq]
  have hmem : (⟨y,hy⟩ : P) ∈ connectedComponent (⟨x,hx⟩ : P) := heq.subset hyc
  rw [connectedComponentIn_eq_image hx]
  exact ⟨⟨y,hy⟩,hmem,rfl⟩

theorem original_component_closure_mapsTo_interior_of_not_boundary_exception
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) {R S : Set X} (hKR : g '' K.space ⊆ R)
    (hmark : ∀ z ∈ K.space, g z ∈ frontier R ↔ z ∈ J.space)
    (hS : S ⊆ interior R)
    (x : (K.space \ g ⁻¹' S : Set E))
    (hx : ConnectedComponents.mk x ∉ originalMarkedBoundaryComponents K J g S) :
    MapsTo g (closure (connectedComponentIn (K.space \ g ⁻¹' S) (x : E))) (interior R) := by
  intro y hy
  have hyK : y ∈ K.space :=
    (K.isCompact_space_of_finite hK).isClosed.closure_subset_iff.mpr
      ((connectedComponentIn_subset _ _).trans inter_subset_left) hy
  by_contra hyint
  have hyfront : g y ∈ frontier R := ⟨subset_closure (hKR ⟨y,hyK,rfl⟩),hyint⟩
  have hyP : y ∈ K.space \ g ⁻¹' S := ⟨hyK,fun hs => hyint (hS hs)⟩
  have hyc := mem_componentIn_of_mem_closure x.property hyP hy
  apply hx
  exact ⟨⟨y,hyP⟩,(hmark y hyK).mp hyfront,
    (Topology.mem_componentIn_iff_component_class x.property hyP).mp hyc⟩

end PoincareConjecture.M76.PrismBelt

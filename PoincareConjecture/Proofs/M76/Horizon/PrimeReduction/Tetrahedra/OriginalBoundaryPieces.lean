import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalSurfacePieces
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBoundaryPolygons









set_option autoImplicit false
universe u
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_tetrahedral_boundary_pieces
    {E : Type u} {X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hS : ∀ i, S i ⊆ g '' K.space)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (havoid : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4) :
    ∃ γ δ : Type u, Finite γ ∧ Finite δ ∧
      ∃ (C : γ → SimplicialComplex ℝ E) (P : γ → Set X)
        (n : δ → ℕ) (L : ∀ i, Polygon E (n i + 3)) (owner : δ → γ),
        (∀ c, (C c).faces.Finite ∧ IsConnected (C c).space ∧
          (C c).space ⊆ convexHull ℝ (t : Set E) ∧
          P c = g '' (C c).space ∧ PolyhedralPLInCharts e g (C c).space ∧
          IsCompact (P c) ∧ IsConnected (P c)) ∧
        Pairwise (fun c d => Disjoint (P c) (P d)) ∧
        (⋃ c, P c) = (g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i) ∧
        (∀ i, Function.Injective (L i) ∧ (L i).HasSimplicialEdges ∧
          (L i).boundary ℝ ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) ∧
        Pairwise (fun i j => Disjoint (g '' (L i).boundary ℝ) (g '' (L j).boundary ℝ)) ∧
        (∀ i c, g '' (L i).boundary ℝ ⊆ P c ↔ owner i = c) ∧
        (∀ c, P c ∩ g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) =
          ⋃ i : {i : δ // owner i = c}, g '' (L i).boundary ℝ) ∧
        ∀ c x, x ∈ P c →
          connectedComponentIn ((g '' convexHull ℝ (t : Set E)) ∩ (⋃ i, S i)) x = P c := by
  classical
  obtain ⟨γ,hγ,C,P,hC,_,hPdis,_,hPcover,hPcomp,_⟩ :=
    exists_original_sphere_pieces_in_face he K hK g hg hgi S sS hS hdis ht
  let : Finite γ := hγ
  obtain ⟨δ,hδ,n,L,hL,_,hLdis,hLcover⟩ :=
    exists_original_tetrahedral_boundary_polygons K hK g hgi Q A hmap hA
      havoid hposition ht ht4
  let : Finite δ := hδ
  have hfront : intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ⊆
      convexHull ℝ (t : Set E) :=
    intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hLconn (i : δ) : IsConnected (g '' (L i).boundary ℝ) := by
    obtain ⟨H⟩ := (L i).nonempty_boundary_homeomorph_circle (hL i).2.1 (hL i).1
    have hc : IsConnected ((L i).boundary ℝ) :=
      isConnected_iff_connectedSpace.mpr (H.connectedSpace_iff.mpr inferInstance)
    exact hc.image g (hg.continuousOn.mono
      (((hL i).2.2.trans hfront).trans (K.convexHull_subset_space ht)))
  have hsub (i : δ) : g '' (L i).boundary ℝ ⊆ ⋃ c, P c := by
    intro x hx
    have hh := hLcover.subset (mem_iUnion.mpr ⟨i,hx⟩)
    exact hPcover.symm.subset ⟨image_mono hfront hh.2,hh.1⟩
  choose owner howner huniq using fun i =>
    (hLconn i).exists_unique_subset_finite_disjoint_closed P
      (fun c => (hC c).2.2.2.2.2.1.isClosed) hPdis (hsub i)
  have hlabel (i : δ) (c : γ) : g '' (L i).boundary ℝ ⊆ P c ↔ owner i = c := by
    constructor
    · intro h
      exact (huniq i c h).symm
    · rintro rfl
      exact howner i
  refine ⟨γ,δ,hγ,hδ,C,P,n,L,owner,hC,hPdis,hPcover,hL,hLdis,hlabel,?_,hPcomp⟩
  intro c
  apply Subset.antisymm
  · rintro x ⟨hxP,hxfront⟩
    have hxS := (hPcover.subset (mem_iUnion.mpr ⟨c,hxP⟩)).2
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hLcover.symm.subset ⟨hxS,hxfront⟩)
    have hic : owner i = c := by
      by_contra hn
      exact disjoint_left.mp (hPdis hn) (howner i hi) hxP
    exact mem_iUnion.mpr ⟨⟨i,hic⟩,hi⟩
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact ⟨(hlabel i c).mpr i.property hi,
      (hLcover.subset (mem_iUnion.mpr ⟨i,hi⟩)).2⟩

end PoincareConjecture.M76

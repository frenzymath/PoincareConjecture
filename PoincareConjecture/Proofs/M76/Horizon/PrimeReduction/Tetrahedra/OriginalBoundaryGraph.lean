import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalFaceArcModels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.FiniteIntervalUnion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalArcIncidence
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.IntervalUnionDegree
import PoincareConjecture.Proofs.M76.Mathlib.SimplexIntrinsicFrontier
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_tetrahedral_boundary_graph
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    {S : Set X}
    (havoid : Disjoint S (g '' K.vertices))
    (hposition : ∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) S g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4) :
    ∃ G : SimplicialComplex ℝ E, G.faces.Finite ∧
      (∀ a ∈ G.faces, a.card ≤ 2) ∧
      G.space ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∧
      g '' G.space = S ∩ (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) ∧
      (∀ a ∈ G.faces, ∃ s : K.FaceOfCard 3, s.1 ⊆ t ∧
        convexHull ℝ (a : Set E) ⊆ convexHull ℝ (s.1 : Set E)) ∧
      ∀ p : G.vertices, (G.vertexAbstractComplex.edgeGraph.neighborSet p).ncard = 2 := by
  classical
  let F := {s : K.FaceOfCard 3 // s.1 ⊆ t}
  let := K.finite_faceOfCard hK 3
  have hfacet (s : F) : convexHull ℝ (s.1.1 : Set E) ⊆
      intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) := by
    apply (K.indep ht).convexHull_subset_intrinsicFrontier
    exact Finset.ssubset_iff_subset_ne.mpr ⟨s.2, fun heq => by
      have h := congrArg Finset.card heq
      rw [s.1.2.2, ht4] at h
      omega⟩
  have hcover : intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) =
      ⋃ s : F, convexHull ℝ (s.1.1 : Set E) := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨v, hv, hxv⟩ := ((K.indep ht).mem_intrinsicFrontier_convexHull_finset
        (K.nonempty_of_mem_faces ht) x).mp hx
      have hc : (t.erase v).card = 3 := by rw [Finset.card_erase_of_mem hv, ht4]
      have hface : t.erase v ∈ K.faces := K.down_closed ht (Finset.erase_subset _ _)
        (Finset.card_pos.mp (by omega))
      exact mem_iUnion.mpr ⟨⟨⟨t.erase v, hface, hc⟩, Finset.erase_subset _ _⟩, hxv⟩
    · exact iUnion_subset hfacet
  choose γ hγ d r hdis hphysical hsub harcs using fun s : F =>
    (hposition s.1).exists_normal_arc_family_on_original_face K g hgi s.1.2.1
      (Q s.1) (A s.1) (hmap s.1) (hA s.1)
  let : ∀ s, Finite (γ s) := hγ
  let D : (Σ s, γ s) → Set E := fun z => d z.1 z.2
  let R : (Σ s, γ s) → Set E := fun z => r z.1 z.2
  obtain ⟨G, hG, hGs, hdim, hfaces⟩ := Set.exists_finite_interval_union_complex D R
    (fun z => (harcs z.1 z.2).1)
  have hDsub (z : Σ s, γ s) : D z ⊆ convexHull ℝ (z.1.1.1 : Set E) :=
    fun _ hx => hsub z.1 (mem_iUnion.mpr ⟨z.2, hx⟩)
  have hGF : G.space ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) := by
    rw [hGs]
    exact iUnion_subset (fun z => (hDsub z).trans (hfacet z.1))
  refine ⟨G, hG, hdim, hGF, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyF := hGF hy
      obtain ⟨z, hz⟩ := mem_iUnion.mp (hGs.subset hy)
      exact ⟨((hphysical z.1).subset
        ⟨y, mem_iUnion.mpr ⟨z.2, hz⟩, rfl⟩).1, mem_image_of_mem g hyF⟩
    · rintro ⟨hxS, y, hy, hyx⟩
      obtain ⟨s, hys⟩ := mem_iUnion.mp (hcover.subset hy)
      obtain ⟨z, hz, hzx⟩ := (hphysical s).symm.subset ⟨hxS, y, hys, hyx⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact ⟨z, hGs.symm.subset (mem_iUnion.mpr ⟨⟨s, i⟩, hi⟩), hzx⟩
  · intro a ha
    obtain ⟨z, hz⟩ := hfaces a ha
    exact ⟨z.1.1, z.1.2, hz.trans (hDsub z)⟩
  · obtain ⟨hi, he⟩ := original_normal_arc_incidence K g hgi havoid ht ht4 γ d r
      hdis hphysical hsub (fun s i => (harcs s i).2.1)
    exact interval_union_graph_degree_two D R (fun z => (harcs z.1 z.2).1)
      hi he G hG hdim hGs

end PoincareConjecture.M76

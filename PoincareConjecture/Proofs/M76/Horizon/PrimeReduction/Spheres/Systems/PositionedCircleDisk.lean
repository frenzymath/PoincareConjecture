import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.InnermostCircleDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NonreturningTriangleGraphPosition

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

theorem exists_positioned_sphere_system_face_circle_cap
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (K N : SimplicialComplex ℝ E) (hNK : N ≤ K)
    (g : E → X) (hgi : InjOn g K.space)
    {Z : Set X} (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target)
    (hphysicalGraph : Q.symm '' G.space = (⋃ i, S i) ∩
      (g '' convexHull ℝ (s : Set E)))
    (hSZ : Disjoint (⋃ i, S i) Z)
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (hcircle : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅) :
    ∃ (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (n : ℕ) (L : Polygon V3 (n + 3)) (D : Set V3) (i : κ),
      Function.Injective L ∧ L.HasSimplicialEdges ∧
      L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
      IsFinitePLBallPair P2 D (L.boundary ℝ) ∧ IsCompact D ∧
      D ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) ∧
      D ∩ G.space = L.boundary ℝ ∧
      IsCompact (Q.symm '' D) ∧
      Q.symm '' D ⊆ g '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∧
      Disjoint (Q.symm '' D) Z ∧
      Disjoint (Q.symm '' D) (⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
        g '' convexHull ℝ (a : Set E)) ∧
      (Q.symm '' D) ∩ (⋃ j, S j) = Q.symm '' L.boundary ℝ ∧
      Q.symm '' L.boundary ℝ ⊆ S i ∧
      (∀ j, Q.symm '' L.boundary ℝ ⊆ S j → j = i) := by
  classical
  obtain ⟨F, R, C, n, P, hRF, hi, hP, hPB, hball, hcompact, hDT, hexact⟩ :=
    exists_original_triangle_innermost_circle_disk K g hgi hs hs3 Q A hmap hA
      G hG hdim (hGT.trans inter_subset_left) hfinite hinterior hexterior hcircle
  let L := P.affineImage F.toAffineMap
  let D := F '' closure P.inside
  have hLB : L.boundary ℝ = F '' P.boundary ℝ := P.affineImage_boundary F.toAffineMap
  have hLi : Function.Injective L := hRF.injective.comp hi
  have hL : L.HasSimplicialEdges :=
    P.hasSimplicialEdges_affineImage hP F.toAffineMap hRF.injective
  have hLD : L.boundary ℝ ⊆ D := hLB.trans_subset hball.1
  have hTQ : convexHull ℝ (A '' (s : Set E)) ⊆ Q.target := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (A.toAffineMap.image_convexHull (s : Set E)).symm.subset hx
    change A u ∈ Q.target
    rw [← hA hu]
    exact Q.map_source (hmap hu)
  have hDQ : D ⊆ Q.target := (hDT.trans intrinsicInterior_subset).trans hTQ
  have hne (v : G.vertices) :
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    by_cases hv : (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))
    · rw [hinterior v hv]
      norm_num
    · rw [hexterior v hv]
      norm_num
  have hmembers (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      ∃! i, Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ S i := by
    simpa only [Homeomorph.refl_apply, id_eq, image_id'] using
      exists_unique_moved_sphere_member_of_graph_component S sS hdis
        (Homeomorph.refl X) Q G (hGT.trans inter_subset_right)
        (by simpa only [Homeomorph.refl_apply, id_eq, image_id'] using
          hphysicalGraph.subset.trans inter_subset_left) hne C
  have hsN : s ∉ N.faces := by
    intro hsN
    have hxG : L 0 ∈ G.space := (hexact.symm.subset
      (hLB.subset (L.vertex_mem_boundary 0))).2
    have hx := hphysicalGraph.subset (mem_image_of_mem Q.symm hxG)
    obtain ⟨u, hu, hux⟩ := hx.2
    exact disjoint_left.mp hSZ hx.1 (hux ▸
      (hmark u (K.convexHull_subset_space hs hu)).mpr
        (N.convexHull_subset_space hsN hu))
  have hDphys : IsCompact (Q.symm '' D) :=
    hcompact.image_of_continuousOn (Q.symm.continuousOn.mono hDQ)
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro u hu v hv huv
    exact hgi (K.convexHull_subset_space hs hu) (K.convexHull_subset_space hs hv)
      (Q.injOn (hmap hu) (hmap hv) ((hA hu).trans (huv.trans (hA hv).symm)))
  have hAsp := A.toAffineMap.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ _) (K.nonempty_of_mem_faces hs).to_set.convexHull hAi
  have hrel : intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) =
      A '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    change intrinsicInterior ℝ (convexHull ℝ (A.toAffineMap '' (s : Set E))) =
      A.toAffineMap '' intrinsicInterior ℝ (convexHull ℝ (s : Set E))
    rw [← A.toAffineMap.image_convexHull,
      A.toAffineMap.intrinsicInterior_image_of_injOn_span _ hAsp]
  have hphysical : Q.symm '' D ⊆ g '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hrel.subset (hDT hx)
    refine ⟨u, hu, ?_⟩
    rw [← hA (intrinsicInterior_subset hu)]
    exact (Q.left_inv (hmap (intrinsicInterior_subset hu))).symm
  have hDZ : Disjoint (Q.symm '' D) Z := by
    apply disjoint_left.mpr
    intro x hx hxZ
    obtain ⟨u, hu, rfl⟩ := hphysical hx
    exact hsN ((SimplicialComplex.mem_subcomplex_of_mem_intrinsicInterior_iff hNK hs hu).mp
      ((hmark u (K.convexHull_subset_space hs (intrinsicInterior_subset hu))).mp hxZ))
  have hDsk : Disjoint (Q.symm '' D) (⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 2),
      g '' convexHull ℝ (a : Set E)) := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxsk
    have hfront := original_skeleton_triangle_intersection_subset_boundary K g hgi hs hs3
      Q A hmap hA (intrinsicInterior_subset (hDT hx)) hxsk
    rw [← closure_sdiff_intrinsicInterior] at hfront
    exact hfront.2 (hDT hx)
  have hwhole : (Q.symm '' D) ∩ (⋃ j, S j) = Q.symm '' L.boundary ℝ := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxS⟩
      have hxp : Q.symm x ∈ g '' convexHull ℝ (s : Set E) :=
        (image_mono intrinsicInterior_subset) (hphysical (mem_image_of_mem Q.symm hx))
      obtain ⟨y, hyG, hyx⟩ := hphysicalGraph.symm.subset ⟨hxS, hxp⟩
      have hyx' := Q.symm.injOn (hGT hyG).2 (hDQ hx) hyx
      have hxG := hyx' ▸ hyG
      exact ⟨x, hLB.symm.subset (hexact.subset ⟨hx, hxG⟩), rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxD := hLD hx
      have hxG := (hexact.symm.subset (hLB.subset hx)).2
      exact ⟨⟨x, hxD, rfl⟩,
        (hphysicalGraph.subset (mem_image_of_mem Q.symm hxG)).1⟩
  obtain ⟨i, hiS, hiunique⟩ := hmembers C
  have hLC : L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) :=
    hLB.trans hPB
  refine ⟨C, n, L, D, i, hLi, hL, hLC, ?_, hcompact, hDT, ?_, hDphys,
    hphysical, hDZ, hDsk, hwhole, ?_, ?_⟩
  · rwa [hLB]
  · exact hexact.trans hLB.symm
  · rwa [hLC]
  · intro j hj
    exact hiunique j (by rwa [← hLC])

end PoincareConjecture.M76

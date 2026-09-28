import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalPolygonFacetPoint
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.CrossingInterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.PlanePairSignTransport

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem original_polygon_two_sided_accumulation
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {n : ℕ} (P : Polygon E (n + 3)) (hPi : Function.Injective P)
    (hPsub : P.boundary ℝ ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))
    (i : κ) (hPS : g '' P.boundary ℝ ⊆ S i) :
    ((g '' P.boundary ℝ) ∩
      closure (S i ∩ interior (g '' convexHull ℝ (t : Set E))) ∩
      closure (S i \ (g '' convexHull ℝ (t : Set E)))).Nonempty := by
  classical
  have hPT : g '' P.boundary ℝ ⊆ ⋃ j, S j := hPS.trans (subset_iUnion S i)
  obtain ⟨x,hx,s,hst,hxs⟩ := exists_original_polygon_facet_interior_point
    K hK g hgi hedges ht ht4 P hPi hPsub hPT
  have hxface := intrinsicInterior_subset hxs
  have hxQ := hmap s hxface
  have hxS := hPS ⟨x,hx,rfl⟩
  obtain ⟨W,hW,hxW,hWfront⟩ := exists_original_tetrahedron_facet_frontier_germ
    K hK g hg.continuousOn hgi ht ht4 s hst hxs
  obtain ⟨O,hO,hSO,hOS,_⟩ := exists_open_sphere_system_isolation S sS hdis i
  obtain ⟨G,_,hGT,_,hphysical,_,_,_,hcross,_,_⟩ := hposition s
  have hAhull : A s '' convexHull ℝ (s.1 : Set E) =
      convexHull ℝ (A s '' (s.1 : Set E)) := (A s).toAffineMap.image_convexHull _
  have hfacechart (y : X) (hy : y ∈ (Q s).source) :
      y ∈ g '' convexHull ℝ (s.1 : Set E) ↔
        Q s y ∈ convexHull ℝ (A s '' (s.1 : Set E)) := by
    rw [←hAhull]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z,hz,(hA s hz).symm⟩
    · rintro ⟨z,hz,hzy⟩
      exact ⟨z,hz,(Q s).injOn (hmap s hz) hy ((hA s hz).trans hzy)⟩
  have hxG : Q s (g x) ∈ G.space := by
    obtain ⟨z,hz,hzx⟩ := hphysical.symm.subset ⟨hPT ⟨x,hx,rfl⟩,x,hxface,rfl⟩
    have hzQ := (hGT hz).2
    rw [←hzx,(Q s).right_inv hzQ]
    exact hz
  have hAi : InjOn (A s) (convexHull ℝ (s.1 : Set E)) := by
    intro z hz w hw heq
    exact hgi (K.convexHull_subset_space s.2.1 hz) (K.convexHull_subset_space s.2.1 hw)
      ((Q s).injOn (hmap s hz) (hmap s hw) ((hA s hz).trans (heq.trans (hA s hw).symm)))
  have hAsp := (A s).toAffineMap.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ (s.1 : Set E))
    ((K.nonempty_of_mem_faces s.2.1).to_set.convexHull) hAi
  have hxint : Q s (g x) ∈ intrinsicInterior ℝ (convexHull ℝ (A s '' (s.1 : Set E))) := by
    have hAx : Q s (g x) = A s x := hA s hxface
    have hInt : intrinsicInterior ℝ (A s '' convexHull ℝ (s.1 : Set E)) =
        A s '' intrinsicInterior ℝ (convexHull ℝ (s.1 : Set E)) :=
      (A s).toAffineMap.intrinsicInterior_image_of_injOn_span _ hAsp
    rw [hAx,←hAhull,hInt]
    exact ⟨x,hxs,rfl⟩
  let U := (Q s).target ∩ (Q s).symm ⁻¹' (W ∩ O)
  have hU : IsOpen U := (Q s).symm.isOpen_inter_preimage (hW.inter hO)
  have hxU : Q s (g x) ∈ U := by
    refine ⟨(Q s).map_source hxQ,?_⟩
    change (Q s).symm (Q s (g x)) ∈ W ∩ O
    rw [(Q s).left_inv hxQ]
    exact ⟨hxW,hSO hxS⟩
  obtain ⟨B,hxB,hBU,hBx,_,_,hBS,hBF⟩ := hcross _ ⟨hxG,hxint⟩ U hU hxU
  let C := (Q s).trans B
  have hxC : g x ∈ C.source := ⟨hxQ,hxB⟩
  have hCx : C (g x) = 0 := hBx
  have hlocal (y : X) (hy : y ∈ C.source) : y ∈ W ∩ O := by
    have hh := (hBU hy.2).2
    change (Q s).symm (Q s y) ∈ W ∩ O at hh
    rwa [(Q s).left_inv hy.1] at hh
  have hCS (y : X) (hy : y ∈ C.source) : y ∈ S i ↔ (C y).2 = 0 := by
    have hmem : y ∈ S i ↔ y ∈ ⋃ j, S j :=
      ⟨fun h => mem_iUnion.mpr ⟨i,h⟩,fun h => hOS.subset ⟨(hlocal y hy).2,h⟩⟩
    have hh := hBS (Q s y) hy.2
    rw [(Q s).left_inv hy.1] at hh
    exact hmem.trans hh
  obtain ⟨ball⟩ := exists_chartwisePLBall_image
    (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
    (ContinuousLinearEquiv.refl ℝ V3) hg (K.convexHull_subset_space ht) hgi
  have hCF (y : X) (hy : y ∈ C.source) :
      y ∈ frontier (g '' convexHull ℝ (t : Set E)) ↔ (C y).1.1 = 0 := by
    rw [ball.frontier_eq]
    exact (hWfront y (hlocal y hy).1).trans
      ((hfacechart y hy.1).trans (hBF (Q s y) hy.2))
  have hreg : g x ∈ closure (interior (g '' convexHull ℝ (t : Set E))) := by
    rw [ball.closure_interior]
    exact ⟨x,convexHull_mono hst hxface,rfl⟩
  have hregOut : g x ∈ closure (interior (g '' convexHull ℝ (t : Set E))ᶜ) := by
    rw [ball.isCompact.isClosed.isOpen_compl.interior_eq,closure_compl]
    exact ((hCF _ hxC).mpr (by rw [hCx]; rfl)).2
  have hCFout (y : X) (hy : y ∈ C.source) :
      y ∈ frontier (g '' convexHull ℝ (t : Set E))ᶜ ↔ (C y).1.1 = 0 := by
    rw [frontier_compl]
    exact hCF y hy
  have hout := mem_closure_surface_interior_of_crossing_frontier
    C hxC hCx hCS hCFout hregOut
  rw [ball.isCompact.isClosed.isOpen_compl.interior_eq] at hout
  exact ⟨g x,⟨⟨x,hx,rfl⟩,
    mem_closure_surface_interior_of_crossing_frontier C hxC hCx hCS hCF hreg⟩,hout⟩

theorem original_polygon_inward_accumulation
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {n : ℕ} (P : Polygon E (n + 3)) (hPi : Function.Injective P)
    (hPsub : P.boundary ℝ ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))
    (i : κ) (hPS : g '' P.boundary ℝ ⊆ S i) :
    ((g '' P.boundary ℝ) ∩
      closure (S i ∩ interior (g '' convexHull ℝ (t : Set E)))).Nonempty := by
  obtain ⟨x,hx,_⟩ := original_polygon_two_sided_accumulation
    K hK g hg hgi Q A hmap hA S sS hdis hedges hposition ht ht4 P hPi hPsub i hPS
  exact ⟨x,hx⟩

end PoincareConjecture.M76

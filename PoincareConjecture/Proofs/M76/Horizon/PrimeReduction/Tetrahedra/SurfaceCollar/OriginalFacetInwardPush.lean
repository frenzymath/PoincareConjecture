import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalCrossingInwardPush
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalInwardCrossing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.PairedChartRestriction

set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_facet_inward_push
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s j, (e j).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (s : K.FaceOfCard 3) (hst : (s.1 : Set E) ⊆ t)
    {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (s.1 : Set E)))
    (i : κ) (hxS : g x ∈ S i) {O : Set X} (hO : IsOpen O) (hxO : g x ∈ O) :
    ∃ H : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id Oᶜ ∧ (∀ y, H y ∈ S i ↔ y ∈ S i) ∧
      (∀ y ∈ g '' convexHull ℝ (t : Set E),
        H y ∈ interior (g '' convexHull ℝ (t : Set E)) ∨ H y = y) ∧
      H (g x) ∈ interior (g '' convexHull ℝ (t : Set E)) := by
  classical
  have hxface := intrinsicInterior_subset hx
  have hxQ := hmap s hxface
  obtain ⟨W,hW,hxW,hWfront⟩ := exists_original_tetrahedron_facet_frontier_germ
    K hK g hg.continuousOn hgi ht ht4 s hst hx
  obtain ⟨N,hN,hSN,hNS,_⟩ := exists_open_sphere_system_isolation S sS hdis i
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
    obtain ⟨z,hz,hzx⟩ := hphysical.symm.subset
      ⟨mem_iUnion.mpr ⟨i,hxS⟩,x,hxface,rfl⟩
    rw [←hzx,(Q s).right_inv (hGT hz).2]
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
    exact ⟨x,hx,rfl⟩
  let U := (Q s).target ∩ (Q s).symm ⁻¹' (W ∩ N)
  have hU : IsOpen U := (Q s).symm.isOpen_inter_preimage (hW.inter hN)
  have hxU : Q s (g x) ∈ U := by
    refine ⟨(Q s).map_source hxQ,?_⟩
    change (Q s).symm (Q s (g x)) ∈ W ∩ N
    rw [(Q s).left_inv hxQ]
    exact ⟨hxW,hSN hxS⟩
  obtain ⟨B,hxB,hBU,hBx,hBPL,hBiPL,hBS,hBF⟩ := hcross _ ⟨hxG,hxint⟩ U hU hxU
  let T := B.trans crossingCoordinateOrder.toHomeomorph.toOpenPartialHomeomorph
  have hT : T ∈ piecewiseAffineGroupoid V3 :=
    ⟨(locallyPiecewiseAffineOn_affine crossingCoordinateOrder.toContinuousAffineMap
        isOpen_univ).comp hBPL,
      hBiPL.comp (locallyPiecewiseAffineOn_affine
        crossingCoordinateOrder.symm.toContinuousAffineMap isOpen_univ)⟩
  let C := (Q s).trans T
  have hxC : g x ∈ C.source := ⟨hxQ,hxB,mem_univ _⟩
  have hC (j : ι) : (e j).symm.trans C ∈ piecewiseAffineGroupoid V3 := by
    simpa only [OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid V3).trans (hQ s j) hT
  have hCx : C (g x) = 0 := by
    change crossingCoordinateOrder (B (Q s (g x))) = 0
    rw [hBx]
    ext j
    fin_cases j <;> rfl
  have hlocal (y : X) (hy : y ∈ C.source) : y ∈ W ∩ N := by
    have hh := (hBU hy.2.1).2
    change (Q s).symm (Q s y) ∈ W ∩ N at hh
    rwa [(Q s).left_inv hy.1] at hh
  have hCS (y : X) (hy : y ∈ C.source) : y ∈ S i ↔ C y 1 = 0 := by
    have hmem : y ∈ S i ↔ y ∈ ⋃ j, S j :=
      ⟨fun h => mem_iUnion.mpr ⟨i,h⟩,fun h => hNS.subset ⟨(hlocal y hy).2,h⟩⟩
    have hh := hBS (Q s y) hy.2.1
    rw [(Q s).left_inv hy.1] at hh
    exact hmem.trans hh
  obtain ⟨ball⟩ := exists_chartwisePLBall_image
    (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
    (ContinuousLinearEquiv.refl ℝ V3) hg (K.convexHull_subset_space ht) hgi
  have hCF (y : X) (hy : y ∈ C.source) :
      y ∈ frontier (g '' convexHull ℝ (t : Set E)) ↔ C y 0 = 0 := by
    rw [ball.frontier_eq]
    exact (hWfront y (hlocal y hy).1).trans
      ((hfacechart y hy.1).trans (hBF (Q s y) hy.2.1))
  exact exists_original_crossing_inward_push e he C hC ball.isCompact.isClosed
    ball.closure_interior hO hxC hCx hxO hCF hCS

end PoincareConjecture.M76

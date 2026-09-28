import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.CubePolygonAvoidance
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.InnermostDiskChart
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareConjecture.Proofs.M76.Triangulation.PLSpherePolygonCut
import PoincareConjecture.Proofs.M76.Triangulation.ConvexSphereLargeDisks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation









set_option autoImplicit false
open Set Geometry Metric
namespace Set
local notation "V3" => (Fin 3 → ℝ)

theorem IsFinitePLBallPair.exists_boundary_disk_containing_polygons
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    {B R : Set E} (hB : IsFinitePLBallPair V3 B R)
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hi : ∀ i, Function.Injective (P i))
    (hsub : ∀ i, (P i).boundary ℝ ⊆ R) :
    ∃ D q : Set E, IsFinitePLBallPair (ℝ × ℝ) D q ∧ D ⊆ R ∧
      (⋃ i, (P i).boundary ℝ) ⊆ D \ q := by
  classical
  obtain ⟨G,hG,hGb⟩ := hB.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  obtain ⟨_,K,_,_,hK,hKs⟩ := hB.exists_finite_carrier_and_rim_complexes
  let H := G.restrictSubsets hB.1 isClosed_closedBall.frontier_subset hGb
  have hH : H.IsFinitePL :=
    hG.restrictSubsets hB.1 isClosed_closedBall.frontier_subset hGb K hK hKs
  have hHcopy := hH
  obtain ⟨f,hf,hfval⟩ := hHcopy
  obtain ⟨g,hg,hgval⟩ := hH.symm
  have hgf : LeftInvOn g f R := by
    intro x hx
    rw [←hfval ⟨x,hx⟩,←hgval,H.symm_apply_apply]
  have hfg : LeftInvOn f g (frontier (closedBall (0 : V3) 1)) := by
    intro x hx
    rw [←hgval ⟨x,hx⟩,←hfval,H.apply_symm_apply]
  choose m Q hQi hQ hQB using fun i =>
    (P i).exists_polygon_finitePL_image (hP i) (hi i) hf
      (hsub i) (hgf.injOn.mono (hsub i))
  obtain ⟨v,hv,hvQ⟩ := PoincareConjecture.M76.exists_cube_frontier_point_avoiding_polygons m Q
  let a := ⋃ i, (P i).boundary ℝ
  have ha : IsCompact a := isCompact_iUnion (fun i => (P i).isCompact_boundary)
  have haR : a ⊆ R := iUnion_subset hsub
  have haf : IsCompact (f '' a) := ha.image_of_continuousOn (hf.continuousOn.mono haR)
  have hafsub : f '' a ⊆ frontier (closedBall (0 : V3) 1) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [←hfval ⟨x,haR hx⟩]
    exact (H ⟨x,haR hx⟩).property
  have hvfa : v ∉ f '' a := by
    rintro ⟨x,hx,hxv⟩
    obtain ⟨i,hxi⟩ := mem_iUnion.mp hx
    exact hvQ (mem_iUnion.mpr ⟨i,(hQB i).symm.subset ⟨x,hxi,hxv⟩⟩)
  have hgcopy := hg
  obtain ⟨J,hJ,hJs,_⟩ := hgcopy
  obtain ⟨d,q,hd,hds,had,_⟩ := J.exists_convex_frontier_disk_of_compact hJ
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hJs
    (F := ℝ × ℝ) (by simp [Module.finrank_prod]) ⟨v,hv⟩ haf hafsub hvfa
  refine ⟨g '' d,g '' q,hd.image_of_subset hg hds hfg.injOn,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    rw [←hgval ⟨x,hds hx⟩]
    exact (H.symm ⟨x,hds hx⟩).property
  · intro x hx
    have hfx := had (mem_image_of_mem f hx)
    refine ⟨⟨f x,hfx.1,hgf (haR hx)⟩,?_⟩
    rintro ⟨y,hy,hyx⟩
    have hfy := congrArg f hyx
    rw [hfg (hds (hd.1 hy))] at hfy
    exact hfx.2 (hfy ▸ hy)

theorem IsFinitePLBallPair.exists_innermost_boundary_polygon_disk
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι] [Nonempty ι]
    {B R : Set E} (hB : IsFinitePLBallPair V3 B R)
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, (P i).HasSimplicialEdges) (hi : ∀ i, Function.Injective (P i))
    (hsub : ∀ i, (P i).boundary ℝ ⊆ R)
    (hdis : Pairwise fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)) :
    ∃ i d, IsFinitePLBallPair (ℝ × ℝ) d ((P i).boundary ℝ) ∧
      d ⊆ R ∧ d ∩ (⋃ j, (P j).boundary ℝ) = (P i).boundary ℝ := by
  obtain ⟨D,q,hD,hDR,hPD⟩ := hB.exists_boundary_disk_containing_polygons n P hP hi hsub
  obtain ⟨i,d,hd,hds,hdP⟩ := hD.exists_innermost_polygon_disk n P hP hi
    (fun i => (subset_iUnion _ i).trans hPD) hdis
  exact ⟨i,d,hd,(hds.trans sdiff_subset).trans hDR,hdP⟩

end Set

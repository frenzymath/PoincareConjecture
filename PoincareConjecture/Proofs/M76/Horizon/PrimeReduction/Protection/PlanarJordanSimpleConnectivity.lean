import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FinitePLMarkedCycle
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonCycleLoopComparison
import PoincareConjecture.Proofs.M76.Mathlib.PolygonDisk
import PoincareConjecture.Proofs.M76.Mathlib.PolygonPreconnectedRegion
import PoincareConjecture.Proofs.M76.Mathlib.RelativeFinitePLApproximation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import PoincareConjecture.Proofs.M76.Mathlib.SubdivisionVertices
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Jordan.Domains











set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)

private theorem polygon_boundary_loop_null
    {U : Set P2} {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hPU : closure P.inside ⊆ U) :
    (P.boundaryLoop.map (continuous_inclusion
      ((P.isUnitBallPair_closed_inside hP hi).1.trans hPU))).Homotopic
      (Path.refl _) := by
  obtain ⟨H, _⟩ := P.exists_closed_inside_homeomorph_closedBall hP hi
  let : ContractibleSpace (closedBall (0 : P2) 1) := contractibleSpace_closedBall zero_le_one
  let : ContractibleSpace (closure P.inside) := H.contractibleSpace
  let rho := P.boundaryLoop.map (continuous_inclusion (P.isUnitBallPair_closed_inside hP hi).1)
  have hn : rho.Homotopic (Path.refl _) := SimplyConnectedSpace.paths_homotopic _ _
  exact hn.map (ContinuousMap.inclusion hPU)

private theorem geometric_cycle_null
    {U : Set P2} (hpoly : ∀ (n : ℕ) (P : Polygon P2 (n + 3)),
      P.HasSimplicialEdges → Function.Injective P → P.boundary ℝ ⊆ U → closure P.inside ⊆ U)
    (K : SimplicialComplex ℝ P2) (hKU : K.space ⊆ U)
    {v : K.vertices} (w : K.vertexAbstractComplex.edgeGraph.Walk v v) (hw : w.IsCycle) :
    ((K.geometricWalkPath w).map (continuous_inclusion hKU)).Homotopic
      (Path.refl _) := by
  classical
  obtain ⟨n, P, hlen, hv, hb, hi, hP, _, hPK⟩ := K.exists_polygon_of_geometric_cycle w hw
  have hcompare := (K.polygon_boundaryLoop_homotopic_geometricWalk
    w P hlen hv hb hPK).map (ContinuousMap.inclusion hKU)
  have hn := polygon_boundary_loop_null P hP hi (hpoly n P hP hi (hPK.trans hKU))
  apply hcompare.symm.trans
  have hbase : (inclusion hKU ⟨v, K.vertices_subset_space v.property⟩ : U) =
      inclusion ((P.isUnitBallPair_closed_inside hP hi).1.trans
        (hpoly n P hP hi (hPK.trans hKU))) ⟨P 0, P.vertex_mem_boundary 0⟩ :=
    Subtype.ext hb.symm
  have hn' := hn.pathCast hbase hbase
  have hr : (Path.refl _).cast hbase hbase = Path.refl _ := by
    apply Path.ext
    funext t
    exact hbase.symm
  rw [hr] at hn'
  exact hn'

theorem finitePL_loop_null_of_polygon_fillings
    {U : Set P2} (hpoly : ∀ (n : ℕ) (P : Polygon P2 (n + 3)),
      P.HasSimplicialEdges → Function.Injective P → P.boundary ℝ ⊆ U → closure P.inside ⊆ U)
    {f : ℝ → P2} (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1))
    (hc : f 1 = f 0) (hm : MapsTo f (Icc (0 : ℝ) 1) U) :
    ((Path.imageIntervalLoop f hf.continuousOn hc).map
      (continuous_inclusion (mapsTo_iff_image_subset.mp hm))).Homotopic (Path.refl _) := by
  classical
  let j : C(f '' Icc (0 : ℝ) 1, U) := ContinuousMap.inclusion (mapsTo_iff_image_subset.mp hm)
  let b := j ⟨f 0, mem_image_of_mem f (left_mem_Icc.mpr zero_le_one)⟩
  let rho := (Path.imageIntervalLoop f hf.continuousOn hc).map j.continuous
  by_contra hn
  have hout : (Path.refl b).whiskeredLoopClass rho ∉ (⊥ : Subgroup (FundamentalGroup U b)) := by
    intro hm
    apply hn
    have hh : (((Path.refl b).trans rho).trans (Path.refl b).symm).Homotopic
        (Path.refl b) := Path.Homotopic.Quotient.eq.mp (Subgroup.mem_bot.mp hm)
    exact ((Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans rho)).symm.trans hh
  obtain ⟨K, hKspace, G, hG, _, _, v, w, q, hw, hout⟩ :=
    hf.exists_excluded_marked_image_cycle hc j (Path.refl b) ⊥ hout
  have hKU : K.space ⊆ U := hKspace.subset.trans (mapsTo_iff_image_subset.mp hm)
  have hGeq : G = ContinuousMap.inclusion hKU := by
    apply ContinuousMap.ext
    intro x
    exact hG x
  subst G
  have hnull := geometric_cycle_null hpoly K hKU w hw
  apply hout
  rw [Subgroup.mem_bot]
  have heq : q.whiskeredLoopClass _ = q.whiskeredLoopClass (Path.refl _) :=
    congrArg FundamentalGroup.fromPath (Path.Homotopic.Quotient.eq.mpr
      (((Path.Homotopic.refl q).hcomp hnull).hcomp (Path.Homotopic.refl q.symm)))
  exact heq.trans (q.whiskeredLoopClass_refl)

theorem exists_based_finitePL_loop_approximation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {x : U} (p : Path x x) :
    ∃ (f : ℝ → E) (_hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1)),
      f 0 = x ∧ f 1 = x ∧
      ∀ t ∈ Icc (0 : ℝ) 1, segment ℝ (p.extend t : E) (f t) ⊆ U := by
  classical
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K₀, hK₀, hKI₀, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨K, hK, hKK₀, hPK⟩ := K₀.exists_finite_subdivision_with_vertices hK₀ {0, 1} (by
    rw [hKI₀]
    intro t ht
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl <;> norm_num)
  have hKI : K.space = Icc (0 : ℝ) 1 := hKK₀.space_eq.trans hKI₀
  let f : ℝ → E := fun t => (p.extend t : E)
  have hfc : Continuous f := continuous_subtype_val.comp p.continuous_extend
  have himage : IsCompact (f '' K.space) := (K.isCompact_space_of_finite hK).image hfc
  obtain ⟨eps, heps, hthick⟩ := himage.exists_thickening_subset_open hU (by
    rintro _ ⟨t, _, rfl⟩
    exact (p.extend t).property)
  have hempty : FinitePiecewiseAffineOn f ∅ := by
    refine ⟨⊥, Set.finite_empty, SimplicialComplex.space_bot, ?_⟩
    intro s hs
    exact (Set.notMem_empty s hs).elim
  obtain ⟨g, J, hJ, hJK, hg, hgv, _, herr⟩ :=
    K.exists_relative_finitePL_approximation hK hfc.continuousOn (empty_subset _) hempty heps
  have hg0 : g 0 = x := by
    rw [hgv (hJK.vertices_subset (hPK (by simp)))]
    exact congrArg Subtype.val p.extend_zero
  have hg1 : g 1 = x := by
    rw [hgv (hJK.vertices_subset (hPK (by simp)))]
    exact congrArg Subtype.val p.extend_one
  refine ⟨g, ⟨J, hJ, hJK.space_eq.trans hKI, hg⟩, hg0, hg1, ?_⟩
  intro t ht z hz
  have hball : segment ℝ (f t) (g t) ⊆ ball (f t) eps :=
    (convex_ball (f t) eps).segment_subset (mem_ball_self heps)
      (by simpa only [mem_ball, dist_eq_norm] using herr t (hKI.symm ▸ ht))
  exact hthick (mem_thickening_iff.mpr
    ⟨f t, mem_image_of_mem f (hKI.symm ▸ ht), hball hz⟩)

theorem loop_null_of_polygon_fillings
    {U : Set P2} (hU : IsOpen U)
    (hpoly : ∀ (n : ℕ) (P : Polygon P2 (n + 3)),
      P.HasSimplicialEdges → Function.Injective P → P.boundary ℝ ⊆ U → closure P.inside ⊆ U)
    {x : U} (p : Path x x) : p.Homotopic (Path.refl x) := by
  obtain ⟨f, hf, hf0, hf1, hseg⟩ := exists_based_finitePL_loop_approximation hU p
  have hm : MapsTo f (Icc (0 : ℝ) 1) U := fun t ht =>
    hseg t ht (right_mem_segment ℝ _ _)
  let q : Path x x := {
    toFun := fun t => ⟨f t, hm t.property⟩
    continuous_toFun := hf.continuousOn.domRestrict.subtype_mk _
    source' := Subtype.ext hf0
    target' := Subtype.ext hf1 }
  have hpq : p.Homotopic q := by
    refine ⟨{
      toFun := fun z => ⟨AffineMap.lineMap (p z.2 : P2) (q z.2 : P2) (z.1 : ℝ), ?_⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · apply hseg z.2 z.2.property
      rw [Path.extend_apply p z.2.property]
      exact lineMap_mem_segment ℝ (p z.2 : P2) (q z.2 : P2) z.1.property
    · apply Continuous.subtype_mk
      dsimp only [AffineMap.lineMap_apply]
      fun_prop
    · intro t; apply Subtype.ext; simp
    · intro t; apply Subtype.ext; simp
    · intro t a ha
      rcases ha with rfl | rfl <;> apply Subtype.ext <;> simp
  have hnull := finitePL_loop_null_of_polygon_fillings hpoly hf (hf1.trans hf0.symm) hm
  have hbase : x = (⟨f 0, hm (left_mem_Icc.mpr zero_le_one)⟩ : U) := Subtype.ext hf0.symm
  have hcast := hnull.pathCast hbase hbase
  have heq : ((Path.refl _).cast hbase hbase) = Path.refl x := by
    apply Path.ext; funext t; exact hbase.symm
  rw [heq] at hcast
  exact hpq.trans hcast

theorem polygon_inside_subset_of_connected_complement
    {U : Set P2} (hb : Bornology.IsBounded U) (hc : IsPreconnected Uᶜ)
    {n : ℕ} (P : Polygon P2 (n + 3)) (hP : P.HasSimplicialEdges)
    (hi : Function.Injective P) (hPU : P.boundary ℝ ⊆ U) : closure P.inside ⊆ U := by
  have hmeet : (Uᶜ ∩ P.outside).Nonempty := by
    by_contra hn
    have hsub : Uᶜ ⊆ closure P.inside := by
      rw [P.closure_inside hP hi]
      intro x hx hxo
      exact hn ⟨x, hx, hxo⟩
    have hbound := hb.union ((P.isCompact_closure_inside hP hi).isBounded.subset hsub)
    rw [union_compl_self] at hbound
    exact NormedSpace.unbounded_univ ℝ P2 hbound
  have hout : Uᶜ ⊆ P.outside := P.subset_outside_of_preconnected_inter hc
    (fun x hx hxP => hx (hPU hxP)) hmeet
  intro x hx
  by_contra hxU
  exact (P.closure_inside hP hi ▸ hx) (hout hxU)

theorem isSimplyConnected_of_bounded_open_connected_complement
    {U : Set P2} (hU : IsOpen U) (hconn : IsConnected U)
    (hb : Bornology.IsBounded U) (hc : IsPreconnected Uᶜ) : IsSimplyConnected U := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨isPathConnected_iff_pathConnectedSpace.mp
    (hU.isConnected_iff_isPathConnected.mp hconn), ?_⟩
  intro x p
  exact loop_null_of_polygon_fillings hU
    (fun _ P hP hi hPU => polygon_inside_subset_of_connected_complement hb hc P hP hi hPU) p

theorem isSimplyConnected_planar_region_of_connected_complement
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U) (hconn : IsConnected U)
    (hb : Bornology.IsBounded U) (hc : IsPreconnected Uᶜ) : IsSimplyConnected U := by
  let a : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] P2 := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have haU : IsOpen (a '' U) := a.toHomeomorph.isOpenMap _ hU
  have hac : IsConnected (a '' U) := hconn.image a a.continuous.continuousOn
  have hab : Bornology.IsBounded (a '' U) :=
    (hb.isCompact_closure.image a.continuous).isBounded.subset (image_mono subset_closure)
  have hacomp : IsPreconnected (a '' U)ᶜ := by
    change IsPreconnected (a.toHomeomorph '' U)ᶜ
    rw [← a.toHomeomorph.image_compl]
    exact hc.image a a.continuous.continuousOn
  exact a.toHomeomorph.isSimplyConnected_image.mp
    (isSimplyConnected_of_bounded_open_connected_complement haU hac hab hacomp)

theorem isSimplyConnected_bounded_jordan_side
    {U V S : Set (EuclideanSpace ℝ (Fin 2))}
    (hU : IsOpen U) (hconn : IsConnected U) (hb : Bornology.IsBounded U)
    (hVconn : IsConnected V) (hdis : Disjoint U V)
    (hcover : U ∪ V = Sᶜ) (hVfront : frontier V = S) : IsSimplyConnected U := by
  have hclV : closure V = Uᶜ :=
    closure_eq_compl_of_complementary_regions
      (hcover.symm.trans (union_comm _ _)) hdis.symm hVfront
  exact isSimplyConnected_planar_region_of_connected_complement hU hconn hb
    (hclV ▸ hVconn.closure.isPreconnected)

theorem exists_simplyConnected_jordan_domains
    {gamma : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2)}
    (hc : Continuous gamma) (hi : Function.Injective gamma) :
    ∃ U V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ IsOpen V ∧ IsSimplyConnected U ∧ IsPathConnected V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      Disjoint U V ∧ U ∪ V = (range gamma)ᶜ ∧
      frontier U = range gamma ∧ frontier V = range gamma ∧ IsCompact (closure U) := by
  obtain ⟨U, V, hU, hV, hUc, hVc, hUb, hVb, hdis, hcover, hUf, hVf, hK⟩ :=
    Poincare.Topology.Plane.Jordan.exists_complementary_domains hc hi
  exact ⟨U, V, hU, hV,
    isSimplyConnected_bounded_jordan_side hU hUc.isConnected hUb hVc.isConnected
      hdis hcover hVf, hVc, hUb, hVb, hdis, hcover, hUf, hVf, hK⟩

end PoincareConjecture.M76


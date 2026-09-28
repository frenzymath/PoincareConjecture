import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.RealChartEdgeIncidence
import PoincareConjecture.Proofs.M76.PrimeReduction.PureEdgeInterval
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PeriodCircleLoop
import Mathlib.Analysis.Convex.Contractible








set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex

theorem exists_polygon_of_homeomorph_circle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2) (H : K.space ≃ₜ Circle) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = K.space := by
  classical
  let : Nontrivial Circle := ⟨1,-1,by
    intro h
    have := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at this⟩
  let : Nontrivial K.space := H.toEquiv.nontrivial
  let : ConnectedSpace K.space := H.connectedSpace_iff.mpr inferInstance
  have hc := K.connected_edgeGraph_of_isConnected hK
    (isConnected_iff_connectedSpace.mpr inferInstance)
  let : Nonempty K.vertices := hc.nonempty
  let : Finite K.vertices := (K.finite_vertices_of_finite_faces hK).to_subtype
  let : Nontrivial K.vertices := by
    by_contra hn
    let : Subsingleton K.vertices := not_nontrivial_iff_subsingleton.mp hn
    let v : K.vertices := Classical.choice hc.nonempty
    have heq (x : K.space) : (x : E) = v := by
      obtain ⟨s,hs,hxs⟩ := mem_space_iff.mp x.property
      have hsub : (s : Set E) ⊆ {(v : E)} := by
        intro a ha
        have haK : a ∈ K.vertices := K.down_closed hs
          (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty a)
        exact congrArg Subtype.val (Subsingleton.elim (⟨a,haK⟩ : K.vertices) v)
      have := convexHull_mono hsub hxs
      simpa only [convexHull_singleton, mem_singleton_iff] using this
    obtain ⟨x,y,hxy⟩ := exists_pair_ne K.space
    exact hxy (Subtype.ext ((heq x).trans (heq y).symm))
  have hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 2 ∧ s ⊆ t := by
    intro s hs
    by_cases htwo : s.card = 2
    · exact ⟨s,hs,htwo,Finset.Subset.refl _⟩
    have hone : s.card = 1 := by
      have := hdim s hs
      have := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
      omega
    obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp hone
    let v : K.vertices := ⟨a,hs⟩
    obtain ⟨w,hw⟩ := hc.preconnected.exists_adj_of_nontrivial v
    have hne : a ≠ (w : E) := fun h => hw.1 (Subtype.ext h)
    have hedge := hw.2
    change ({v,w} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces at hedge
    have hedge' : ({a,(w : E)} : Finset E) ∈ K.faces := by
      simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype] using hedge
    exact ⟨{a,(w : E)},hedge',by simp [hne],by simp⟩
  have hdegree := K.neighbor_count_le_two_of_homeomorph_circle hK H
  have hnoleaf : ¬ ∃ v, (K.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1 := by
    intro hleaf
    obtain ⟨_,C,_,hC,hCne,e,_,_⟩ :=
      K.isFinitePLBallPair_of_pure_edges_with_leaf hK hpure hc hdegree hleaf
    let : ContractibleSpace C := hC.contractibleSpace (hCne.mono interior_subset)
    let : ContractibleSpace K.space := e.contractibleSpace
    let : SimplyConnectedSpace K.space := inferInstance
    let : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
    let a := H.trans (AddCircle.homeomorphCircle (show (1 : ℝ) ≠ 0 by norm_num)).symm
    have hSC : SimplyConnectedSpace (AddCircle (1 : ℝ)) := a.symm.toHomotopyEquiv.simplyConnectedSpace
    exact AddCircle.periodLoop_not_homotopic_refl 1
      ((simply_connected_iff_loops_nullhomotopic.mp hSC).2 0 (AddCircle.periodLoop 1))
  apply K.exists_polygon_of_pure_edges hK hpure hc
  intro v
  have hle := hdegree v
  obtain ⟨w,hw⟩ := hc.preconnected.exists_adj_of_nontrivial v
  have hpos : 0 < (K.vertexAbstractComplex.edgeGraph.neighborSet v).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨w,hw⟩
  have hne : (K.vertexAbstractComplex.edgeGraph.neighborSet v).ncard ≠ 1 :=
    fun h => hnoleaf ⟨v,h⟩
  omega

end Geometry.SimplicialComplex

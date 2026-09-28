import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Cuts
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Strips

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  {S : D.OrientedEdgeGraphSubdivision e R C a b}
  {dLeft dRight : EuclideanSpace ℝ (Fin 2)} (K : S.CutChain dLeft dRight)

noncomputable def CutChain.graphCuts (i : Fin S.count) :
    TransverseGraphCuts (S.piece i).lower
      ((S.piece i).parameter (S.cut i.castSucc)) ((S.piece i).parameter (S.cut i.succ))
      ((S.piece i).frame (K.direction i.castSucc)).1
      ((S.piece i).frame (K.direction i.castSucc)).2
      ((S.piece i).frame (K.direction i.succ)).1
      ((S.piece i).frame (K.direction i.succ)).2 :=
  Classical.choice (exists_transverseGraphCuts
    (S.piece i).parameter.open_target (S.piece i).lower_smooth
    (S.piece i).parameter.open_target (S.piece i).lower_smooth
    ((S.piece i).parameter_lt (S.cut_lt i))
    ((S.piece i).interval_target ⟨le_rfl, ((S.piece i).parameter_lt (S.cut_lt i)).le⟩)
    ((S.piece i).interval_target ⟨((S.piece i).parameter_lt (S.cut_lt i)).le, le_rfl⟩)
    (K.left_transverse i) (K.right_transverse i))

omit [T2Space M] in

theorem CutChain.exists_adjacent_strip_width (i j : Fin S.count) (hij : i.succ = j.castSucc) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ z w : ℝ, |z| < δ → |w| < δ →
        (t, z) ∈ ((S.piece i).strip (K.graphCuts i)).source ∧
        (s, w) ∈ ((S.piece j).strip (K.graphCuts j)).source ∧
        ((S.piece i).strip (K.graphCuts i) (t, z) =
          (S.piece j).strip (K.graphCuts j) (s, w) → t = 1 ∧ s = 0) := by
  let g := S.piece i
  let h := S.piece j
  have hcommon : g.frame.symm (g.parameter (S.cut i.succ), g.lower (g.parameter (S.cut i.succ))) =
      h.frame.symm (h.parameter (S.cut j.castSucc), h.lower (h.parameter (S.cut j.castSucc))) := by
    have hi := congrArg g.frame.symm (g.graph_coordinates (S.cut i.succ)
      (g.interval_source ⟨(S.cut_lt i).le, le_rfl⟩))
    have hj := congrArg h.frame.symm (h.graph_coordinates (S.cut j.castSucc)
      (h.interval_source ⟨le_rfl, (S.cut_lt j).le⟩))
    simp only [ContinuousLinearEquiv.symm_apply_apply, hij] at hi hj
    simpa only [hij] using hi.symm.trans hj
  have hbase : ∀ x ∈ Icc (g.parameter (S.cut i.castSucc)) (g.parameter (S.cut i.succ)),
      ∀ y ∈ Icc (h.parameter (S.cut j.castSucc)) (h.parameter (S.cut j.succ)),
        g.frame.symm (x, g.lower x) = h.frame.symm (y, h.lower y) →
          x = g.parameter (S.cut i.succ) ∧ y = h.parameter (S.cut j.castSucc) := by
    intro x hx y hy heq
    obtain ⟨u, hu, rfl⟩ := g.parameter_image.symm ▸ hx
    obtain ⟨v, hv, rfl⟩ := h.parameter_image.symm ▸ hy
    have hedge : (D.edge e.1 e.2).map u = (D.edge e.1 e.2).map v :=
      (g.graph_map u (g.interval_source hu)).trans
        ((congrArg C heq).trans (h.graph_map v (h.interval_source hv)).symm)
    have huv := D.edge_injective e.1 e.2 (Ioo_subset_Icc_self (S.piece_interval_unit i hu))
      (Ioo_subset_Icc_self (S.piece_interval_unit j hv)) hedge
    have hui : u = S.cut i.succ := le_antisymm hu.2 (by simpa only [huv, hij] using hv.1)
    have hvj : v = S.cut j.castSucc := by rw [← huv, hui, hij]
    exact ⟨congrArg g.parameter hui, congrArg h.parameter hvj⟩
  obtain ⟨r, hr, hseparate⟩ := exists_adjacent_linear_oblique_width
    (K.graphCuts i) (K.graphCuts j) g.frame.symm h.frame.symm
    g.parameter.open_target g.lower_smooth h.parameter.open_target h.lower_smooth
    (g.parameter_lt (S.cut_lt i)) g.interval_target
    (h.parameter_lt (S.cut_lt j)) h.interval_target hcommon
    (by simp [g, h, hij]) hbase
    (K.separator i j hij)
    (by simpa [g] using K.separator_zero i j hij)
    (K.separator_left_pos i j hij)
    (by simpa only [hij] using K.separator_right_pos i j hij)
  obtain ⟨r₁, hr₁, _, hsource₁⟩ := g.exists_strip_region_width (K.graphCuts i) (S.cut_lt i)
  obtain ⟨r₂, hr₂, _, hsource₂⟩ := h.exists_strip_region_width (K.graphCuts j) (S.cut_lt j)
  let δ := min r (min r₁ r₂)
  have hδ : 0 < δ := lt_min hr (lt_min hr₁ hr₂)
  refine ⟨δ, hδ, fun t ht s hs z w hz hw => ?_⟩
  have hz₁ := hz.trans_le ((min_le_right r (min r₁ r₂)).trans (min_le_left r₁ r₂))
  have hw₂ := hw.trans_le ((min_le_right r (min r₁ r₂)).trans (min_le_right r₁ r₂))
  have htC := (hsource₁ t ht z hz₁).1
  have hsC := (hsource₂ s hs w hw₂).1
  refine ⟨htC, hsC, fun heq => ?_⟩
  apply (hseparate t ht s hs z w (hz.trans_le (min_le_left _ _))
    (hw.trans_le (min_le_left _ _))).2.2
  exact C.injOn htC.2 hsC.2 heq

omit [T2Space M] in

theorem CutChain.exists_simultaneous_strip_width
    (bound : Fin S.count → ℝ) (hbound : ∀ i, 0 < bound i) :
    ∃ δ > 0,
      (∀ i, δ ≤ bound i ∧ δ ≤ (K.graphCuts i).radius ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, |z| < δ →
          (t, z) ∈ ((S.piece i).strip (K.graphCuts i)).source ∧
          ((S.piece i).strip (K.graphCuts i) (t, z) ∈
            chartDiskBoundaryUnion D.centers D.radius ↔ z = 0) ∧
          ((S.piece i).strip (K.graphCuts i) (t, z) ∈ connectedComponentIn
            (chartDiskBoundaryUnion D.centers D.radius)ᶜ R ↔ 0 < z) ∧
          (0 ≤ z → (S.piece i).strip (K.graphCuts i) (t, z) ∈ closure (connectedComponentIn
            (chartDiskBoundaryUnion D.centers D.radius)ᶜ R))) ∧
      ∀ (i j : Fin S.count), i.succ = j.castSucc →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
          ∀ z w : ℝ, |z| < δ → |w| < δ →
            (S.piece i).strip (K.graphCuts i) (t, z) =
              (S.piece j).strip (K.graphCuts j) (s, w) → t = 1 ∧ s = 0 := by
  classical
  have hwidth := fun i => (S.piece i).exists_strip_region_width (K.graphCuts i) (S.cut_lt i)
  choose width hpos hradius hregion using hwidth
  let Adjacent := {p : Fin S.count × Fin S.count // p.1.succ = p.2.castSucc}
  have hpairs := fun p : Adjacent => K.exists_adjacent_strip_width p.1.1 p.1.2 p.2
  choose pairWidth hpairPos hpair using hpairs
  let bounds : Fin S.count ⊕ Adjacent → ℝ :=
    Sum.elim (fun i => min (bound i) (width i)) pairWidth
  have hbounds : ∀ i, 0 < bounds i := by
    rintro (i | p)
    · exact lt_min (hbound i) (hpos i)
    · exact hpairPos p
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le_finite_family bounds hbounds
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro i
    have hδi : δ ≤ width i := (hle (Sum.inl i)).trans (min_le_right _ _)
    refine ⟨(hle (Sum.inl i)).trans (min_le_left _ _), hδi.trans (hradius i), ?_⟩
    exact fun t ht z hz => hregion i t ht z (hz.trans_le hδi)
  · intro i j hij t ht s hs z w hz hw heq
    let p : Adjacent := ⟨(i, j), hij⟩
    have hδp : δ ≤ pairWidth p := hle (Sum.inr p)
    exact (hpair p t ht s hs z w (hz.trans_le hδp) (hw.trans_le hδp)).2.2 heq

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition.OrientedEdgeGraphSubdivision

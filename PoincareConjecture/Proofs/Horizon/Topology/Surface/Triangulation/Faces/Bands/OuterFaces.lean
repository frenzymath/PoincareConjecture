import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.ObliqueFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.BoundaryContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff Matrix
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

namespace SmoothGraphBandPair

variable {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo hi : ℝ → ℝ} {a b : ℝ} {hab : a < b}
  (B : SmoothGraphBandPair F lo hi hab)

omit [T2Space M] in

theorem lower_top_vertex {z : M} (hz : z ∈ B.lower.carrier)
    (htop : (collarParameterEquiv (F.symm z)).2 =
      hi (collarParameterEquiv (F.symm z)).1) :
    z = F (collarParameterEquiv.symm (b, hi b)) := by
  rw [B.lower.carrier_eq_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [B.lower_source] at hw
  have hrect : w 0 ∈ Icc a b ∧ w 1 ∈ Icc (0 : ℝ) 1 := by
    change w ∈ {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc (0 : ℝ) 1}
    rw [← rectangle_triangle_union hab zero_lt_one]
    exact Or.inl hw
  have hband : collarParameterEquiv.symm (graphStripMap lo hi (collarParameterEquiv w)) ∈
      coordinateGraphBand lo hi a b := by
    change collarParameterEquiv
      (collarParameterEquiv.symm (graphStripMap lo hi (collarParameterEquiv w))) ∈
      {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1}
    rw [collarParameterEquiv.apply_symm_apply, ← graphStripMap_image_rectangle B.gap]
    exact ⟨collarParameterEquiv w, hrect, rfl⟩
  rw [B.lower_map, F.left_inv (B.band_subset_source hband),
    collarParameterEquiv.apply_symm_apply] at htop
  change lo (w 0) + w 1 * (hi (w 0) - lo (w 0)) = hi (w 0) at htop
  have hy : w 1 = 1 := by nlinarith [B.gap (w 0) hrect.1]
  have hcoord := (mem_rectangleLowerBasis_convexHull hab zero_lt_one w).mp hw
  simp only [sub_zero, div_one, hy] at hcoord
  have hx : w 0 = b := by
    have h := (le_div_iff₀ (sub_pos.mpr hab)).mp hcoord.2.1
    linarith [hrect.1.2]
  rw [B.lower_map]
  apply congrArg F
  apply congrArg collarParameterEquiv.symm
  change (w 0, lo (w 0) + w 1 * (hi (w 0) - lo (w 0))) = (b, hi b)
  simp [hx, hy]

omit [T2Space M] in

theorem upper_edge_image_eq_graph :
    (B.upper.boundary 0).map '' Icc (0 : ℝ) 1 =
      (fun t => F (collarParameterEquiv.symm (t, hi t))) '' Icc a b := by
  have hinterval : (fun t : ℝ => a + t * (b - a)) '' Icc (0 : ℝ) 1 = Icc a b := by
    have hc : Continuous (fun t : ℝ => a + t * (b - a)) := by fun_prop
    simpa using hc.continuousOn.image_Icc_of_monotoneOn
      (zero_le_one : (0 : ℝ) ≤ 1) (fun x _ y _ hxy => by nlinarith)
  rw [← hinterval, image_image]
  exact image_congr (fun t _ => B.upper_edge t)

end SmoothGraphBandPair

namespace ObliqueBandFaces

variable {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

private theorem affine_real_formula (f : ℝ →ᵃ[ℝ] ℝ) (x : ℝ) :
    f x = x * f.linear 1 + f 0 := by
  have hlin : f.linear x = x * f.linear 1 := by
    simpa using f.linear.map_smul x (1 : ℝ)
  simpa only [Pi.add_apply, hlin] using congrFun f.decomp x

private theorem affineIndependent_graph_off_graph (f : ℝ →ᵃ[ℝ] ℝ)
    {c d x y : ℝ} (hcd : c ≠ d) (hy : y ≠ f x) :
    AffineIndependent ℝ (![(c, f c), (d, f d), (x, y)] : Fin 3 → ℝ × ℝ) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hsum j
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hsum
  have hx := congrArg Prod.fst hsum
  have hy' := congrArg Prod.snd hsum
  simp [Fin.sum_univ_succ] at hw hx hy'
  have hnormal : w 2 * (y - f x) = 0 := by
    rw [affine_real_formula f c, affine_real_formula f d] at hy'
    rw [affine_real_formula f x]
    nlinarith [congrArg (fun r : ℝ => r * f.linear 1) hx,
      congrArg (fun r : ℝ => r * f 0) hw]
  have hw2 : w 2 = 0 := (mul_eq_zero.mp hnormal).resolve_right (sub_ne_zero.mpr hy)
  rw [hw2, zero_mul, add_zero] at hx
  rw [hw2, add_zero] at hw
  have hw1 : w 1 = 0 := by
    have hm : w 1 * (d - c) = 0 := by
      nlinarith [congrArg (fun r : ℝ => r * c) hw]
    exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hcd.symm)
  fin_cases j <;> simp_all

omit [T2Space M] in

theorem first_upper_line_avoids_lower_left :
    B.interface.piece B.firstCell a ≠ lo a := by
  let Q := B.interface
  let i := B.firstCell
  have hi : i.castSucc = 0 := rfl
  have hcell : Q.cut 0 ∈ Icc (Q.cut i.castSucc) (Q.cut i.succ) := by
    rw [hi]
    exact ⟨le_rfl, by simpa only [hi] using
      (Q.cut_strictMono (Fin.castSucc_lt_succ (i := i))).le⟩
  have hdom := Q.cell_subset_pieceDomain i hcell
  have hc : Q.cut 0 = a + ra * ua := Q.cut_first
  have hv : Q.piece i (Q.cut 0) = lo a + ra * wa := by
    have h := (Q.piece_endpoints i).1
    rw [hi] at h
    exact h.trans (congrArg Prod.snd Q.first_vertex)
  intro hbad
  change Q.piece i a = lo a at hbad
  have hua : ua ≠ 0 := by
    intro hu
    have hca : Q.cut 0 = a := by simpa only [hu, mul_zero, add_zero] using hc
    have h := (Q.piece_endpoints i).1
    rw [hi, hca, hbad] at h
    linarith [(Q.vertex_height_bounds 0).1]
  have hslope : ua * (Q.piece i).linear 1 = wa := by
    have heval := affine_real_formula (Q.piece i) (Q.cut 0)
    have ha := affine_real_formula (Q.piece i) a
    rw [hv, hc] at heval
    rw [hbad] at ha
    have hm : ra * (ua * (Q.piece i).linear 1 - wa) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left B.left_length_pos.ne')
  have hline (t : ℝ) : Q.piece i (a + t * ua) = lo a + t * wa := by
    have hm := congrArg (fun r : ℝ => t * r) hslope
    nlinarith [affine_real_formula (Q.piece i) (a + t * ua),
      affine_real_formula (Q.piece i) a]
  have hzero : (fun t : ℝ => Q.projection i (a + t * ua)) =ᶠ[𝓝 ra] fun _ => 0 := by
    filter_upwards [B.cuts.left.parameter.open_source.mem_nhds Q.left_parameter_mem] with t ht
    dsimp only [ObliquePolygonalBoundary.projection]
    rw [hline]
    have hh : lo a + t * wa - lo (a + t * ua) = B.cuts.left.parameter t :=
      (B.cuts.left.map_eq t).symm
    rw [hh]
    unfold obliqueProjection
    have hA : B.cuts.A (B.cuts.left.parameter t) = a + t * ua :=
      B.cuts.left.horizontal_parameter ht
    rw [hA]
    simp
  have hd : HasDerivAt (Q.projection i) (deriv (Q.projection i) (Q.cut 0)) (a + ra * ua) := by
    rw [← hc]
    exact (((Q.smooth_projection B.smooth_lower i) _ hdom).contDiffAt
      ((Q.isOpen_pieceDomain B.open_domain B.smooth_lower i).mem_nhds hdom)).differentiableAt
        (by simp) |>.hasDerivAt
  have hcomp := hd.comp ra (((hasDerivAt_id ra).mul_const ua).const_add a)
  have heq : deriv (Q.projection i) (Q.cut 0) * ua = 0 := by
    simpa only [one_mul] using
      hcomp.unique ((hasDerivAt_const ra (0 : ℝ)).congr_of_eventuallyEq hzero)
  exact (mul_ne_zero (Q.positive_deriv_projection B.open_domain B.smooth_lower i hcell).ne' hua) heq

omit [T2Space M] in

theorem first_upper_corner_affineIndependent :
    AffineIndependent ℝ (fun j : Fin 3 => collarParameterEquiv.symm
      (![(B.interface.cut 0, B.interface.piece B.firstCell (B.interface.cut 0)),
        (B.interface.cut B.firstCell.succ,
          B.interface.piece B.firstCell (B.interface.cut B.firstCell.succ)),
        (a, lo a)] j)) := by
  have hcd : B.interface.cut 0 ≠ B.interface.cut B.firstCell.succ :=
    (B.interface.cut_strictMono (Fin.castSucc_lt_succ (i := B.firstCell))).ne
  exact (affineIndependent_graph_off_graph (B.interface.piece B.firstCell) hcd
    B.first_upper_line_avoids_lower_left.symm).map'
      collarParameterEquiv.symm.toContinuousLinearMap.toLinearMap.toAffineMap
      collarParameterEquiv.symm.injective

noncomputable def firstUpperCornerBasis :
    AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Poincare.Topology.Plane.Meshes.affineBasisOfTriangle
    (fun j : Fin 3 => collarParameterEquiv.symm
      (![(B.interface.cut 0, B.interface.piece B.firstCell (B.interface.cut 0)),
        (B.interface.cut B.firstCell.succ,
          B.interface.piece B.firstCell (B.interface.cut B.firstCell.succ)),
        (a, lo a)] j)) B.first_upper_corner_affineIndependent

omit [T2Space M] in
theorem firstUpperCornerBasis_zero : B.firstUpperCornerBasis 0 =
    collarParameterEquiv.symm
      (B.interface.cut 0, lo (B.interface.cut 0) + B.interface.height 0) := by
  change collarParameterEquiv.symm
      (B.interface.cut 0, B.interface.piece B.firstCell (B.interface.cut 0)) = _
  have h := (B.interface.piece_endpoints B.firstCell).1
  have hfirst : B.firstCell.castSucc = 0 := rfl
  rw [hfirst] at h
  rw [h]

omit [T2Space M] in
theorem firstUpperCornerBasis_one : B.firstUpperCornerBasis 1 =
    collarParameterEquiv.symm (B.interface.cut B.firstCell.succ,
      lo (B.interface.cut B.firstCell.succ) + B.interface.height B.firstCell.succ) := by
  change collarParameterEquiv.symm (B.interface.cut B.firstCell.succ,
      B.interface.piece B.firstCell (B.interface.cut B.firstCell.succ)) = _
  rw [(B.interface.piece_endpoints B.firstCell).2]

omit [T2Space M] in
@[simp] theorem firstUpperCornerBasis_two :
    B.firstUpperCornerBasis 2 = collarParameterEquiv.symm (a, lo a) := rfl

omit [T2Space M] in

theorem first_upper_edge_image_eq_corner_side :
    ((B.pair B.firstCell).upper.boundary 0).map '' Icc (0 : ℝ) 1 =
      F '' segment ℝ (B.firstUpperCornerBasis 0) (B.firstUpperCornerBasis 1) := by
  rw [B.upper_edge_image, B.firstUpperCornerBasis_zero, B.firstUpperCornerBasis_one]
  have hlinear := image_segment ℝ
    collarParameterEquiv.symm.toContinuousLinearMap.toLinearMap.toAffineMap
    (B.interface.cut 0, lo (B.interface.cut 0) + B.interface.height 0)
    (B.interface.cut B.firstCell.succ,
      lo (B.interface.cut B.firstCell.succ) + B.interface.height B.firstCell.succ)
  simpa [image_image, LinearMap.toAffineMap, firstCell] using congrArg (fun S => F '' S) hlinear

omit [T2Space M] in

theorem leftCut_eq_corner_side :
    B.leftCut = F '' segment ℝ (B.firstUpperCornerBasis 0) (B.firstUpperCornerBasis 2) := by
  rw [B.firstUpperCornerBasis_zero, B.firstUpperCornerBasis_two, B.interface.first_vertex]
  unfold leftCut
  have hlinear := image_segment ℝ
    collarParameterEquiv.symm.toContinuousLinearMap.toLinearMap.toAffineMap
    (a + ra * ua, lo a + ra * wa) (a, lo a)
  rw [segment_symm ℝ (a, lo a) (a + ra * ua, lo a + ra * wa)]
  simpa [image_image, LinearMap.toAffineMap] using congrArg (fun S => F '' S) hlinear

omit [T2Space M] in
private theorem outer_coordinates_of_not_interior {q : EuclideanSpace ℝ (Fin 2)}
    (hq : q ∈ B.band) (hout : B.coordinates q ∉ interior B.carrier) :
    (collarParameterEquiv q).1 = 0 ∨ (collarParameterEquiv q).1 = 1 ∨
      (collarParameterEquiv q).2 = 0 ∨
      (collarParameterEquiv q).2 = B.height (collarParameterEquiv q).1 := by
  have h := hq
  rw [B.band_eq_subgraph] at h
  by_contra! hn
  exact hout (B.openBand_image_subset_interior ⟨q,
    ⟨⟨lt_of_le_of_ne h.1.1 hn.1.symm, lt_of_le_of_ne h.1.2 hn.2.1⟩,
      lt_of_le_of_ne h.2.1 hn.2.2.1.symm,
      lt_of_le_of_ne h.2.2 hn.2.2.2⟩, rfl⟩)

omit [T2Space M] in
private theorem cell_eq_first_of_zero {i : Fin B.interface.count}
    (ht : (0 : ℝ) ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) : i = B.firstCell := by
  have hz : B.cut i.castSucc = B.cut 0 := by
    rw [B.cut_first]
    exact le_antisymm ht.1 (by simpa using B.cut_strictMono.monotone (Fin.zero_le i.castSucc))
  have hi := congrArg Fin.val (B.cut_strictMono.injective hz)
  exact Fin.ext hi

omit [T2Space M] in
private theorem cell_eq_last_of_one {i : Fin B.interface.count}
    (ht : (1 : ℝ) ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) : i = B.lastCell := by
  have ho : B.cut i.succ = B.cut (Fin.last B.interface.count) := by
    rw [B.cut_last]
    exact le_antisymm (by simpa using B.cut_strictMono.monotone (Fin.le_last i.succ)) ht.2
  have hi := congrArg Fin.val (B.cut_strictMono.injective ho)
  apply Fin.ext
  dsimp [lastCell]
  simp only [Fin.val_succ, Fin.val_last] at hi
  omega

omit [T2Space M] in
private theorem lower_coordinate_mem_arc {q : EuclideanSpace ℝ (Fin 2)}
    (hq : q ∈ B.band) (hz : (collarParameterEquiv q).2 = 0) :
    B.coordinates q ∈ B.lowerArc := by
  have h := hq
  rw [B.band_eq_subgraph] at h
  have hab : a < b := by
    simpa only [B.cuts.A_zero, B.cuts.B_zero] using B.cuts.separated 0
      ⟨by linarith [B.cuts.radius_pos], B.cuts.radius_pos⟩
  refine ⟨a + (collarParameterEquiv q).1 * (b - a), ?_, ?_⟩
  · constructor <;> nlinarith [h.1.1, h.1.2]
  · dsimp only
    rw [← B.coordinates_bottom]
    congr 1
    apply collarParameterEquiv.injective
    simp only [collarParameterEquiv.apply_symm_apply]
    exact Prod.ext rfl hz.symm

omit [T2Space M] in
private theorem right_coordinate_mem_cut {q : EuclideanSpace ℝ (Fin 2)}
    (hq : q ∈ B.band) (hx : (collarParameterEquiv q).1 = 1) :
    B.coordinates q ∈ B.rightCut := by
  have h := hq
  rw [B.band_eq_subgraph] at h
  rw [← B.right_height_image]
  refine ⟨(collarParameterEquiv q).2, ?_, ?_⟩
  · simpa only [hx, mem_Icc] using h.2
  · apply congrArg B.coordinates
    apply collarParameterEquiv.injective
    rw [collarParameterEquiv.apply_symm_apply]
    exact Prod.ext hx.symm rfl

omit [T2Space M] in
private theorem left_coordinate_mem_cut {q : EuclideanSpace ℝ (Fin 2)}
    (hq : q ∈ B.band) (hx : (collarParameterEquiv q).1 = 0) :
    B.coordinates q ∈ B.leftCut := by
  have h := hq
  rw [B.band_eq_subgraph] at h
  rw [← B.left_height_image]
  refine ⟨(collarParameterEquiv q).2, ?_, ?_⟩
  · simpa only [hx, mem_Icc] using h.2
  · apply congrArg B.coordinates
    apply collarParameterEquiv.injective
    rw [collarParameterEquiv.apply_symm_apply]
    exact Prod.ext hx.symm rfl

omit [T2Space M] in

theorem lower_carrier_inter_subset_outer {C : Set M}
    (hinterior : Disjoint C (interior B.carrier)) (hlower : Disjoint C B.lowerArc)
    (i : Fin B.interface.count) :
    C ∩ (B.pair i).lower.carrier ⊆
      {B.vertex (i.succ, true)} ∪ (if i = B.lastCell then B.rightCut else ∅) := by
  classical
  rintro z ⟨hzC, hz⟩
  have hzB : z ∈ B.carrier := mem_iUnion.mpr ⟨(i, false), hz⟩
  rw [B.carrier_eq_image] at hzB
  obtain ⟨q, hq, rfl⟩ := hzB
  have hsource := B.band_subset_source hq
  have hp := (B.pair i).parameter_mem (i := false) hz
  rw [B.coordinates.left_inv hsource] at hp
  have hnot : B.coordinates q ∉ interior B.carrier := disjoint_left.mp hinterior hzC
  rcases B.outer_coordinates_of_not_interior hq hnot with hzero | hone | hbottom | htop
  · have hi : i = B.firstCell := B.cell_eq_first_of_zero (by simpa only [hzero] using hp.1)
    have hleft : (collarParameterEquiv q).1 = B.cut i.castSucc := by
      rw [hi, hzero]
      exact B.cut_first.symm
    have heq := (B.pair i).lower_left_vertex hz
      (by simpa only [B.coordinates.left_inv hsource] using hleft)
    have hqzero : (collarParameterEquiv q).2 = 0 := by
      have h := congrArg (fun z => collarParameterEquiv (B.coordinates.symm z)) heq
      rw [B.coordinates.left_inv hsource] at h
      have hs : collarParameterEquiv.symm (B.cut i.castSucc, 0) ∈ B.coordinates.source :=
        (B.pair i).band_subset_source (by
          simp only [coordinateGraphBand, mem_preimage, collarParameterEquiv.apply_symm_apply,
            mem_ofPred_eq, mem_Icc]
          exact ⟨⟨le_rfl, (B.cut_strictMono Fin.castSucc_lt_succ).le⟩, le_rfl,
            ((B.pair i).gap _ ⟨le_rfl, (B.cut_strictMono Fin.castSucc_lt_succ).le⟩).le⟩)
      rw [B.coordinates.left_inv hs, collarParameterEquiv.apply_symm_apply] at h
      exact congrArg Prod.snd h
    exact False.elim (disjoint_left.mp hlower hzC (B.lower_coordinate_mem_arc hq hqzero))
  · have hi : i = B.lastCell := B.cell_eq_last_of_one (by simpa only [hone] using hp.1)
    exact Or.inr (by rw [if_pos hi]; exact B.right_coordinate_mem_cut hq hone)
  · exact False.elim (disjoint_left.mp hlower hzC (B.lower_coordinate_mem_arc hq hbottom))
  · have htop' : (collarParameterEquiv (B.coordinates.symm (B.coordinates q))).2 =
        B.upperGraph i (collarParameterEquiv (B.coordinates.symm (B.coordinates q))).1 := by
      rw [B.coordinates.left_inv hsource, ← B.height_eq_upperGraph hp.1]
      exact htop
    have heq := (B.pair i).lower_top_vertex hz htop'
    exact Or.inl (by
      rw [mem_singleton_iff, heq]
      simp [vertex, (B.upperGraph_endpoints i).2])

omit [T2Space M] in

theorem upper_carrier_inter_subset_outer {C : Set M}
    (hinterior : Disjoint C (interior B.carrier)) (hlower : Disjoint C B.lowerArc)
    (i : Fin B.interface.count) :
    C ∩ (B.pair i).upper.carrier ⊆
      ((B.pair i).upper.boundary 0).map '' Icc (0 : ℝ) 1 ∪
        (if i = B.firstCell then B.leftCut else ∅) := by
  classical
  rintro z ⟨hzC, hz⟩
  have hzB : z ∈ B.carrier := mem_iUnion.mpr ⟨(i, true), hz⟩
  rw [B.carrier_eq_image] at hzB
  obtain ⟨q, hq, rfl⟩ := hzB
  have hsource := B.band_subset_source hq
  have hp := (B.pair i).parameter_mem (i := true) hz
  rw [B.coordinates.left_inv hsource] at hp
  have hnot : B.coordinates q ∉ interior B.carrier := disjoint_left.mp hinterior hzC
  rcases B.outer_coordinates_of_not_interior hq hnot with hzero | hone | hbottom | htop
  · have hi : i = B.firstCell := B.cell_eq_first_of_zero (by simpa only [hzero] using hp.1)
    exact Or.inr (by rw [if_pos hi]; exact B.left_coordinate_mem_cut hq hzero)
  · have hcutright : B.cut i.succ = 1 :=
      le_antisymm (by simpa using B.cut_strictMono.monotone (Fin.le_last i.succ))
        (by simpa only [hone] using hp.1.2)
    have hright : (collarParameterEquiv q).1 = B.cut i.succ := by
      rw [hcutright, hone]
    have heq := (B.pair i).upper_right_vertex hz
      (by simpa only [B.coordinates.left_inv hsource] using hright)
    left
    rw [(B.pair i).upper_edge_image_eq_graph, heq]
    exact mem_image_of_mem _ ⟨(B.cut_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
  · exact False.elim (disjoint_left.mp hlower hzC (B.lower_coordinate_mem_arc hq hbottom))
  · left
    rw [(B.pair i).upper_edge_image_eq_graph]
    refine ⟨(collarParameterEquiv q).1, hp.1, ?_⟩
    apply congrArg B.coordinates
    apply collarParameterEquiv.injective
    rw [collarParameterEquiv.apply_symm_apply]
    refine Prod.ext rfl ?_
    exact (B.height_eq_upperGraph hp.1).symm.trans htop.symm

omit [T2Space M] in

theorem upper_carrier_inter_subset_upper_edge {C : Set M}
    (hinterior : Disjoint C (interior B.carrier)) (hlower : Disjoint C B.lowerArc)
    {i : Fin B.interface.count} (hi : i ≠ B.firstCell) :
    C ∩ (B.pair i).upper.carrier ⊆
      ((B.pair i).upper.boundary 0).map '' Icc (0 : ℝ) 1 := by
  simpa only [if_neg hi, union_empty] using B.upper_carrier_inter_subset_outer hinterior hlower i

omit [T2Space M] in

theorem lower_carrier_inter_subset_vertex {C : Set M}
    (hinterior : Disjoint C (interior B.carrier)) (hlower : Disjoint C B.lowerArc)
    {i : Fin B.interface.count} (hi : i ≠ B.lastCell) :
    C ∩ (B.pair i).lower.carrier ⊆ {B.vertex (i.succ, true)} := by
  simpa only [if_neg hi, union_empty] using B.lower_carrier_inter_subset_outer hinterior hlower i

omit [T2Space M] in
theorem last_top_vertex_mem_rightCut : B.vertex (B.lastCell.succ, true) ∈ B.rightCut := by
  have hlast : B.lastCell.succ = Fin.last B.interface.count := by
    apply Fin.ext
    dsimp [lastCell]
    have hn := B.interface.count_pos
    omega
  change B.coordinates (collarParameterEquiv.symm
    (B.cut B.lastCell.succ, B.interface.height B.lastCell.succ)) ∈ B.rightCut
  rw [hlast, B.cut_last, ← B.right_height_image]
  refine ⟨B.interface.height (Fin.last B.interface.count), ⟨?_, ?_⟩, rfl⟩
  · exact (B.interface.vertex_height_bounds (Fin.last B.interface.count)).1.le
  · rw [B.height_one, B.interface.height_last]

omit [T2Space M] in

theorem last_lower_carrier_inter_subset_rightCut {C : Set M}
    (hinterior : Disjoint C (interior B.carrier)) (hlower : Disjoint C B.lowerArc) :
    C ∩ (B.pair B.lastCell).lower.carrier ⊆ B.rightCut := by
  have h := B.lower_carrier_inter_subset_outer hinterior hlower B.lastCell
  apply h.trans
  exact union_subset (singleton_subset_iff.mpr B.last_top_vertex_mem_rightCut) (by simp)

omit [T2Space M] in

theorem first_upper_carrier_inter_subset_corner_sides {C : Set M}
    (hinterior : Disjoint C (interior B.carrier)) (hlower : Disjoint C B.lowerArc) :
    C ∩ (B.pair B.firstCell).upper.carrier ⊆ F ''
      (segment ℝ (B.firstUpperCornerBasis 0) (B.firstUpperCornerBasis 1) ∪
        segment ℝ (B.firstUpperCornerBasis 0) (B.firstUpperCornerBasis 2)) := by
  have h := B.upper_carrier_inter_subset_outer hinterior hlower B.firstCell
  simpa [B.first_upper_edge_image_eq_corner_side,
    B.leftCut_eq_corner_side, image_union] using h

theorem corner_sides_image_subset_first_upper_carrier :
    F '' (segment ℝ (B.firstUpperCornerBasis 0) (B.firstUpperCornerBasis 1) ∪
      segment ℝ (B.firstUpperCornerBasis 0) (B.firstUpperCornerBasis 2)) ⊆
      (B.pair B.firstCell).upper.carrier := by
  have hleft : ((B.pair B.firstCell).upper.boundary 2).map '' Icc (0 : ℝ) 1 =
      B.leftCut := B.left_edge_image
  rw [image_union, ← B.first_upper_edge_image_eq_corner_side,
    ← B.leftCut_eq_corner_side, ← hleft]
  apply union_subset
  · exact ((B.pair B.firstCell).upper.boundary_image_subset_frontier 0).trans
      (B.pair B.firstCell).upper.isClosed_carrier.frontier_subset
  · exact ((B.pair B.firstCell).upper.boundary_image_subset_frontier 2).trans
      (B.pair B.firstCell).upper.isClosed_carrier.frontier_subset

end ObliqueBandFaces
end PoincareConjecture.Topology.Surface

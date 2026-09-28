


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Oblique
import Mathlib.Topology.LocallyFinite









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Matrix
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

omit [T2Space M] in
theorem upperGraphs_eq_on_overlap {i j : Fin B.interface.count} {t : ℝ}
    (hi : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ))
    (hj : t ∈ Icc (B.cut j.castSucc) (B.cut j.succ)) :
    B.upperGraph i t = B.upperGraph j t := by
  have hordered {i j : Fin B.interface.count} (hij : i < j)
      (hi : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ))
      (hj : t ∈ Icc (B.cut j.castSucc) (B.cut j.succ)) :
      B.upperGraph i t = B.upperGraph j t := by
    have hle : i.succ ≤ j.castSucc := by
      change (i : ℕ) + 1 ≤ j
      exact hij
    have hcuts : B.cut i.succ = B.cut j.castSucc :=
      le_antisymm (B.cut_strictMono.monotone hle) (hj.1.trans hi.2)
    have he : i.succ = j.castSucc := B.cut_strictMono.injective hcuts
    have ht : t = B.cut i.succ := le_antisymm hi.2 (hcuts.symm ▸ hj.1)
    rw [ht, (B.upperGraph_endpoints i).2, he, (B.upperGraph_endpoints j).1]
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hordered hij hi hj
  · subst j
    rfl
  · exact (hordered hij hj hi).symm


noncomputable def height (t : ℝ) : ℝ :=
  if h : ∃ i : Fin B.interface.count, t ∈ Icc (B.cut i.castSucc) (B.cut i.succ)
    then B.upperGraph h.choose t else 0

omit [T2Space M] in
theorem height_eq_upperGraph {i : Fin B.interface.count} {t : ℝ}
    (ht : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) : B.height t = B.upperGraph i t := by
  have h : ∃ j : Fin B.interface.count, t ∈ Icc (B.cut j.castSucc) (B.cut j.succ) := ⟨i, ht⟩
  rw [height, dif_pos h]
  exact B.upperGraphs_eq_on_overlap h.choose_spec ht

omit [T2Space M] in
theorem continuousOn_height : ContinuousOn B.height (Icc (0 : ℝ) 1) := by
  rw [← B.cut_interval_cover]
  apply (locallyFinite_of_finite _).continuousOn_iUnion (fun _ => isClosed_Icc)
  intro i
  let G := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
  apply ((G.smooth_upperGraph B.smooth_lower).continuousOn.mono
    (fun _ ht => G.parameter_mem_target ht)).congr
  intro t ht
  exact B.height_eq_upperGraph ht

omit [T2Space M] in
theorem height_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 0 < B.height t := by
  rw [← B.cut_interval_cover] at ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  rw [B.height_eq_upperGraph hi]
  exact ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).upperGraph_bounds hi).1

omit [T2Space M] in
theorem band_eq_subgraph : B.band =
    {q : EuclideanSpace ℝ (Fin 2) | (collarParameterEquiv q).1 ∈ Icc (0 : ℝ) 1 ∧
      0 ≤ (collarParameterEquiv q).2 ∧ (collarParameterEquiv q).2 ≤ B.height (collarParameterEquiv q).1} := by
  ext q
  constructor
  · intro hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    refine ⟨?_, hi.2.1, ?_⟩
    · rw [← B.cut_interval_cover]
      exact mem_iUnion.mpr ⟨i, hi.1⟩
    · rw [B.height_eq_upperGraph hi.1]
      exact hi.2.2
  · intro hq
    have ht := hq.1
    rw [← B.cut_interval_cover] at ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    refine mem_iUnion.mpr ⟨i, hi, hq.2.1, ?_⟩
    rw [← B.height_eq_upperGraph hi]
    exact hq.2.2

omit [T2Space M] in
theorem band_subset_source : B.band ⊆ B.coordinates.source := by
  intro q hq
  obtain ⟨i, hi⟩ := mem_iUnion.mp hq
  exact (B.pair i).band_subset_source hi


def carrier : Set M := ⋃ i, (B.face i).carrier

omit [T2Space M] in
theorem carrier_eq_image : B.carrier = B.coordinates '' B.band := B.cover

theorem isClosed_carrier : IsClosed B.carrier :=
  isClosed_iUnion_of_finite fun i => (B.face i).isClosed_carrier

omit [T2Space M] in
theorem carrier_subset_target : B.carrier ⊆ B.coordinates.target := by
  rw [B.carrier_eq_image]
  rintro _ ⟨q, hq, rfl⟩
  exact B.coordinates.map_source (B.band_subset_source hq)

omit [T2Space M] in
theorem mem_carrier_iff {z : M} (hz : z ∈ B.coordinates.target) :
    z ∈ B.carrier ↔ B.coordinates.symm z ∈ B.band := by
  rw [B.carrier_eq_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rwa [B.coordinates.left_inv (B.band_subset_source hq)]
  · intro hq
    exact ⟨B.coordinates.symm z, hq, B.coordinates.right_inv hz⟩


def openBand : Set (EuclideanSpace ℝ (Fin 2)) :=
  {q | (collarParameterEquiv q).1 ∈ Ioo (0 : ℝ) 1 ∧
    0 < (collarParameterEquiv q).2 ∧ (collarParameterEquiv q).2 < B.height (collarParameterEquiv q).1}

omit [T2Space M] in
theorem isOpen_openBand : IsOpen B.openBand := by
  let D : Set (EuclideanSpace ℝ (Fin 2)) := {q | (collarParameterEquiv q).1 ∈ Ioo (0 : ℝ) 1}
  have hD : IsOpen D := isOpen_Ioo.preimage (continuous_fst.comp collarParameterEquiv.continuous)
  have hH : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 2) =>
      B.height (collarParameterEquiv q).1 - (collarParameterEquiv q).2) D :=
    (B.continuousOn_height.comp (continuous_fst.comp collarParameterEquiv.continuous).continuousOn
      (fun _ hq => ⟨hq.1.le, hq.2.le⟩)).sub
        (continuous_snd.comp collarParameterEquiv.continuous).continuousOn
  have htop := hH.isOpen_inter_preimage hD (isOpen_Ioi (a := (0 : ℝ)))
  have hbottom : IsOpen {q : EuclideanSpace ℝ (Fin 2) | 0 < (collarParameterEquiv q).2} :=
    isOpen_Ioi.preimage (continuous_snd.comp collarParameterEquiv.continuous)
  convert htop.inter hbottom using 1
  ext q
  simp only [openBand, D, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Ioi, sub_pos]
  tauto

omit [T2Space M] in
theorem openBand_subset_band : B.openBand ⊆ B.band := by
  rw [B.band_eq_subgraph]
  intro q hq
  exact ⟨⟨hq.1.1.le, hq.1.2.le⟩, hq.2.1.le, hq.2.2.le⟩

omit [T2Space M] in
theorem openBand_image_subset_interior : B.coordinates '' B.openBand ⊆ interior B.carrier := by
  apply (B.coordinates.isOpen_image_of_subset_source B.isOpen_openBand
    (B.openBand_subset_band.trans B.band_subset_source)).subset_interior_iff.mpr
  rw [B.carrier_eq_image]
  exact image_mono B.openBand_subset_band

omit [T2Space M] in
theorem height_zero : B.height 0 = B.cuts.left.parameter ra := by
  have hfirst : B.firstCell.castSucc = 0 := rfl
  have hmem : (0 : ℝ) ∈ Icc (B.cut B.firstCell.castSucc) (B.cut B.firstCell.succ) := by
    rw [hfirst, B.cut_first]
    exact ⟨le_rfl, by simpa only [hfirst, B.cut_first] using
      (B.cut_strictMono (Fin.castSucc_lt_succ (i := B.firstCell))).le⟩
  rw [B.height_eq_upperGraph hmem]
  have h := (B.upperGraph_endpoints B.firstCell).1
  rw [hfirst, B.cut_first, B.interface.height_first] at h
  exact h

omit [T2Space M] in
theorem height_one : B.height 1 = B.cuts.right.parameter rb := by
  have hlast : B.lastCell.succ = Fin.last B.interface.count := by
    apply Fin.ext
    dsimp [lastCell]
    have hn := B.interface.count_pos
    omega
  have hmem : (1 : ℝ) ∈ Icc (B.cut B.lastCell.castSucc) (B.cut B.lastCell.succ) := by
    rw [hlast, B.cut_last]
    exact ⟨by simpa only [hlast, B.cut_last] using
      (B.cut_strictMono (Fin.castSucc_lt_succ (i := B.lastCell))).le, le_rfl⟩
  rw [B.height_eq_upperGraph hmem]
  have h := (B.upperGraph_endpoints B.lastCell).2
  rw [hlast, B.cut_last, B.interface.height_last] at h
  exact h


def lowerArc (_B : ObliqueBandFaces F lo a b ua wa ub wb ra rb) : Set M :=
  (fun x => F (collarParameterEquiv.symm (x, lo x))) '' Icc a b


def polygonalTop : Set M := ⋃ i : Fin B.interface.count,
  (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) ''
    segment ℝ
      (B.interface.cut i.castSucc, lo (B.interface.cut i.castSucc) + B.interface.height i.castSucc)
      (B.interface.cut i.succ, lo (B.interface.cut i.succ) + B.interface.height i.succ)


def leftCut (_B : ObliqueBandFaces F lo a b ua wa ub wb ra rb) : Set M :=
  (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) ''
  segment ℝ (a, lo a) (a + ra * ua, lo a + ra * wa)


def rightCut (_B : ObliqueBandFaces F lo a b ua wa ub wb ra rb) : Set M :=
  (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) ''
  segment ℝ (b, lo b) (b + rb * ub, lo b + rb * wb)

omit [T2Space M] in
theorem height_graph_image :
    (fun t => B.coordinates (collarParameterEquiv.symm (t, B.height t))) '' Icc (0 : ℝ) 1 =
      B.polygonalTop := by
  rw [← B.cut_interval_cover, image_iUnion]
  apply iUnion_congr
  intro i
  let G := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
  calc
    _ = (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) ''
        ((fun t => B.cuts.coordinates B.open_domain B.smooth_lower (t, G.upperGraph t)) ''
          Icc (B.cut i.castSucc) (B.cut i.succ)) := by
      rw [image_image]
      apply image_congr
      intro t ht
      rw [B.height_eq_upperGraph ht, B.coordinates_pair_apply]
    _ = _ := congrArg (fun S => (fun q : ℝ × ℝ => F (collarParameterEquiv.symm q)) '' S)
      (G.coordinates_image_upperGraph_eq_segment B.open_domain B.smooth_lower)

private theorem image_mul_interval {η : ℝ} (hη : 0 ≤ η) :
    (fun t : ℝ => t * η) '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) η := by
  simpa using (continuous_id.mul_const η).continuousOn.image_Icc_of_monotoneOn
    (zero_le_one : (0 : ℝ) ≤ 1) (fun x _ y _ hxy => mul_le_mul_of_nonneg_right hxy hη)

omit [T2Space M] in
theorem left_height_image :
    (fun z => B.coordinates (collarParameterEquiv.symm (0, z))) '' Icc (0 : ℝ) (B.height 0) =
      B.leftCut := by
  unfold leftCut
  rw [← B.left_edge_image, ← image_mul_interval (B.height_pos (by simp)).le, image_image]
  congr 1
  funext t
  rw [(B.pair B.firstCell).left_edge]
  have hfirst : B.firstCell.castSucc = 0 := rfl
  have hh := (B.upperGraph_endpoints B.firstCell).1
  rw [hfirst, B.cut_first, B.interface.height_first] at hh
  change B.coordinates (collarParameterEquiv.symm (0, t * B.height 0)) =
    B.coordinates (collarParameterEquiv.symm
      (B.cut B.firstCell.castSucc, 0 + t * (B.upperGraph B.firstCell
        (B.cut B.firstCell.castSucc) - 0)))
  rw [hfirst, B.cut_first, hh, B.height_zero, sub_zero, zero_add]

omit [T2Space M] in
theorem right_height_image :
    (fun z => B.coordinates (collarParameterEquiv.symm (1, z))) '' Icc (0 : ℝ) (B.height 1) =
      B.rightCut := by
  unfold rightCut
  rw [← B.right_edge_image, ← image_mul_interval (B.height_pos (by simp)).le, image_image]
  congr 1
  funext t
  rw [(B.pair B.lastCell).right_edge]
  have hlast : B.lastCell.succ = Fin.last B.interface.count := by
    apply Fin.ext
    dsimp [lastCell]
    have hn := B.interface.count_pos
    omega
  have hh := (B.upperGraph_endpoints B.lastCell).2
  rw [hlast, B.cut_last, B.interface.height_last] at hh
  change B.coordinates (collarParameterEquiv.symm (1, t * B.height 1)) =
    B.coordinates (collarParameterEquiv.symm
      (B.cut B.lastCell.succ, 0 + t * (B.upperGraph B.lastCell
        (B.cut B.lastCell.succ) - 0)))
  rw [hlast, B.cut_last, hh, B.height_one, sub_zero, zero_add]


theorem frontier_carrier_subset : frontier B.carrier ⊆
    B.lowerArc ∪ B.polygonalTop ∪ B.leftCut ∪ B.rightCut := by
  intro z hz
  have hzB := B.isClosed_carrier.frontier_subset hz
  rw [B.carrier_eq_image] at hzB
  obtain ⟨q, hq, rfl⟩ := hzB
  have hq' := hq
  rw [B.band_eq_subgraph] at hq'
  have hcoord {x y : ℝ} (hx : x = (collarParameterEquiv q).1)
      (hy : y = (collarParameterEquiv q).2) :
      B.coordinates (collarParameterEquiv.symm (x, y)) = B.coordinates q := by
    apply congrArg B.coordinates
    apply collarParameterEquiv.injective
    rw [collarParameterEquiv.apply_symm_apply]
    exact Prod.ext hx hy
  by_cases hx0 : (collarParameterEquiv q).1 = 0
  · left
    right
    rw [← B.left_height_image]
    refine ⟨(collarParameterEquiv q).2, ?_, ?_⟩
    · simpa only [mem_Icc, hx0] using hq'.2
    · exact hcoord hx0.symm rfl
  by_cases hx1 : (collarParameterEquiv q).1 = 1
  · right
    rw [← B.right_height_image]
    refine ⟨(collarParameterEquiv q).2, ?_, ?_⟩
    · simpa only [mem_Icc, hx1] using hq'.2
    · exact hcoord hx1.symm rfl
  by_cases hy0 : (collarParameterEquiv q).2 = 0
  · left
    left
    left
    have hab : a < b := by
      simpa only [B.cuts.A_zero, B.cuts.B_zero] using
        B.cuts.separated 0 ⟨by linarith [B.cuts.radius_pos], B.cuts.radius_pos⟩
    refine ⟨a + (collarParameterEquiv q).1 * (b - a), ?_, ?_⟩
    · constructor <;> nlinarith [hq'.1.1, hq'.1.2]
    · exact (B.coordinates_bottom _).symm.trans (hcoord rfl hy0.symm)
  by_cases hyH : (collarParameterEquiv q).2 = B.height (collarParameterEquiv q).1
  · left
    left
    right
    rw [← B.height_graph_image]
    refine ⟨(collarParameterEquiv q).1, hq'.1, ?_⟩
    exact hcoord rfl hyH.symm
  exact False.elim (hz.2 (B.openBand_image_subset_interior
    ⟨q, ⟨⟨lt_of_le_of_ne hq'.1.1 (Ne.symm hx0), lt_of_le_of_ne hq'.1.2 hx1⟩,
      lt_of_le_of_ne hq'.2.1 (Ne.symm hy0), lt_of_le_of_ne hq'.2.2 hyH⟩, rfl⟩))


def lowerParameterNeighborhood : Set (EuclideanSpace ℝ (Fin 2)) :=
  B.coordinates.source ∩ {q | (collarParameterEquiv q).1 ∈ Ioo (0 : ℝ) 1 ∧
    |(collarParameterEquiv q).2| < B.height (collarParameterEquiv q).1}

omit [T2Space M] in
theorem isOpen_lowerParameterNeighborhood : IsOpen B.lowerParameterNeighborhood := by
  let D : Set (EuclideanSpace ℝ (Fin 2)) := {q | (collarParameterEquiv q).1 ∈ Ioo (0 : ℝ) 1}
  have hD : IsOpen D := isOpen_Ioo.preimage (continuous_fst.comp collarParameterEquiv.continuous)
  have hH : ContinuousOn (fun q : EuclideanSpace ℝ (Fin 2) =>
      B.height (collarParameterEquiv q).1 - |(collarParameterEquiv q).2|) D :=
    (B.continuousOn_height.comp (continuous_fst.comp collarParameterEquiv.continuous).continuousOn
      (fun _ hq => ⟨hq.1.le, hq.2.le⟩)).sub
        (continuous_snd.comp collarParameterEquiv.continuous).abs.continuousOn
  have htop := hH.isOpen_inter_preimage hD (isOpen_Ioi (a := (0 : ℝ)))
  convert B.coordinates.open_source.inter htop using 1
  ext q
  simp only [lowerParameterNeighborhood, D, mem_inter_iff, mem_ofPred_eq, mem_preimage,
    mem_Ioi, sub_pos]

omit [T2Space M] in
theorem axis_mem_lowerParameterNeighborhood {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    collarParameterEquiv.symm (t, 0) ∈ B.lowerParameterNeighborhood := by
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  constructor
  · apply B.band_subset_source
    rw [B.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, Prod.fst, Prod.snd] using
      And.intro ht' (And.intro (le_refl (0 : ℝ)) (B.height_pos ht').le)
  · simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, Prod.fst, Prod.snd, abs_zero] using
      And.intro ht (B.height_pos ht')


def lowerNeighborhood : Set M := B.coordinates '' B.lowerParameterNeighborhood

omit [T2Space M] in
theorem isOpen_lowerNeighborhood : IsOpen B.lowerNeighborhood :=
  B.coordinates.isOpen_image_of_subset_source B.isOpen_lowerParameterNeighborhood inter_subset_left

omit [T2Space M] in
theorem lowerNeighborhood_subset_target : B.lowerNeighborhood ⊆ F.target := by
  rintro z ⟨q, hq, rfl⟩
  exact (B.coordinates.map_source hq.1).1

omit [T2Space M] in
theorem lower_arc_parameter_mem_neighborhood {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    F (collarParameterEquiv.symm (a + t * (b - a), lo (a + t * (b - a)))) ∈
      B.lowerNeighborhood := by
  rw [← B.coordinates_bottom]
  exact ⟨_, B.axis_mem_lowerParameterNeighborhood ht, rfl⟩

omit [T2Space M] in
theorem ambient_height_eq {q : EuclideanSpace ℝ (Fin 2)} (hq : q ∈ B.coordinates.source) :
    (collarParameterEquiv (F.symm (B.coordinates q))).2 -
      lo (collarParameterEquiv (F.symm (B.coordinates q))).1 = (collarParameterEquiv q).2 := by
  have hFq : collarParameterEquiv.symm
      (B.cuts.coordinates B.open_domain B.smooth_lower (collarParameterEquiv q)) ∈ F.source := hq.2
  change (collarParameterEquiv (F.symm (F (collarParameterEquiv.symm
      (B.cuts.coordinates B.open_domain B.smooth_lower (collarParameterEquiv q)))))).2 -
    lo (collarParameterEquiv (F.symm (F (collarParameterEquiv.symm
      (B.cuts.coordinates B.open_domain B.smooth_lower (collarParameterEquiv q)))))).1 = _
  rw [F.left_inv hFq, collarParameterEquiv.apply_symm_apply, B.cuts.coordinates_apply]
  simp [obliqueStripMap]

omit [T2Space M] in


theorem mem_carrier_iff_above_lower {z : M} (hz : z ∈ B.lowerNeighborhood) :
    z ∈ B.carrier ↔
      lo (collarParameterEquiv (F.symm z)).1 ≤ (collarParameterEquiv (F.symm z)).2 := by
  obtain ⟨q, hq, rfl⟩ := hz
  rw [← sub_nonneg, B.ambient_height_eq hq.1]
  rw [B.mem_carrier_iff (B.coordinates.map_source hq.1), B.coordinates.left_inv hq.1,
    B.band_eq_subgraph]
  constructor
  · exact fun h => h.2.1
  · intro hy
    exact ⟨⟨hq.2.1.1.le, hq.2.1.2.le⟩, hy, (le_abs_self _).trans hq.2.2.le⟩

omit [T2Space M] in


theorem mem_interior_of_above_lower {z : M} (hz : z ∈ B.lowerNeighborhood)
    (hpos : lo (collarParameterEquiv (F.symm z)).1 < (collarParameterEquiv (F.symm z)).2) :
    z ∈ interior B.carrier := by
  obtain ⟨q, hq, rfl⟩ := hz
  have hy : 0 < (collarParameterEquiv q).2 := by
    rw [← B.ambient_height_eq hq.1]
    exact sub_pos.mpr hpos
  apply B.openBand_image_subset_interior
  exact ⟨q, ⟨hq.2.1, hy, (le_abs_self _).trans_lt hq.2.2⟩, rfl⟩

omit [T2Space M] in

theorem open_lower_arc_subset_neighborhood :
    (fun x => F (collarParameterEquiv.symm (x, lo x))) '' Ioo a b ⊆ B.lowerNeighborhood := by
  rintro _ ⟨x, hx, rfl⟩
  have hab : a < b := hx.1.trans hx.2
  let t := (x - a) / (b - a)
  have ht : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (sub_pos.mpr hx.1) (sub_pos.mpr hab),
      (div_lt_one (sub_pos.mpr hab)).mpr (sub_lt_sub_right hx.2 a)⟩
  have hx' : a + t * (b - a) = x := by
    dsimp [t]
    rw [div_mul_cancel₀ _ (sub_pos.mpr hab).ne']
    ring
  simpa only [hx'] using B.lower_arc_parameter_mem_neighborhood ht

private theorem not_mem_interior_of_positive_ray {X : Type*} [TopologicalSpace X]
    {S : Set X} {q : X} (γ : ℝ → X) (hγ : Continuous γ) (hzero : γ 0 = q)
    (hout : ∀ t > 0, γ t ∉ S) : q ∉ interior S := by
  intro hq
  have hlim : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 q) := by
    rw [← hzero]
    exact hγ.continuousAt.mono_left nhdsWithin_le_nhds
  have hm := hlim.eventually (mem_interior_iff_mem_nhds.mp hq)
  obtain ⟨t, ht, hpos⟩ := (hm.and self_mem_nhdsWithin).exists
  exact hout t hpos ht

omit [T2Space M] in
theorem mem_interior_band_of_image_mem_interior {q : EuclideanSpace ℝ (Fin 2)}
    (hq : q ∈ B.coordinates.source) (hi : B.coordinates q ∈ interior B.carrier) :
    q ∈ interior B.band := by
  have hopen : IsOpen (B.coordinates.source ∩ B.coordinates ⁻¹' interior B.carrier) :=
    B.coordinates.continuousOn.isOpen_inter_preimage B.coordinates.open_source isOpen_interior
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset (hopen.mem_nhds ⟨hq, hi⟩)
  intro w hw
  have hm := (B.mem_carrier_iff (B.coordinates.map_source hw.1)).mp (interior_subset hw.2)
  simpa only [B.coordinates.left_inv hw.1] using hm

omit [T2Space M] in
theorem coordinate_outer_mem_frontier {q : EuclideanSpace ℝ (Fin 2)} (hq : q ∈ B.band)
    (houter : (collarParameterEquiv q).1 = 0 ∨ (collarParameterEquiv q).1 = 1 ∨
      (collarParameterEquiv q).2 = 0 ∨
      (collarParameterEquiv q).2 = B.height (collarParameterEquiv q).1) :
    B.coordinates q ∈ frontier B.carrier := by
  have hmem : B.coordinates q ∈ B.carrier := by
    rw [B.carrier_eq_image]
    exact mem_image_of_mem _ hq
  refine ⟨subset_closure hmem, ?_⟩
  intro hi
  have hqi := B.mem_interior_band_of_image_mem_interior (B.band_subset_source hq) hi
  rcases houter with hx | hx | hy | hy
  · apply not_mem_interior_of_positive_ray
      (fun s => collarParameterEquiv.symm ((collarParameterEquiv q).1 - s,
        (collarParameterEquiv q).2)) (by fun_prop)
      (by simpa only [sub_zero] using collarParameterEquiv.symm_apply_apply q) ?_ hqi
    intro s hs hmem
    rw [B.band_eq_subgraph] at hmem
    have h := hmem.1.1
    simp only [collarParameterEquiv.apply_symm_apply, hx, zero_sub] at h
    linarith
  · apply not_mem_interior_of_positive_ray
      (fun s => collarParameterEquiv.symm ((collarParameterEquiv q).1 + s,
        (collarParameterEquiv q).2)) (by fun_prop)
      (by simpa only [add_zero] using collarParameterEquiv.symm_apply_apply q) ?_ hqi
    intro s hs hmem
    rw [B.band_eq_subgraph] at hmem
    have h := hmem.1.2
    simp only [collarParameterEquiv.apply_symm_apply, hx] at h
    linarith
  · apply not_mem_interior_of_positive_ray
      (fun s => collarParameterEquiv.symm ((collarParameterEquiv q).1,
        (collarParameterEquiv q).2 - s)) (by fun_prop)
      (by simpa only [sub_zero] using collarParameterEquiv.symm_apply_apply q) ?_ hqi
    intro s hs hmem
    rw [B.band_eq_subgraph] at hmem
    have h := hmem.2.1
    simp only [collarParameterEquiv.apply_symm_apply, hy, zero_sub] at h
    linarith
  · apply not_mem_interior_of_positive_ray
      (fun s => collarParameterEquiv.symm ((collarParameterEquiv q).1,
        (collarParameterEquiv q).2 + s)) (by fun_prop)
      (by simpa only [add_zero] using collarParameterEquiv.symm_apply_apply q) ?_ hqi
    intro s hs hmem
    rw [B.band_eq_subgraph] at hmem
    have h := hmem.2.2
    simp only [collarParameterEquiv.apply_symm_apply, hy] at h
    linarith

omit [T2Space M] in

theorem outer_boundaries_subset_frontier :
    B.lowerArc ∪ B.polygonalTop ∪ B.leftCut ∪ B.rightCut ⊆ frontier B.carrier := by
  intro z hz
  rcases hz with ((hz | hz) | hz) | hz
  · obtain ⟨x, hx, rfl⟩ := hz
    have hab : a < b := by
      simpa only [B.cuts.A_zero, B.cuts.B_zero] using
        B.cuts.separated 0 ⟨by linarith [B.cuts.radius_pos], B.cuts.radius_pos⟩
    let t := (x - a) / (b - a)
    have ht : t ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le,
        (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right hx.2 a)⟩
    have hx' : a + t * (b - a) = x := by
      dsimp [t]
      rw [div_mul_cancel₀ _ (sub_pos.mpr hab).ne']
      ring
    have hq : collarParameterEquiv.symm (t, 0) ∈ B.band := by
      rw [B.band_eq_subgraph]
      simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, Prod.fst, Prod.snd] using
        And.intro ht (And.intro (le_refl (0 : ℝ)) (B.height_pos ht).le)
    have h := B.coordinate_outer_mem_frontier hq (Or.inr (Or.inr (Or.inl (by simp))))
    simpa only [B.coordinates_bottom, hx'] using h
  · rw [← B.height_graph_image] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    apply B.coordinate_outer_mem_frontier
    · rw [B.band_eq_subgraph]
      simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, Prod.fst, Prod.snd] using
        And.intro ht (And.intro (B.height_pos ht).le (le_refl (B.height t)))
    · exact Or.inr (Or.inr (Or.inr (by simp)))
  · rw [← B.left_height_image] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    apply B.coordinate_outer_mem_frontier
    · rw [B.band_eq_subgraph]
      simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, Prod.fst, Prod.snd, mem_Icc] using
        And.intro (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hs
    · exact Or.inl (by simp)
  · rw [← B.right_height_image] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    apply B.coordinate_outer_mem_frontier
    · rw [B.band_eq_subgraph]
      simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, Prod.fst, Prod.snd, mem_Icc] using
        And.intro (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hs
    · exact Or.inr (Or.inl (by simp))


theorem frontier_carrier : frontier B.carrier =
    B.lowerArc ∪ B.polygonalTop ∪ B.leftCut ∪ B.rightCut :=
  Subset.antisymm B.frontier_carrier_subset B.outer_boundaries_subset_frontier


theorem mem_frontier_iff_on_lower {z : M} (hz : z ∈ B.lowerNeighborhood) :
    z ∈ frontier B.carrier ↔
      (collarParameterEquiv (F.symm z)).2 = lo (collarParameterEquiv (F.symm z)).1 := by
  constructor
  · intro hf
    have hle := (B.mem_carrier_iff_above_lower hz).mp (B.isClosed_carrier.frontier_subset hf)
    apply le_antisymm _ hle
    by_contra hn
    exact hf.2 (B.mem_interior_of_above_lower hz (lt_of_not_ge hn))
  · intro heq
    obtain ⟨q, hq, rfl⟩ := hz
    have hy : (collarParameterEquiv q).2 = 0 := by
      rw [← B.ambient_height_eq hq.1, heq, sub_self]
    apply B.coordinate_outer_mem_frontier
    · rw [B.band_eq_subgraph]
      exact ⟨⟨hq.2.1.1.le, hq.2.1.2.le⟩, hy.symm.le,
        (le_abs_self _).trans hq.2.2.le⟩
    · exact Or.inr (Or.inr (Or.inl hy))


theorem mem_interior_iff_above_lower {z : M} (hz : z ∈ B.lowerNeighborhood) :
    z ∈ interior B.carrier ↔
      lo (collarParameterEquiv (F.symm z)).1 < (collarParameterEquiv (F.symm z)).2 := by
  constructor
  · intro hi
    have hle := (B.mem_carrier_iff_above_lower hz).mp (interior_subset hi)
    apply lt_of_le_of_ne hle
    intro heq
    exact ((B.mem_frontier_iff_on_lower hz).mpr heq.symm).2 hi
  · exact B.mem_interior_of_above_lower hz

end PoincareConjecture.Topology.Surface.ObliqueBandFaces

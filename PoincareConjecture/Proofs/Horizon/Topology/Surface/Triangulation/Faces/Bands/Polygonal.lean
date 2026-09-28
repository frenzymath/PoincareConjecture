import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Graphs
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Topology
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.Subdivision
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.PolygonalApproximation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology Matrix
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

def coordinateGraphBand (lo hi : ℝ → ℝ) (a b : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  collarParameterEquiv ⁻¹'
    {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1}

structure SmoothGraphBandPair
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (lo hi : ℝ → ℝ) {a b : ℝ} (hab : a < b) where
  lower : SmoothFace M
  upper : SmoothFace M
  gap : ∀ t ∈ Icc a b, lo t < hi t
  band_subset_source : coordinateGraphBand lo hi a b ⊆ F.source
  lower_map : lower.map = fun z => F (collarParameterEquiv.symm
    (graphStripMap lo hi (collarParameterEquiv z)))
  upper_map : upper.map = lower.map
  lower_source : lower.source = convexHull ℝ (range (rectangleLowerBasis hab zero_lt_one))
  upper_source : upper.source = convexHull ℝ (range (rectangleUpperBasis hab zero_lt_one))
  lower_injective : InjOn lower.map lower.source
  upper_injective : InjOn upper.map upper.source
  cover : lower.carrier ∪ upper.carrier = F '' coordinateGraphBand lo hi a b
  diagonal_inter : lower.carrier ∩ upper.carrier = (lower.boundary 1).map '' Icc (0 : ℝ) 1
  diagonal_eq : lower.boundary 1 = upper.boundary 1
  lower_edge : ∀ t : ℝ, (lower.boundary 2).map t =
    F (collarParameterEquiv.symm (a + t * (b - a), lo (a + t * (b - a))))
  upper_edge : ∀ t : ℝ, (upper.boundary 0).map t =
    F (collarParameterEquiv.symm (a + t * (b - a), hi (a + t * (b - a))))
  right_edge : ∀ t : ℝ, (lower.boundary 0).map t =
    F (collarParameterEquiv.symm (b, lo b + t * (hi b - lo b)))
  left_edge : ∀ t : ℝ, (upper.boundary 2).map t =
    F (collarParameterEquiv.symm (a, lo a + t * (hi a - lo a)))

theorem exists_smoothGraphBandPair
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {lo hi : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hlo : ContDiffOn ℝ ∞ lo U) (hhi : ContDiffOn ℝ ∞ hi U)
    {a b : ℝ} (hab : a < b) (hI : Icc a b ⊆ U)
    (hgap : ∀ t ∈ Icc a b, lo t < hi t)
    (hband : coordinateGraphBand lo hi a b ⊆ F.source)
    (p : M) (hchart : F.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    Nonempty (SmoothGraphBandPair F lo hi hab) := by
  let V := U ∩ interior {t | lo t < hi t}
  have hV : IsOpen V := hU.inter isOpen_interior
  have hIV : Icc a b ⊆ V := by
    intro t ht
    refine ⟨hI ht, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact ((hlo t (hI ht)).continuousWithinAt.continuousAt (hU.mem_nhds (hI ht))).eventually_lt
      ((hhi t (hI ht)).continuousWithinAt.continuousAt (hU.mem_nhds (hI ht))) (hgap t ht)
  obtain ⟨f, g, hf, hg, hfs, hgs, hfi, hgi, hcover, hinter, hdiag, hlower, hupper,
      hright, hleft⟩ := exists_smoothFace_pair_between_graphs F hF hFinv hV
    (hlo.mono inter_subset_left) (hhi.mono inter_subset_left)
    (fun t ht => show t ∈ {t | lo t < hi t} from interior_subset ht.2) hab hIV hband p hchart
  exact ⟨⟨f, g, hgap, hband, hf, hg, hfs, hgs, hfi, hgi, hcover, hinter, hdiag,
    hlower, hupper, hright, hleft⟩⟩

namespace SmoothGraphBandPair

variable {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo hi : ℝ → ℝ} {a b : ℝ} {hab : a < b}
  (B : SmoothGraphBandPair F lo hi hab)

def face : Bool → SmoothFace M
  | false => B.lower
  | true => B.upper

omit [T2Space M] in
theorem carrier_subset (i : Bool) : (B.face i).carrier ⊆ F '' coordinateGraphBand lo hi a b := by
  rw [← B.cover]
  cases i
  · exact subset_union_left
  · exact subset_union_right

omit [T2Space M] in
theorem parameter_mem {z : M} {i : Bool} (hz : z ∈ (B.face i).carrier) :
    (collarParameterEquiv (F.symm z)).1 ∈ Icc a b ∧
      lo (collarParameterEquiv (F.symm z)).1 ≤ (collarParameterEquiv (F.symm z)).2 ∧
      (collarParameterEquiv (F.symm z)).2 ≤ hi (collarParameterEquiv (F.symm z)).1 := by
  obtain ⟨w, hw, rfl⟩ := B.carrier_subset i hz
  rw [F.left_inv (B.band_subset_source hw)]
  exact hw

include B in
omit [T2Space M] in
private theorem strip_mem_band {w : EuclideanSpace ℝ (Fin 2)}
    (hw : w 0 ∈ Icc a b ∧ w 1 ∈ Icc (0 : ℝ) 1) :
    collarParameterEquiv.symm (graphStripMap lo hi (collarParameterEquiv w)) ∈
      coordinateGraphBand lo hi a b := by
  change collarParameterEquiv
      (collarParameterEquiv.symm (graphStripMap lo hi (collarParameterEquiv w))) ∈
        {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1}
  rw [collarParameterEquiv.apply_symm_apply, ← graphStripMap_image_rectangle B.gap]
  exact ⟨collarParameterEquiv w, hw, rfl⟩

omit [T2Space M] in
theorem lower_left_vertex {z : M} (hz : z ∈ B.lower.carrier)
    (hx : (collarParameterEquiv (F.symm z)).1 = a) :
    z = F (collarParameterEquiv.symm (a, lo a)) := by
  rw [B.lower.carrier_eq_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [B.lower_source] at hw
  have hrect : w 0 ∈ Icc a b ∧ w 1 ∈ Icc (0 : ℝ) 1 := by
    change w ∈ {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc (0 : ℝ) 1}
    rw [← rectangle_triangle_union hab zero_lt_one]
    exact Or.inl hw
  rw [B.lower_map] at hx ⊢
  rw [F.left_inv (B.band_subset_source (B.strip_mem_band hrect)),
    collarParameterEquiv.apply_symm_apply] at hx
  change w 0 = a at hx
  have hh := (mem_rectangleLowerBasis_convexHull hab zero_lt_one w).mp hw
  simp only [sub_zero, sub_self, div_one, hx, zero_div] at hh
  have hy : w 1 = 0 := le_antisymm hh.2.1 hh.1
  apply congrArg F
  apply congrArg collarParameterEquiv.symm
  change (w 0, lo (w 0) + w 1 * (hi (w 0) - lo (w 0))) = (a, lo a)
  simp [hx, hy]

omit [T2Space M] in
theorem upper_right_vertex {z : M} (hz : z ∈ B.upper.carrier)
    (hx : (collarParameterEquiv (F.symm z)).1 = b) :
    z = F (collarParameterEquiv.symm (b, hi b)) := by
  rw [B.upper.carrier_eq_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [B.upper_source] at hw
  have hrect : w 0 ∈ Icc a b ∧ w 1 ∈ Icc (0 : ℝ) 1 := by
    change w ∈ {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc (0 : ℝ) 1}
    rw [← rectangle_triangle_union hab zero_lt_one]
    exact Or.inr hw
  rw [B.upper_map, B.lower_map] at hx ⊢
  rw [F.left_inv (B.band_subset_source (B.strip_mem_band hrect)),
    collarParameterEquiv.apply_symm_apply] at hx
  change w 0 = b at hx
  have hh := (mem_rectangleUpperBasis_convexHull hab zero_lt_one w).mp hw
  simp only [sub_zero, div_one, hx, div_self (sub_ne_zero.mpr hab.ne')] at hh
  have hy : w 1 = 1 := le_antisymm hh.2.2 hh.2.1
  apply congrArg F
  apply congrArg collarParameterEquiv.symm
  change (w 0, lo (w 0) + w 1 * (hi (w 0) - lo (w 0))) = (b, hi b)
  simp [hx, hy]

omit [T2Space M] in
theorem right_edge_slice {z : M} (hz : z ∈ F '' coordinateGraphBand lo hi a b)
    (hx : (collarParameterEquiv (F.symm z)).1 = b) :
    z ∈ (B.lower.boundary 0).map '' Icc (0 : ℝ) 1 := by
  obtain ⟨w, hw, rfl⟩ := hz
  rw [F.left_inv (B.band_subset_source hw)] at hx
  have hy : (collarParameterEquiv w).2 ∈ Icc (lo b) (hi b) := by
    simpa only [mem_Icc, ← hx] using hw.2
  have hgap : 0 < hi b - lo b := sub_pos.mpr (B.gap b (right_mem_Icc.mpr hab.le))
  let t := ((collarParameterEquiv w).2 - lo b) / (hi b - lo b)
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hy.1) hgap.le,
      (div_le_one hgap).mpr (sub_le_sub_right hy.2 _)⟩
  refine ⟨t, ht, ?_⟩
  rw [B.right_edge]
  apply congrArg F
  have he : (b, lo b + t * (hi b - lo b)) = collarParameterEquiv w := by
    apply Prod.ext hx.symm
    dsimp [t]
    rw [div_mul_cancel₀ _ hgap.ne']
    ring
  rw [he, collarParameterEquiv.symm_apply_apply]

omit [T2Space M] in
private theorem edge_eq_of_map_eq {e e' : SmoothEdge M} (h : e.map = e'.map) : e = e' := by
  cases e
  cases e'
  cases h
  rfl

omit [T2Space M] in

theorem adjacent_edge_eq {hi' : ℝ → ℝ} {c d : ℝ} {hcd : c < d}
    (C : SmoothGraphBandPair F lo hi' hcd) (hjoin : b = c) (hheight : hi b = hi' c) :
    B.lower.boundary 0 = C.upper.boundary 2 := by
  apply edge_eq_of_map_eq
  funext t
  rw [B.right_edge, C.left_edge, hheight, hjoin]

theorem adjacent_lower_upper_inter {hi' : ℝ → ℝ} {c d : ℝ} {hcd : c < d}
    (C : SmoothGraphBandPair F lo hi' hcd) (hjoin : b = c) (hheight : hi b = hi' c) :
    B.lower.carrier ∩ C.upper.carrier = (B.lower.boundary 0).map '' Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · intro z hz
    have hB := B.parameter_mem (i := false) hz.1
    have hC := C.parameter_mem (i := true) hz.2
    apply B.right_edge_slice (B.carrier_subset false hz.1)
    exact le_antisymm hB.1.2 (hjoin.symm ▸ hC.1.1)
  · intro z hz
    constructor
    · exact B.lower.isClosed_carrier.frontier_subset (B.lower.boundary_image_subset_frontier 0 hz)
    · rw [B.adjacent_edge_eq C hjoin hheight] at hz
      exact C.upper.isClosed_carrier.frontier_subset (C.upper.boundary_image_subset_frontier 2 hz)

omit [T2Space M] in

theorem disjoint_of_right_lt_left {hi' : ℝ → ℝ} {c d : ℝ} {hcd : c < d}
    (C : SmoothGraphBandPair F lo hi' hcd) (hsep : b < c) (i j : Bool) :
    Disjoint (B.face i).carrier (C.face j).carrier := by
  apply disjoint_left.mpr
  intro z hzB hzC
  have hB := B.parameter_mem hzB
  have hC := C.parameter_mem hzC
  exact (not_lt_of_ge (hC.1.1.trans hB.1.2)) hsep

theorem adjacent_face_intersection {hi' : ℝ → ℝ} {c d : ℝ} {hcd : c < d}
    (C : SmoothGraphBandPair F lo hi' hcd) (hjoin : b = c) (hheight : hi b = hi' c)
    (i j : Bool) :
    (∃ k l : Fin 3, (B.face i).boundary k = (C.face j).boundary l ∧
      (B.face i).carrier ∩ (C.face j).carrier =
        ((B.face i).boundary k).map '' Icc (0 : ℝ) 1) ∨
      ∃ z : M, (B.face i).carrier ∩ (C.face j).carrier ⊆ {z} := by
  have hx {z : M} (hz : z ∈ (B.face i).carrier ∩ (C.face j).carrier) :
      (collarParameterEquiv (F.symm z)).1 = b := by
    have hB := B.parameter_mem hz.1
    have hC := C.parameter_mem hz.2
    exact le_antisymm hB.1.2 (hjoin.symm ▸ hC.1.1)
  cases i <;> cases j
  · right
    refine ⟨F (collarParameterEquiv.symm (c, lo c)), ?_⟩
    intro z hz
    exact C.lower_left_vertex hz.2 ((hx hz).trans hjoin)
  · exact Or.inl ⟨0, 2, B.adjacent_edge_eq C hjoin hheight,
      B.adjacent_lower_upper_inter C hjoin hheight⟩
  · right
    refine ⟨F (collarParameterEquiv.symm (b, hi b)), ?_⟩
    intro z hz
    exact B.upper_right_vertex hz.1 (hx hz)
  · right
    refine ⟨F (collarParameterEquiv.symm (b, hi b)), ?_⟩
    intro z hz
    exact B.upper_right_vertex hz.1 (hx hz)

end SmoothGraphBandPair

structure PolygonalBandFaces
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (lo hi : ℝ → ℝ) (a b ya yb : ℝ) where
  count : ℕ
  count_pos : 0 < count
  cut : Fin (count + 1) → ℝ
  height : Fin (count + 1) → ℝ
  piece : Fin count → ℝ →ᵃ[ℝ] ℝ
  cut_strictMono : StrictMono cut
  cut_first : cut 0 = a
  cut_last : cut (Fin.last count) = b
  height_first : height 0 = ya
  height_last : height (Fin.last count) = yb
  piece_endpoints : ∀ i,
    piece i (cut i.castSucc) = height i.castSucc ∧ piece i (cut i.succ) = height i.succ
  piece_formula : ∀ i t, piece i t = height i.castSucc +
    ((height i.succ - height i.castSucc) / (cut i.succ - cut i.castSucc)) * (t - cut i.castSucc)
  piece_bounds : ∀ i t, t ∈ Icc (cut i.castSucc) (cut i.succ) →
    lo t < piece i t ∧ piece i t < hi t
  pair : ∀ i, SmoothGraphBandPair F lo (piece i) (cut_strictMono (Fin.castSucc_lt_succ (i := i)))

theorem exists_polygonalBandFaces
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {lo hi : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hlo : ContDiffOn ℝ ∞ lo U)
    {a b ya yb : ℝ} (hab : a < b) (hI : Icc a b ⊆ U)
    (hhi : ContinuousOn hi (Icc a b)) (hgap : ∀ t ∈ Icc a b, lo t < hi t)
    (ha : lo a < ya ∧ ya < hi a) (hb : lo b < yb ∧ yb < hi b)
    (hband : coordinateGraphBand lo hi a b ⊆ F.source)
    (p : M) (hchart : F.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    Nonempty (PolygonalBandFaces F lo hi a b ya yb) := by
  classical
  obtain ⟨n, c, y, piece, hn, hc, hca, hcb, hya, hyb, hends, hformula, hbounds⟩ :=
    exists_piecewiseAffine_between hab (hlo.continuousOn.mono hI) hhi hgap ha hb
  have hcell (i : Fin n) : Icc (c i.castSucc) (c i.succ) ⊆ Icc a b := by
    intro t ht
    constructor
    · rw [← hca]
      exact (hc.monotone (Fin.zero_le i.castSucc)).trans ht.1
    · rw [← hcb]
      exact ht.2.trans (hc.monotone (Fin.le_last i.succ))
  have hpiece (i : Fin n) : ContDiff ℝ ∞ (piece i) := by
    have heq : (piece i : ℝ → ℝ) = fun t => y i.castSucc +
        ((y i.succ - y i.castSucc) / (c i.succ - c i.castSucc)) * (t - c i.castSucc) :=
      funext (hformula i)
    rw [heq]
    fun_prop
  have hpairs (i : Fin n) :
      Nonempty (SmoothGraphBandPair F lo (piece i) (hc (Fin.castSucc_lt_succ (i := i)))) := by
    apply exists_smoothGraphBandPair F hF hFinv hU hlo (hpiece i).contDiffOn
      (hc Fin.castSucc_lt_succ) ((hcell i).trans hI)
      (fun t ht => (hbounds i t ht).1) ?_ p hchart
    intro z hz
    apply hband
    exact ⟨hcell i hz.1, hz.2.1, hz.2.2.trans (hbounds i _ hz.1).2.le⟩
  exact ⟨{
    count := n
    count_pos := hn
    cut := c
    height := y
    piece := piece
    cut_strictMono := hc
    cut_first := hca
    cut_last := hcb
    height_first := hya
    height_last := hyb
    piece_endpoints := hends
    piece_formula := hformula
    piece_bounds := hbounds
    pair := fun i => Classical.choice (hpairs i) }⟩

namespace PolygonalBandFaces

variable {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo hi : ℝ → ℝ} {a b ya yb : ℝ} (P : PolygonalBandFaces F lo hi a b ya yb)

def face (i : Fin P.count × Bool) : SmoothFace M := (P.pair i.1).face i.2

def band : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i, coordinateGraphBand lo (P.piece i) (P.cut i.castSucc) (P.cut i.succ)

omit [T2Space M] in
theorem cover : (⋃ i, (P.face i).carrier) = F '' P.band := by
  ext z
  constructor
  · rintro ⟨_, ⟨⟨i, side⟩, rfl⟩, hz⟩
    obtain ⟨w, hw, rfl⟩ := (P.pair i).carrier_subset side hz
    exact ⟨w, mem_iUnion.mpr ⟨i, hw⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hw
    have h := mem_image_of_mem F hi
    rw [← (P.pair i).cover] at h
    rcases h with h | h
    · exact mem_iUnion.mpr ⟨(i, false), h⟩
    · exact mem_iUnion.mpr ⟨(i, true), h⟩

omit [T2Space M] in
theorem band_subset : P.band ⊆ coordinateGraphBand lo hi a b := by
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  refine ⟨⟨?_, ?_⟩, hi.2.1, hi.2.2.trans (P.piece_bounds i _ hi.1).2.le⟩
  · rw [← P.cut_first]
    exact (P.cut_strictMono.monotone (Fin.zero_le i.castSucc)).trans hi.1.1
  · rw [← P.cut_last]
    exact hi.1.2.trans (P.cut_strictMono.monotone (Fin.le_last i.succ))

omit [T2Space M] in

theorem face_subset_band (i : Fin P.count × Bool) :
    (P.face i).carrier ⊆ F '' coordinateGraphBand lo hi a b := by
  intro z hz
  apply image_mono P.band_subset
  rw [← P.cover]
  exact mem_iUnion.mpr ⟨i, hz⟩

omit [T2Space M] in

theorem cut_interval_cover :
    (⋃ i : Fin P.count, Icc (P.cut i.castSucc) (P.cut i.succ)) = Icc a b := by
  simpa only [P.cut_first, P.cut_last] using
    iUnion_Icc_consecutive P.count_pos P.cut P.cut_strictMono.monotone

noncomputable def vertex (i : Fin (P.count + 1) × Bool) : M :=
  F (collarParameterEquiv.symm
    (P.cut i.1, if i.2 then P.height i.1 else lo (P.cut i.1)))

omit [T2Space M] in

theorem adjacent_edges {i j : Fin P.count} (hij : (i : ℕ) + 1 = j) :
    ((P.pair i).lower.boundary 0) = ((P.pair j).upper.boundary 2) := by
  have he : i.succ = j.castSucc := Fin.ext hij
  apply (P.pair i).adjacent_edge_eq (P.pair j) (congrArg P.cut he)
  rw [(P.piece_endpoints i).2, (P.piece_endpoints j).1, he]

theorem adjacent_intersection {i j : Fin P.count} (hij : (i : ℕ) + 1 = j) :
    (P.pair i).lower.carrier ∩ (P.pair j).upper.carrier =
      ((P.pair i).lower.boundary 0).map '' Icc (0 : ℝ) 1 := by
  have he : i.succ = j.castSucc := Fin.ext hij
  apply (P.pair i).adjacent_lower_upper_inter (P.pair j) (congrArg P.cut he)
  rw [(P.piece_endpoints i).2, (P.piece_endpoints j).1, he]

omit [T2Space M] in

theorem nonadjacent_disjoint {i j : Fin P.count} (hij : (i : ℕ) + 1 < j) (s t : Bool) :
    Disjoint (P.face (i, s)).carrier (P.face (j, t)).carrier := by
  apply (P.pair i).disjoint_of_right_lt_left (P.pair j) ?_ s t
  exact P.cut_strictMono (show i.succ < j.castSucc from hij)

private theorem face_intersection_of_lt {i j : Fin P.count} (hij : i < j) (s t : Bool) :
    (∃ k l : Fin 3, (P.face (i, s)).boundary k = (P.face (j, t)).boundary l ∧
      (P.face (i, s)).carrier ∩ (P.face (j, t)).carrier =
        ((P.face (i, s)).boundary k).map '' Icc (0 : ℝ) 1) ∨
    ∃ v : Fin (P.count + 1) × Bool,
      (P.face (i, s)).carrier ∩ (P.face (j, t)).carrier ⊆ {P.vertex v} := by
  by_cases hnext : (i : ℕ) + 1 = j
  · have he : i.succ = j.castSucc := Fin.ext hnext
    have hx {z : M} (hz : z ∈ (P.face (i, s)).carrier ∩ (P.face (j, t)).carrier) :
        (collarParameterEquiv (F.symm z)).1 = P.cut i.succ := by
      have hleft := (P.pair i).parameter_mem hz.1
      have hright := (P.pair j).parameter_mem hz.2
      exact le_antisymm hleft.1.2 (he ▸ hright.1.1)
    cases s <;> cases t
    · right
      refine ⟨(j.castSucc, false), ?_⟩
      intro z hz
      exact (P.pair j).lower_left_vertex hz.2 ((hx hz).trans (congrArg P.cut he))
    · exact Or.inl ⟨0, 2, P.adjacent_edges hnext, P.adjacent_intersection hnext⟩
    · right
      refine ⟨(i.succ, true), ?_⟩
      intro z hz
      have h := (P.pair i).upper_right_vertex hz.1 (hx hz)
      simpa [vertex, (P.piece_endpoints i).2] using h
    · right
      refine ⟨(i.succ, true), ?_⟩
      intro z hz
      have h := (P.pair i).upper_right_vertex hz.1 (hx hz)
      simpa [vertex, (P.piece_endpoints i).2] using h
  · right
    refine ⟨(0, false), ?_⟩
    have hsep : (i : ℕ) + 1 < j := by have hval : (i : ℕ) < j := hij; omega
    rw [disjoint_iff_inter_eq_empty.mp (P.nonadjacent_disjoint hsep s t)]
    exact empty_subset _

theorem face_intersection (i j : Fin P.count × Bool) (hij : i ≠ j) :
    (∃ k l : Fin 3, (P.face i).boundary k = (P.face j).boundary l ∧
      (P.face i).carrier ∩ (P.face j).carrier =
        ((P.face i).boundary k).map '' Icc (0 : ℝ) 1) ∨
    ∃ v : Fin (P.count + 1) × Bool, (P.face i).carrier ∩ (P.face j).carrier ⊆ {P.vertex v} := by
  rcases i with ⟨i, s⟩
  rcases j with ⟨j, t⟩
  by_cases heq : i = j
  · subst j
    cases s <;> cases t
    · exact False.elim (hij rfl)
    · exact Or.inl ⟨1, 1, (P.pair i).diagonal_eq, (P.pair i).diagonal_inter⟩
    · left
      refine ⟨1, 1, (P.pair i).diagonal_eq.symm, ?_⟩
      change (P.pair i).upper.carrier ∩ (P.pair i).lower.carrier = _
      rw [inter_comm, (P.pair i).diagonal_inter, (P.pair i).diagonal_eq]
      rfl
    · exact False.elim (hij rfl)
  · rcases lt_or_gt_of_ne heq with hlt | hgt
    · exact P.face_intersection_of_lt hlt s t
    · rcases P.face_intersection_of_lt hgt t s with ⟨k, l, hedge, hinter⟩ | ⟨v, hv⟩
      · left
        refine ⟨l, k, hedge.symm, ?_⟩
        rw [inter_comm, hinter, hedge]
      · right
        exact ⟨v, by rwa [inter_comm]⟩

end PolygonalBandFaces

end PoincareConjecture.Topology.Surface

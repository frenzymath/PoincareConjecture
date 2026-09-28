


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.CrossingCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.Locality









set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface


def crossingOpenRectangle (a b e : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  collarParameterEquiv ⁻¹' ball (a, b) e


def crossingClosedRectangle (a b e : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  collarParameterEquiv ⁻¹' closedBall (a, b) e

theorem crossingOpenRectangle_eq (a b e : ℝ) :
    crossingOpenRectangle a b e =
      {z | z 0 ∈ Ioo (a - e) (a + e) ∧ z 1 ∈ Ioo (b - e) (b + e)} := by
  ext z
  simp only [crossingOpenRectangle, ← ball_prod_same, mem_preimage, mem_prod,
    collarParameterEquiv_apply, Real.ball_eq_Ioo, mem_ofPred_eq]

theorem crossingClosedRectangle_eq (a b e : ℝ) :
    crossingClosedRectangle a b e =
      {z | z 0 ∈ Icc (a - e) (a + e) ∧ z 1 ∈ Icc (b - e) (b + e)} := by
  ext z
  simp only [crossingClosedRectangle, ← closedBall_prod_same, mem_preimage, mem_prod,
    collarParameterEquiv_apply, Real.closedBall_eq_Icc, mem_ofPred_eq]

theorem crossingOpenRectangle_subset_closed (a b e : ℝ) :
    crossingOpenRectangle a b e ⊆ crossingClosedRectangle a b e :=
  preimage_mono ball_subset_closedBall

theorem isOpen_crossingOpenRectangle (a b e : ℝ) :
    IsOpen (crossingOpenRectangle a b e) :=
  isOpen_ball.preimage collarParameterEquiv.continuous

theorem isCompact_crossingClosedRectangle (a b e : ℝ) :
    IsCompact (crossingClosedRectangle a b e) :=
  collarParameterEquiv.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)

theorem closure_crossingOpenRectangle (a b : ℝ) {e : ℝ} (he : 0 < e) :
    closure (crossingOpenRectangle a b e) = crossingClosedRectangle a b e := by
  change closure (collarParameterEquiv.toHomeomorph ⁻¹' ball (a, b) e) = _
  rw [← collarParameterEquiv.toHomeomorph.preimage_closure,
    closure_ball _ he.ne']
  rfl

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]



structure ChartCircleCrossingPatch (x y : M) (rx ry : ℝ) (p : M) where
  coordinates : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M
  width : ℝ
  width_pos : 0 < width
  point_mem : p ∈ coordinates.target
  center_eq : coordinates.symm p = collarParameterEquiv.symm (ry ^ 2, rx ^ 2)
  target_subset : coordinates.target ⊆
    (chartAt (EuclideanSpace ℝ (Fin 2)) x).source ∩
      (chartAt (EuclideanSpace ℝ (Fin 2)) y).source
  smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ coordinates coordinates.source
  smooth_symm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ coordinates.symm coordinates.target
  rectangle_subset : crossingClosedRectangle (ry ^ 2) (rx ^ 2) width ⊆ coordinates.source
  squaredRadius : ∀ z ∈ coordinates.source,
    ‖chartAt (EuclideanSpace ℝ (Fin 2)) y (coordinates z) -
      chartAt (EuclideanSpace ℝ (Fin 2)) y y‖ ^ 2 = z 0 ∧
    ‖chartAt (EuclideanSpace ℝ (Fin 2)) x (coordinates z) -
      chartAt (EuclideanSpace ℝ (Fin 2)) x x‖ ^ 2 = z 1
  circle_y : ∀ z ∈ coordinates.source, coordinates z ∈ chartCircle y ry ↔ z 0 = ry ^ 2
  circle_x : ∀ z ∈ coordinates.source, coordinates z ∈ chartCircle x rx ↔ z 1 = rx ^ 2

namespace ChartCircleCrossingPatch

variable {x y p : M} {rx ry : ℝ} (P : ChartCircleCrossingPatch x y rx ry p)


def openCarrier : Set M :=
  P.coordinates '' crossingOpenRectangle (ry ^ 2) (rx ^ 2) P.width


def carrier : Set M :=
  P.coordinates '' crossingClosedRectangle (ry ^ 2) (rx ^ 2) P.width

theorem openCarrier_subset_carrier : P.openCarrier ⊆ P.carrier :=
  image_mono (crossingOpenRectangle_subset_closed _ _ _)

theorem isOpen_openCarrier : IsOpen P.openCarrier :=
  P.coordinates.isOpen_image_of_subset_source (isOpen_crossingOpenRectangle _ _ _)
    ((crossingOpenRectangle_subset_closed _ _ _).trans P.rectangle_subset)

theorem mem_openCarrier : p ∈ P.openCarrier := by
  refine ⟨P.coordinates.symm p, ?_, P.coordinates.right_inv P.point_mem⟩
  rw [P.center_eq]
  change collarParameterEquiv (collarParameterEquiv.symm (ry ^ 2, rx ^ 2)) ∈
    ball (ry ^ 2, rx ^ 2) P.width
  rw [collarParameterEquiv.apply_symm_apply]
  exact mem_ball_self P.width_pos

theorem isCompact_carrier : IsCompact P.carrier :=
  (isCompact_crossingClosedRectangle _ _ _).image_of_continuousOn
    (P.coordinates.continuousOn.mono P.rectangle_subset)

theorem carrier_subset_target : P.carrier ⊆ P.coordinates.target := by
  rintro _ ⟨z, hz, rfl⟩
  exact P.coordinates.map_source (P.rectangle_subset hz)

variable [T2Space M]

theorem closure_openCarrier : closure P.openCarrier = P.carrier := by
  apply subset_antisymm
  · exact closure_minimal P.openCarrier_subset_carrier P.isCompact_carrier.isClosed
  · rintro _ ⟨z, hz, rfl⟩
    have hzclosure : z ∈ closure (crossingOpenRectangle (ry ^ 2) (rx ^ 2) P.width) := by
      rwa [closure_crossingOpenRectangle _ _ P.width_pos]
    exact mem_closure_image (P.coordinates.continuousAt (P.rectangle_subset hz)) hzclosure

theorem isCompact_closure_openCarrier : IsCompact (closure P.openCarrier) := by
  rw [P.closure_openCarrier]
  exact P.isCompact_carrier

end ChartCircleCrossingPatch

variable [IsManifold (𝓡 2) ∞ M]



theorem exists_chartCircle_crossing_patch (x y : M) {rx ry : ℝ}
    (hrx : 0 < rx) (hry : 0 < ry)
    (hxsub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) rx ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (hysub : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) y y) ry ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) y).target)
    {p : M} (hpx : p ∈ chartCircle x rx) (hpy : p ∈ chartCircle y ry)
    (hregular : ChartCircleRegularAlong x rx y ry)
    {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ P : ChartCircleCrossingPatch x y rx ry p, P.carrier ⊆ N := by
  obtain ⟨C, hpC, htarget, hC, hCinv, hcenter, hradius, hcy, hcx⟩ :=
    exists_chartCircle_crossing_coordinates x y hrx hry hxsub hysub hpx hpy hregular
  let c := collarParameterEquiv.symm (ry ^ 2, rx ^ 2)
  have hc : c ∈ C.source := by
    change collarParameterEquiv.symm (ry ^ 2, rx ^ 2) ∈ C.source
    rw [← hcenter]
    exact C.map_target hpC
  have hCc : C c = p := by
    change C (collarParameterEquiv.symm (ry ^ 2, rx ^ 2)) = p
    rw [← hcenter]
    exact C.right_inv hpC
  have hsource : C.source ∩ C ⁻¹' N ∈ 𝓝 c :=
    Filter.inter_mem (C.open_source.mem_nhds hc)
      ((C.continuousAt hc).preimage_mem_nhds (hCc.symm ▸ hN))
  have hproduct : collarParameterEquiv.symm ⁻¹' (C.source ∩ C ⁻¹' N) ∈
      𝓝 (ry ^ 2, rx ^ 2) :=
    collarParameterEquiv.symm.continuous.continuousAt.preimage_mem_nhds hsource
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hproduct
  have hrectangle : crossingClosedRectangle (ry ^ 2) (rx ^ 2) (δ / 2) ⊆
      C.source ∩ C ⁻¹' N := by
    intro z hz
    have hz' : collarParameterEquiv z ∈ ball (ry ^ 2, rx ^ 2) δ :=
      closedBall_subset_ball (half_lt_self hδ) hz
    have h := hδsub hz'
    change collarParameterEquiv.symm (collarParameterEquiv z) ∈ C.source ∩ C ⁻¹' N at h
    simpa only [collarParameterEquiv.symm_apply_apply] using h
  let P : ChartCircleCrossingPatch x y rx ry p := {
    coordinates := C
    width := δ / 2
    width_pos := half_pos hδ
    point_mem := hpC
    center_eq := hcenter
    target_subset := htarget
    smooth := hC
    smooth_symm := hCinv
    rectangle_subset := fun _ hz => (hrectangle hz).1
    squaredRadius := hradius
    circle_y := hcy
    circle_x := hcx }
  refine ⟨P, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (hrectangle hz).2


def chartCircleCrossings (s : Finset M) (r : M → ℝ) : Set M :=
  {p | ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ p ∈ chartCircle x (r x) ∩ chartCircle y (r y)}

omit [IsManifold (𝓡 2) ∞ M] in

theorem finite_chartCircleCrossings (s : Finset M) (r : M → ℝ)
    (hfinite : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      (chartCircle x (r x) ∩ chartCircle y (r y)).Finite) :
    (chartCircleCrossings s r).Finite := by
  classical
  have hfin : (⋃ x ∈ s, ⋃ y ∈ s,
      if x = y then ∅ else chartCircle x (r x) ∩ chartCircle y (r y)).Finite := by
    apply s.finite_toSet.biUnion
    intro x hx
    apply s.finite_toSet.biUnion
    intro y hy
    split_ifs with hxy
    · exact finite_empty
    · exact hfinite x hx y hy hxy
  apply hfin.subset
  rintro p ⟨x, hx, y, hy, hxy, hp⟩
  exact mem_iUnion₂.mpr ⟨x, hx, mem_iUnion₂.mpr ⟨y, hy, by simpa only [hxy, ↓reduceIte] using hp⟩⟩

variable [T2Space M]





theorem exists_disjoint_chartCircle_crossing_patches
    (s : Finset M) (r : M → ℝ) (hpos : ∀ x ∈ s, 0 < r x)
    (htarget : ∀ x ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (hfinite : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      (chartCircle x (r x) ∩ chartCircle y (r y)).Finite)
    (htriple : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z →
      ∀ p ∈ chartCircle x (r x), p ∈ chartCircle y (r y) →
        p ∉ chartCircle z (r z))
    (hregular : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ChartCircleRegularAlong x (r x) y (r y) ∨
        ChartCircleRegularAlong y (r y) x (r x))
    (N : M → Set M) (hN : ∀ p ∈ chartCircleCrossings s r, N p ∈ 𝓝 p) :
    ∃ (x y : chartCircleCrossings s r → M)
      (P : ∀ p : chartCircleCrossings s r,
        ChartCircleCrossingPatch (x p) (y p) (r (x p)) (r (y p)) p),
      (∀ p, x p ∈ s ∧ y p ∈ s ∧ x p ≠ y p ∧
        (p : M) ∈ chartCircle (x p) (r (x p)) ∩ chartCircle (y p) (r (y p))) ∧
      (∀ p, (P p).carrier ⊆ N p) ∧
      (∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier) ∧
      (∀ p z, z ∈ s → z ≠ x p → z ≠ y p →
        Disjoint (P p).carrier (chartCircle z (r z))) ∧
      (∀ p q, q ∈ (P p).carrier →
        (q ∈ ⋃ z ∈ s, chartCircle z (r z) ↔
          q ∈ chartCircle (x p) (r (x p)) ∪ chartCircle (y p) (r (y p)))) := by
  classical
  have hpair (p : chartCircleCrossings s r) :
      ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧
        (p : M) ∈ chartCircle x (r x) ∩ chartCircle y (r y) ∧
        ChartCircleRegularAlong x (r x) y (r y) := by
    obtain ⟨x, hx, y, hy, hxy, hp⟩ := p.property
    rcases hregular x hx y hy hxy with hreg | hreg
    · exact ⟨x, hx, y, hy, hxy, hp, hreg⟩
    · exact ⟨y, hy, x, hx, hxy.symm, ⟨hp.2, hp.1⟩, hreg⟩
  choose x hx y hy hxy hp hreg using hpair
  obtain ⟨U, hU, hdisjoint⟩ := (finite_chartCircleCrossings s r hfinite).t2_separation
  let other (p : chartCircleCrossings s r) := s.filter (fun z => z ≠ x p ∧ z ≠ y p)
  let A (p : chartCircleCrossings s r) := ⋃ z ∈ other p, chartCircle z (r z)
  have hA (p : chartCircleCrossings s r) : IsCompact (A p) :=
    (other p).isCompact_biUnion fun z hz =>
      isCompact_chartCircle z (htarget z (Finset.mem_filter.mp hz).1)
  have hpA (p : chartCircleCrossings s r) : (p : M) ∉ A p := by
    intro h
    obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp h
    obtain ⟨hzs, hzx, hzy⟩ := Finset.mem_filter.mp hz
    exact htriple (x p) (hx p) (y p) (hy p) z hzs (hxy p) hzx.symm hzy.symm
      p (hp p).1 (hp p).2 hpz
  have hpatch (p : chartCircleCrossings s r) :
      ∃ P : ChartCircleCrossingPatch (x p) (y p) (r (x p)) (r (y p)) p,
        P.carrier ⊆ (U p ∩ N p) ∩ (A p)ᶜ := by
    apply exists_chartCircle_crossing_patch (x p) (y p)
      (hpos (x p) (hx p)) (hpos (y p) (hy p)) (htarget (x p) (hx p))
      (htarget (y p) (hy p)) (hp p).1 (hp p).2 (hreg p)
    exact Filter.inter_mem
      (Filter.inter_mem ((hU p).2.mem_nhds (hU p).1) (hN p p.property))
      ((hA p).isClosed.isOpen_compl.mem_nhds (hpA p))
  choose P hP using hpatch
  have havoid (p : chartCircleCrossings s r) (z : M) (hz : z ∈ s)
      (hzx : z ≠ x p) (hzy : z ≠ y p) : Disjoint (P p).carrier (chartCircle z (r z)) := by
    apply disjoint_left.mpr
    intro q hq hqz
    exact (hP p hq).2 (mem_iUnion₂.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hz, hzx, hzy⟩, hqz⟩)
  refine ⟨x, y, P, fun p => ⟨hx p, hy p, hxy p, hp p⟩,
    fun p q hq => (hP p hq).1.2, ?_, havoid, ?_⟩
  · intro p q hpq
    exact (hdisjoint p.property q.property (fun heq => hpq (Subtype.ext heq))).mono
      (fun z hz => (hP p hz).1.1) (fun z hz => (hP q hz).1.1)
  · intro p q hq
    constructor
    · intro hqK
      obtain ⟨z, hz, hqz⟩ := mem_iUnion₂.mp hqK
      by_cases hzx : z = x p
      · exact Or.inl (hzx ▸ hqz)
      by_cases hzy : z = y p
      · exact Or.inr (hzy ▸ hqz)
      exact (disjoint_left.mp (havoid p z hz hzx hzy) hq hqz).elim
    · rintro (hqx | hqy)
      · exact mem_iUnion₂.mpr ⟨x p, hx p, hqx⟩
      · exact mem_iUnion₂.mpr ⟨y p, hy p, hqy⟩

end PoincareConjecture.Topology.Surface

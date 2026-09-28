


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.VertexCoordinates










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]


inductive ChartCircleArrangementVertexPatch (r : M → ℝ) (p : M)
  | single (x : M) (patch : ChartCircleVertexPatch x (r x) p)
  | crossing (x y : M) (distinct : x ≠ y)
      (patch : ChartCircleCrossingPatch x y (r x) (r y) p)

namespace ChartCircleArrangementVertexPatch

variable {r : M → ℝ} {p : M}


def centers : ChartCircleArrangementVertexPatch r p → Set M
  | .single x _ => {x}
  | .crossing x y _ _ => {x, y}


def circles (P : ChartCircleArrangementVertexPatch r p) : Set M :=
  ⋃ x ∈ P.centers, chartCircle x (r x)


def coordinates : ChartCircleArrangementVertexPatch r p →
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M
  | .single _ P => P.coordinates
  | .crossing _ _ _ P => P.coordinates


def center : ChartCircleArrangementVertexPatch r p → ℝ × ℝ
  | .single _ _ => (0, 0)
  | .crossing x y _ _ => ((r y) ^ 2, (r x) ^ 2)


def width : ChartCircleArrangementVertexPatch r p → ℝ
  | .single _ P => P.width
  | .crossing _ _ _ P => P.width


def openCarrier : ChartCircleArrangementVertexPatch r p → Set M
  | .single _ P => P.openCarrier
  | .crossing _ _ _ P => P.openCarrier


def carrier : ChartCircleArrangementVertexPatch r p → Set M
  | .single _ P => P.carrier
  | .crossing _ _ _ P => P.carrier


def axes : ChartCircleArrangementVertexPatch r p → Set (EuclideanSpace ℝ (Fin 2))
  | .single _ _ => {z | z 0 = 0}
  | .crossing x y _ _ => {z | z 0 = (r y) ^ 2 ∨ z 1 = (r x) ^ 2}

variable (P : ChartCircleArrangementVertexPatch r p)

theorem carrier_eq_image_rectangle :
    P.carrier = P.coordinates '' crossingClosedRectangle P.center.1 P.center.2 P.width := by
  cases P <;> rfl

theorem openCarrier_eq_image_rectangle :
    P.openCarrier = P.coordinates '' crossingOpenRectangle P.center.1 P.center.2 P.width := by
  cases P <;> rfl

theorem coordinates_mem_circles_iff {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ P.coordinates.source) : P.coordinates z ∈ P.circles ↔ z ∈ P.axes := by
  cases P with
  | single x P =>
    simpa only [coordinates, circles, centers, biUnion_singleton, axes, mem_ofPred_eq]
      using P.circle z hz
  | crossing x y _ P =>
    simp only [coordinates, circles, centers, biUnion_insert, biUnion_singleton,
      mem_union, axes, mem_ofPred_eq]
    rw [P.circle_x z hz, P.circle_y z hz]
    exact or_comm

theorem centers_finite : P.centers.Finite := by
  cases P with
  | single x _ => exact finite_singleton x
  | crossing x y _ _ => exact (finite_singleton y).insert x

theorem width_pos : 0 < P.width := by
  cases P with
  | single _ P => exact P.width_pos
  | crossing _ _ _ P => exact P.width_pos

theorem rectangle_subset :
    crossingClosedRectangle P.center.1 P.center.2 P.width ⊆ P.coordinates.source := by
  cases P with
  | single _ P => exact P.rectangle_subset
  | crossing _ _ _ P => exact P.rectangle_subset

theorem center_eq : P.coordinates.symm p = collarParameterEquiv.symm P.center := by
  cases P with
  | single _ P =>
    change P.coordinates.symm p = collarParameterEquiv.symm (0 : ℝ × ℝ)
    rw [map_zero]
    exact P.center_eq
  | crossing _ _ _ P => exact P.center_eq

theorem smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ P.coordinates P.coordinates.source := by
  cases P with
  | single _ P => exact P.smooth
  | crossing _ _ _ P => exact P.smooth

theorem smooth_symm :
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ P.coordinates.symm P.coordinates.target := by
  cases P with
  | single _ P => exact P.smooth_symm
  | crossing _ _ _ P => exact P.smooth_symm

theorem openCarrier_subset_carrier : P.openCarrier ⊆ P.carrier := by
  cases P with
  | single _ P => exact P.openCarrier_subset_carrier
  | crossing _ _ _ P => exact P.openCarrier_subset_carrier

theorem isOpen_openCarrier : IsOpen P.openCarrier := by
  cases P with
  | single _ P => exact P.isOpen_openCarrier
  | crossing _ _ _ P => exact P.isOpen_openCarrier

theorem mem_openCarrier : p ∈ P.openCarrier := by
  cases P with
  | single _ P => exact P.mem_openCarrier
  | crossing _ _ _ P => exact P.mem_openCarrier

theorem isCompact_carrier : IsCompact P.carrier := by
  cases P with
  | single _ P => exact P.isCompact_carrier
  | crossing _ _ _ P => exact P.isCompact_carrier

theorem carrier_subset_target : P.carrier ⊆ P.coordinates.target := by
  cases P with
  | single _ P => exact P.carrier_subset_target
  | crossing _ _ _ P => exact P.carrier_subset_target

variable [T2Space M]

theorem closure_openCarrier : closure P.openCarrier = P.carrier := by
  cases P with
  | single _ P => exact P.closure_openCarrier
  | crossing _ _ _ P => exact P.closure_openCarrier

end ChartCircleArrangementVertexPatch

variable [T2Space M] [IsManifold (𝓡 2) ∞ M]



theorem exists_chartCircle_arrangement_vertex_patch
    (s : Finset M) (r : M → ℝ) (hpos : ∀ x ∈ s, 0 < r x)
    (htarget : ∀ x ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (htriple : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z →
      ∀ p ∈ chartCircle x (r x), p ∈ chartCircle y (r y) →
        p ∉ chartCircle z (r z))
    (hregular : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ChartCircleRegularAlong x (r x) y (r y) ∨
        ChartCircleRegularAlong y (r y) x (r x))
    {p : M} (hp : p ∈ ⋃ x ∈ s, chartCircle x (r x))
    {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ P : ChartCircleArrangementVertexPatch r p,
      P.centers ⊆ (s : Set M) ∧
      (∀ x ∈ s, p ∈ chartCircle x (r x) ↔ x ∈ P.centers) ∧
      P.carrier ⊆ N ∧
      (∀ x ∈ s, x ∉ P.centers → Disjoint P.carrier (chartCircle x (r x))) := by
  classical
  let absent := s.filter (fun x => p ∉ chartCircle x (r x))
  let A := ⋃ x ∈ absent, chartCircle x (r x)
  have hA : IsCompact A := absent.isCompact_biUnion fun x hx =>
    isCompact_chartCircle x (htarget x (Finset.mem_filter.mp hx).1)
  have hpA : p ∉ A := by
    intro h
    obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.mp h
    exact (Finset.mem_filter.mp hx).2 hpx
  have hNA : N ∩ Aᶜ ∈ 𝓝 p :=
    Filter.inter_mem hN (hA.isClosed.isOpen_compl.mem_nhds hpA)
  have hpatch : ∃ P : ChartCircleArrangementVertexPatch r p,
      P.centers ⊆ (s : Set M) ∧
      (∀ x ∈ s, p ∈ chartCircle x (r x) ↔ x ∈ P.centers) ∧
      P.carrier ⊆ N ∩ Aᶜ := by
    obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.mp hp
    by_cases htwo : ∃ y ∈ s, y ≠ x ∧ p ∈ chartCircle y (r y)
    · obtain ⟨y, hy, hyx, hpy⟩ := htwo
      have hpair : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧
          p ∈ chartCircle x (r x) ∩ chartCircle y (r y) ∧
          ChartCircleRegularAlong x (r x) y (r y) := by
        rcases hregular x hx y hy hyx.symm with h | h
        · exact ⟨x, hx, y, hy, hyx.symm, ⟨hpx, hpy⟩, h⟩
        · exact ⟨y, hy, x, hx, hyx, ⟨hpy, hpx⟩, h⟩
      obtain ⟨i, hi, j, hj, hij, hpij, hreg⟩ := hpair
      obtain ⟨Q, hQ⟩ := exists_chartCircle_crossing_patch i j
        (hpos i hi) (hpos j hj) (htarget i hi) (htarget j hj)
        hpij.1 hpij.2 hreg hNA
      refine ⟨.crossing i j hij Q, ?_, ?_, hQ⟩
      · rintro z (rfl | rfl)
        · exact hi
        · exact hj
      · intro z hz
        change p ∈ chartCircle z (r z) ↔ z = i ∨ z = j
        constructor
        · intro hpz
          by_cases hzi : z = i
          · exact Or.inl hzi
          by_cases hzj : z = j
          · exact Or.inr hzj
          exact (htriple i hi j hj z hz hij (Ne.symm hzi) (Ne.symm hzj)
            p hpij.1 hpij.2 hpz).elim
        · rintro (rfl | rfl)
          · exact hpij.1
          · exact hpij.2
    · obtain ⟨Q, hQ⟩ := exists_chartCircle_vertex_patch x (hpos x hx) (htarget x hx) hpx hNA
      refine ⟨.single x Q, ?_, ?_, hQ⟩
      · intro z hz
        have hzx : z = x := hz
        exact hzx.symm ▸ hx
      · intro z hz
        change p ∈ chartCircle z (r z) ↔ z = x
        constructor
        · intro hpz
          by_contra hzx
          exact htwo ⟨z, hz, hzx, hpz⟩
        · rintro rfl
          exact hpx
  obtain ⟨P, hcenters, hincidence, hP⟩ := hpatch
  refine ⟨P, hcenters, hincidence, fun q hq => (hP hq).1, ?_⟩
  intro x hx hnot
  apply disjoint_left.mpr
  intro q hq hqx
  exact (hP hq).2 (mem_iUnion₂.mpr
    ⟨x, Finset.mem_filter.mpr ⟨hx, fun hpx => hnot ((hincidence x hx).mp hpx)⟩, hqx⟩)



theorem exists_disjoint_chartCircle_arrangement_vertex_patches
    (s : Finset M) (r : M → ℝ) (hpos : ∀ x ∈ s, 0 < r x)
    (htarget : ∀ x ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (htriple : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z →
      ∀ p ∈ chartCircle x (r x), p ∈ chartCircle y (r y) →
        p ∉ chartCircle z (r z))
    (hregular : ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      ChartCircleRegularAlong x (r x) y (r y) ∨
        ChartCircleRegularAlong y (r y) x (r x))
    (V : Finset M) (hV : ∀ p ∈ V, p ∈ ⋃ x ∈ s, chartCircle x (r x))
    (N : M → Set M) (hN : ∀ p ∈ V, N p ∈ 𝓝 p) :
    ∃ P : ∀ p : V, ChartCircleArrangementVertexPatch r p,
      (∀ p, (P p).centers ⊆ (s : Set M)) ∧
      (∀ p : V, ∀ x ∈ s, (p : M) ∈ chartCircle x (r x) ↔ x ∈ (P p).centers) ∧
      (∀ p, (P p).carrier ⊆ N p) ∧
      (∀ p q, p ≠ q → Disjoint (P p).carrier (P q).carrier) ∧
      (∀ p, ∀ x ∈ s, x ∉ (P p).centers →
        Disjoint (P p).carrier (chartCircle x (r x))) ∧
      (∀ p q, q ∈ (P p).carrier →
        (q ∈ ⋃ x ∈ s, chartCircle x (r x) ↔ q ∈ (P p).circles)) := by
  classical
  obtain ⟨U, hU, hdisjoint⟩ := V.finite_toSet.t2_separation
  have hpatch (p : V) : ∃ P : ChartCircleArrangementVertexPatch r p,
      P.centers ⊆ (s : Set M) ∧
      (∀ x ∈ s, (p : M) ∈ chartCircle x (r x) ↔ x ∈ P.centers) ∧
      P.carrier ⊆ N p ∩ U p ∧
      (∀ x ∈ s, x ∉ P.centers → Disjoint P.carrier (chartCircle x (r x))) := by
    apply exists_chartCircle_arrangement_vertex_patch s r hpos htarget htriple hregular
      (hV p p.property)
    exact Filter.inter_mem (hN p p.property) ((hU p).2.mem_nhds (hU p).1)
  choose P hcenters hincidence hP havoid using hpatch
  refine ⟨P, hcenters, hincidence, fun p q hq => (hP p hq).1, ?_, havoid, ?_⟩
  · intro p q hpq
    exact (hdisjoint p.property q.property (fun h => hpq (Subtype.ext h))).mono
      (fun z hz => (hP p hz).2) (fun z hz => (hP q hz).2)
  · intro p q hq
    constructor
    · intro hqK
      obtain ⟨x, hx, hqx⟩ := mem_iUnion₂.mp hqK
      by_cases hxP : x ∈ (P p).centers
      · exact mem_iUnion₂.mpr ⟨x, hxP, hqx⟩
      · exact (disjoint_left.mp (havoid p x hx hxP) hq hqx).elim
    · intro hqP
      obtain ⟨x, hx, hqx⟩ := mem_iUnion₂.mp hqP
      exact mem_iUnion₂.mpr ⟨x, hcenters p hx, hqx⟩

end PoincareConjecture.Topology.Surface

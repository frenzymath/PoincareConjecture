import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Pointed
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.FlowCarrier

attribute [local instance] topologicalSpace chartedSpace secondCountable

structure CoordinateCylinder {n : ℕ} (C : FlowCarrier n) (a b : ℝ) where
  center : C.carrier
  coordinate : EuclideanSpace ℝ (Fin n)
  radius : ℝ
  radius_pos : 0 < radius
  lower : ℝ
  upper : ℝ
  lower_lt_upper : lower < upper
  time_subset : Icc lower upper ⊆ Ioo a b
  chart_subset : Metric.closedBall coordinate (2 * radius) ⊆
    (chartAt (EuclideanSpace ℝ (Fin n)) center).target

namespace CoordinateCylinder

variable {n : ℕ} {C : FlowCarrier n} {a b : ℝ}

def coordinateDomain (d : CoordinateCylinder C a b) : Set (EuclideanSpace ℝ (Fin n) × ℝ) :=
  Metric.closedBall d.coordinate d.radius ×ˢ Icc d.lower d.upper

def domain (d : CoordinateCylinder C a b) : Set (C.carrier × ℝ) :=
  ((chartAt (EuclideanSpace ℝ (Fin n)) d.center).symm ''
    Metric.ball d.coordinate d.radius) ×ˢ Ioo d.lower d.upper

theorem ball_subset_chart (d : CoordinateCylinder C a b) :
    Metric.ball d.coordinate d.radius ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) d.center).target := by
  intro x hx
  apply d.chart_subset
  change dist x d.coordinate ≤ 2 * d.radius
  have hd : dist x d.coordinate < d.radius := hx
  linarith [d.radius_pos]

theorem domain_open (d : CoordinateCylinder C a b) : IsOpen d.domain :=
  ((chartAt (EuclideanSpace ℝ (Fin n)) d.center).symm.isOpen_image_of_subset_source
    Metric.isOpen_ball d.ball_subset_chart).prod isOpen_Ioo

theorem domain_subset (d : CoordinateCylinder C a b) : d.domain ⊆ univ ×ˢ Ioo a b :=
  fun _ hx => ⟨mem_univ _, d.time_subset ⟨hx.2.1.le, hx.2.2.le⟩⟩

theorem isCompact_coordinateDomain (d : CoordinateCylinder C a b) :
    IsCompact d.coordinateDomain :=
  (isCompact_closedBall _ _).prod isCompact_Icc

noncomputable def param (d : CoordinateCylinder C a b)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) : C.carrier × ℝ :=
  ((chartAt (EuclideanSpace ℝ (Fin n)) d.center).symm z.1, z.2)

theorem coordinate_mem (d : CoordinateCylinder C a b) {z : C.carrier × ℝ}
    (hz : z ∈ d.domain) :
    ((chartAt (EuclideanSpace ℝ (Fin n)) d.center) z.1, z.2) ∈ d.coordinateDomain := by
  obtain ⟨x, hx, heq⟩ := hz.1
  refine ⟨?_, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  rw [← heq, (chartAt (EuclideanSpace ℝ (Fin n)) d.center).right_inv
    (d.ball_subset_chart hx)]
  exact Metric.ball_subset_closedBall hx

noncomputable def toCoordinates (d : CoordinateCylinder C a b) : d.domain → d.coordinateDomain :=
  fun z => ⟨((chartAt (EuclideanSpace ℝ (Fin n)) d.center) z.val.1, z.val.2),
    d.coordinate_mem z.property⟩

theorem param_toCoordinates (d : CoordinateCylinder C a b) (z : d.domain) :
    d.param (d.toCoordinates z).val = z.val := by
  apply Prod.ext
  · obtain ⟨x, hx, heq⟩ := z.property.1
    exact (chartAt (EuclideanSpace ℝ (Fin n)) d.center).left_inv
      (heq ▸ (chartAt (EuclideanSpace ℝ (Fin n)) d.center).map_target
        (d.ball_subset_chart hx))
  · rfl

theorem continuous_toCoordinates (d : CoordinateCylinder C a b) : Continuous d.toCoordinates := by
  apply Continuous.subtype_mk
  refine Continuous.prodMk ?_ (continuous_snd.comp continuous_subtype_val)
  apply (chartAt (EuclideanSpace ℝ (Fin n)) d.center).continuousOn.comp_continuous
    (continuous_fst.comp continuous_subtype_val)
  intro z
  obtain ⟨x, hx, heq⟩ := z.property.1
  change z.val.1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) d.center).source
  exact heq ▸ (chartAt (EuclideanSpace ℝ (Fin n)) d.center).map_target (d.ball_subset_chart hx)

end CoordinateCylinder

theorem exists_coordinateCylinder_at {n : ℕ} (C : FlowCarrier n)
    {a b : ℝ} {x : C.carrier × ℝ} (hx : x.2 ∈ Ioo a b) :
    ∃ d : CoordinateCylinder C a b, x ∈ d.domain := by
  let q := x.1
  let z := (chartAt (EuclideanSpace ℝ (Fin n)) q) q
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (chartAt (EuclideanSpace ℝ (Fin n)) q).open_target z (mem_chart_target _ q)
  let d : CoordinateCylinder C a b :=
    { center := q
      coordinate := z
      radius := r / 4
      radius_pos := by positivity
      lower := (a + x.2) / 2
      upper := (x.2 + b) / 2
      lower_lt_upper := by linarith [hx.1, hx.2]
      time_subset := by
        intro t ht
        constructor <;> linarith [ht.1, ht.2, hx.1, hx.2]
      chart_subset := by
        intro y hy
        apply hball
        change dist y z < r
        have hd : dist y z ≤ 2 * (r / 4) := hy
        linarith }
  refine ⟨d, ?_, ?_⟩
  · refine ⟨z, Metric.mem_ball_self (by dsimp [d]; positivity), ?_⟩
    exact (chartAt (EuclideanSpace ℝ (Fin n)) q).left_inv (mem_chart_source _ q)
  · change (a + x.2) / 2 < x.2 ∧ x.2 < (x.2 + b) / 2
    constructor <;> linarith [hx.1, hx.2]

theorem exists_coordinateCylinder_cover {n : ℕ} (C : FlowCarrier n)
    {a b : ℝ} (hab : a < b) :
    ∃ d : ℕ → CoordinateCylinder C a b, univ ×ˢ Ioo a b ⊆ ⋃ i, (d i).domain := by
  classical
  let X := C.carrier × Ioo a b
  have hd (x : X) : ∃ d : CoordinateCylinder C a b, (x.1, x.2.val) ∈ d.domain :=
    C.exists_coordinateCylinder_at x.2.property
  choose d hd using hd
  let U (x : X) : Set X := (fun y : X => (y.1, y.2.val)) ⁻¹' (d x).domain
  have hU (x : X) : U x ∈ 𝓝 x :=
    ((d x).domain_open.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).mem_nhds
      (hd x)
  obtain ⟨A, hA, hcover⟩ := TopologicalSpace.countable_cover_nhds hU
  obtain ⟨p, _⟩ := C.connected.nonempty
  let x₀ : X := (p, ⟨(a + b) / 2, by constructor <;> linarith⟩)
  have hAne : A.Nonempty := by
    have hx : x₀ ∈ ⋃ x ∈ A, U x := hcover.symm ▸ mem_univ x₀
    obtain ⟨x, hx, _⟩ := mem_iUnion₂.mp hx
    exact ⟨x, hx⟩
  obtain ⟨s, hs⟩ := hA.exists_eq_range hAne
  refine ⟨fun i => d (s i), ?_⟩
  intro y hy
  let x : X := (y.1, ⟨y.2, hy.2⟩)
  have hx : x ∈ ⋃ z ∈ A, U z := hcover.symm ▸ mem_univ x
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx
  rw [hs] at hz
  obtain ⟨i, rfl⟩ := hz
  exact mem_iUnion.mpr ⟨i, hxz⟩

end PoincareConjecture.FlowCarrier

import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedCapCoordinates

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.HamiltonMarkedCapCoordinates

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
  {D S : Set X} {eps : ℝ} {g : S × Ico (0 : ℝ) eps → X}
  (c d : HamiltonMarkedCapCoordinates (E := E) (D := D) g)

theorem transition_nonneg (hg : ∀ p, g p ∈ D)
    (p : ℝ × E) (hp : p ∈ (c.chart.symm.trans d.chart).source) (ht : 0 ≤ p.1) :
    p ∈ (c.original.symm.trans d.original).source ∧
      (c.chart.symm.trans d.chart) p = (c.original.symm.trans d.original) p := by
  let x := c.chart.symm p
  let q := d.chart x
  have hx : x ∈ c.chart.source := c.chart.map_target hp.1
  have hxnot : x ∉ interior D := by
    intro hxD
    have h := (c.interior_side hg x hx).mp hxD
    change (c.chart (c.chart.symm p)).1 < 0 at h
    rw [c.chart.right_inv hp.1] at h
    exact not_lt_of_ge ht h
  have hq : q ∈ d.chart.target := d.chart.map_source hp.2
  have hqt : 0 ≤ q.1 := le_of_not_gt fun h => hxnot ((d.interior_side hg x hp.2).mpr h)
  obtain ⟨hxB, hcp⟩ := c.coordinates_nonneg p hp.1 ht
  obtain ⟨hxB', hdq⟩ := d.coordinates_nonneg q hq hqt
  have hqx : d.chart.symm q = x := d.chart.left_inv hp.2
  rw [hqx] at hxB' hdq
  have hpinv := c.inverse_nonneg p hp.1 ht
  refine ⟨⟨c.rectangle (c.target.subset hp.1), ?_⟩, ?_⟩
  · change c.original.symm p ∈ d.original.source
    rw [← hpinv]
    exact hxB'
  · change q = d.original (c.original.symm p)
    rw [← hpinv]
    exact hdq.symm

theorem transition_nonpos (hg : ∀ p, g p ∈ D) (hinj : Function.Injective g)
    (p : ℝ × E) (hp : p ∈ (c.chart.symm.trans d.chart).source) (ht : p.1 ≤ 0) :
    (0, p.2) ∈ (c.original.symm.trans d.original).source ∧
      (c.chart.symm.trans d.chart) p =
        (p.1, ((c.original.symm.trans d.original) (0, p.2)).2) := by
  let x := c.chart.symm p
  let q := d.chart x
  have hx : x ∈ c.chart.source := c.chart.map_target hp.1
  have hxD : x ∈ D := by
    apply (c.side hg x hx).mpr
    change (c.chart (c.chart.symm p)).1 ≤ 0
    rw [c.chart.right_inv hp.1]
    exact ht
  have hqt : q.1 ≤ 0 := (d.side hg x hp.2).mp hxD
  have hq : q ∈ d.chart.target := d.chart.map_source hp.2
  obtain ⟨tc, htc, _, hcx⟩ := c.inverse_nonpos p hp.1 ht
  obtain ⟨td, htd, _, hdx⟩ := d.inverse_nonpos q hq hqt
  have hqx : d.chart.symm q = x := d.chart.left_inv hp.2
  rw [hqx] at hdx
  have hpair : (c.boundary.symm p.2, tc) = (d.boundary.symm q.2, td) :=
    hinj (hcx.symm.trans hdx)
  have hbase : c.boundary.symm p.2 = d.boundary.symm q.2 := congrArg Prod.fst hpair
  have hdepth : (tc : ℝ) = (td : ℝ) := congrArg (fun u => (u.2 : ℝ)) hpair
  rw [htc, htd] at hdepth
  have hfirst : q.1 = p.1 := (neg_injective hdepth).symm
  have hpbt : p.2 ∈ c.boundary.target :=
    c.lateral_subset_boundary_target (c.target.subset hp.1).2
  have hqbt : q.2 ∈ d.boundary.target :=
    d.lateral_subset_boundary_target (d.target.subset hq).2
  have hpzero : (0, p.2) ∈ c.original.target := by
    rw [c.boundary_target] at hpbt
    exact hpbt
  have hqzero : (0, q.2) ∈ d.original.target := by
    rw [d.boundary_target] at hqbt
    exact hqbt
  have hzero : c.original.symm (0, p.2) = d.original.symm (0, q.2) := by
    rw [← c.boundary_inverse p.2 hpbt, ← d.boundary_inverse q.2 hqbt, hbase]
  have hT : (c.original.symm.trans d.original) (0, p.2) = (0, q.2) := by
    change d.original (c.original.symm (0, p.2)) = (0, q.2)
    rw [hzero, d.original.right_inv hqzero]
  refine ⟨⟨hpzero, ?_⟩, ?_⟩
  · change c.original.symm (0, p.2) ∈ d.original.source
    rw [hzero]
    exact d.original.map_target hqzero
  · change q = (p.1, ((c.original.symm.trans d.original) (0, p.2)).2)
    rw [hT]
    exact Prod.ext hfirst rfl

end PoincareConjecture.M76.HamiltonMarkedCapCoordinates




import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.CircleCover.GeneralPosition
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions








set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]



theorem isCompact_chartCircle (x : M) {r : ℝ}
    (htarget : closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    IsCompact (chartCircle x r) :=
  (isCompact_sphere _ _).image_of_continuousOn
    ((chartAt (EuclideanSpace ℝ (Fin 2)) x).continuousOn_symm.mono
      (sphere_subset_closedBall.trans htarget))

variable [T2Space M]



theorem chartDiskBoundaryUnion_eq_iUnion_chartCircle (s : Finset M) (r : M → ℝ)
    (hpos : ∀ x ∈ s, 0 < r x)
    (htarget : ∀ x ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    chartDiskBoundaryUnion s r = ⋃ x ∈ s, chartCircle x (r x) := by
  unfold chartDiskBoundaryUnion
  apply iUnion_congr
  intro x
  apply iUnion_congr
  intro hx
  rw [frontier_chart_image x (isCompact_closedBall _ _) (htarget x hx),
    frontier_closedBall _ (hpos x hx).ne']
  rfl



theorem exists_open_chartCircle_locality (s : Finset M) (r : M → ℝ)
    (htarget : ∀ x ∈ s,
      closedBall (chartAt (EuclideanSpace ℝ (Fin 2)) x x) (r x) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (htriple : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z →
      ∀ p ∈ chartCircle x (r x), p ∈ chartCircle y (r y) →
        p ∉ chartCircle z (r z))
    {p : M} (hp : p ∈ ⋃ x ∈ s, chartCircle x (r x)) :
    ∃ N : Set M, IsOpen N ∧ p ∈ N ∧
      ((∃ i ∈ s, p ∈ chartCircle i (r i) ∧
        N ∩ (⋃ x ∈ s, chartCircle x (r x)) = N ∩ chartCircle i (r i)) ∨
      (∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧
        p ∈ chartCircle i (r i) ∩ chartCircle j (r j) ∧
        N ∩ (⋃ x ∈ s, chartCircle x (r x)) =
          N ∩ (chartCircle i (r i) ∪ chartCircle j (r j)))) := by
  classical
  let absent := s.filter (fun x => p ∉ chartCircle x (r x))
  let K := ⋃ x ∈ absent, chartCircle x (r x)
  have hKcompact : IsCompact K := absent.isCompact_biUnion (fun x hx =>
    isCompact_chartCircle x (htarget x (Finset.mem_filter.mp hx).1))
  have hpK : p ∉ K := by
    intro h
    obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.mp h
    exact (Finset.mem_filter.mp hx).2 hpx
  have hincident {q : M} (hq : q ∉ K)
      (hqcircle : q ∈ ⋃ x ∈ s, chartCircle x (r x)) :
      ∃ x ∈ s, p ∈ chartCircle x (r x) ∧ q ∈ chartCircle x (r x) := by
    obtain ⟨x, hx, hqx⟩ := mem_iUnion₂.mp hqcircle
    refine ⟨x, hx, ?_, hqx⟩
    by_contra hpx
    exact hq (mem_iUnion₂.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hpx⟩, hqx⟩)
  refine ⟨Kᶜ, hKcompact.isClosed.isOpen_compl, hpK, ?_⟩
  obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp hp
  by_cases htwo : ∃ j ∈ s, j ≠ i ∧ p ∈ chartCircle j (r j)
  · obtain ⟨j, hj, hji, hpj⟩ := htwo
    refine Or.inr ⟨i, hi, j, hj, hji.symm, ⟨hpi, hpj⟩, ?_⟩
    ext q
    constructor
    · rintro ⟨hqN, hqK⟩
      obtain ⟨x, hx, hpx, hqx⟩ := hincident hqN hqK
      refine ⟨hqN, ?_⟩
      by_cases hxi : x = i
      · exact Or.inl (hxi ▸ hqx)
      by_cases hxj : x = j
      · exact Or.inr (hxj ▸ hqx)
      exact (htriple i hi j hj x hx hji.symm (Ne.symm hxi) (Ne.symm hxj)
        p hpi hpj hpx).elim
    · rintro ⟨hqN, hqi | hqj⟩
      · exact ⟨hqN, mem_iUnion₂.mpr ⟨i, hi, hqi⟩⟩
      · exact ⟨hqN, mem_iUnion₂.mpr ⟨j, hj, hqj⟩⟩
  · refine Or.inl ⟨i, hi, hpi, ?_⟩
    ext q
    constructor
    · rintro ⟨hqN, hqK⟩
      obtain ⟨x, hx, hpx, hqx⟩ := hincident hqN hqK
      have hxi : x = i := by
        by_contra h
        exact htwo ⟨x, hx, h, hpx⟩
      exact ⟨hqN, hxi ▸ hqx⟩
    · rintro ⟨hqN, hqi⟩
      exact ⟨hqN, mem_iUnion₂.mpr ⟨i, hi, hqi⟩⟩

end PoincareConjecture.Topology.Surface

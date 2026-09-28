import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.LocalChart

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace Poincare.AncientVolume.ScalarRatio

theorem exists_openChart_of_isometry_subset_coverage
    {A B : Type*} [MetricSpace A] [MetricSpace B]
    {K : Set A} {p : A} (hp : p ∈ interior K)
    (e : K → B) (he : Isometry e) {ρ : ℝ} (hρ : 0 < ρ)
    (hcover : Metric.ball (e ⟨p, interior_subset hp⟩) ρ ⊆ range e) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧
      ∃ (hrK : Metric.ball p r ⊆ K) (F : OpenPartialHomeomorph A B),
        F.source = Metric.ball p r ∧
        F.target = Metric.ball (e ⟨p, interior_subset hp⟩) r ∧
        F p = e ⟨p, interior_subset hp⟩ ∧
        (∀ x (hx : x ∈ Metric.ball p r), F x = e ⟨x, hrK hx⟩) ∧
        (∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r, dist (F x) (F y) = dist x y) ∧
        (∀ x ∈ Metric.ball (e ⟨p, interior_subset hp⟩) r,
          ∀ y ∈ Metric.ball (e ⟨p, interior_subset hp⟩) r,
          dist (F.symm x) (F.symm y) = dist x y) := by
  obtain ⟨R, hR, hRK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  have hhalf : 0 < R / 2 := half_pos hR
  have hclosed : Metric.closedBall p (R / 2) ⊆ K :=
    (Metric.closedBall_subset_ball (half_lt_self hR)).trans hRK
  let e₀ : Metric.closedBall p (R / 2) → B := fun x => e ⟨x.1, hclosed x.property⟩
  have he₀ : Isometry e₀ := by
    apply isometry_iff_dist_eq.mpr
    intro x y
    exact he.dist_eq _ _
  let r := min ρ (R / 2 / 2)
  have hr : 0 < r := lt_min hρ (half_pos hhalf)
  have hrρ : r ≤ ρ := min_le_left _ _
  have hrR : r < R / 2 := (min_le_right _ _).trans_lt (half_lt_self hhalf)
  have hrK : Metric.ball p r ⊆ K :=
    (Metric.ball_subset_closedBall).trans ((Metric.closedBall_subset_closedBall hrR.le).trans hclosed)
  have hcover₀ : Metric.ball (e₀ ⟨p, Metric.mem_closedBall_self hhalf.le⟩) r ⊆ range e₀ := by
    intro y hy
    have hyρ : y ∈ Metric.ball (e ⟨p, interior_subset hp⟩) ρ :=
      (Metric.ball_subset_ball hrρ) hy
    obtain ⟨x, hx⟩ := hcover hyρ
    have hxball : x.1 ∈ Metric.closedBall p (R / 2) := by
      have hd := he.dist_eq x ⟨p, interior_subset hp⟩
      change dist (e x) (e ⟨p, interior_subset hp⟩) = dist x.1 p at hd
      change dist x.1 p ≤ R / 2
      rw [← hd, hx]
      exact hy.le.trans hrR.le
    exact ⟨⟨x.1, hxball⟩, hx⟩
  let F := openChartOfClosedBallCoverage p hhalf e₀ he₀ hr hrR hcover₀
  refine ⟨r, hr, hrρ, hrK, F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact openChartOfClosedBallCoverage_source p hhalf e₀ he₀ hr hrR hcover₀
  · exact openChartOfClosedBallCoverage_target p hhalf e₀ he₀ hr hrR hcover₀
  · exact openChartOfClosedBallCoverage_center p hhalf e₀ he₀ hr hrR hcover₀
  · intro x hx
    exact openChartOfClosedBallCoverage_apply p hhalf e₀ he₀ hr hrR hcover₀ hx
  · intro x hx y hy
    exact openChartOfClosedBallCoverage_dist p hhalf e₀ he₀ hr hrR hcover₀ hx hy
  · intro x hx y hy
    exact openChartOfClosedBallCoverage_symm_dist p hhalf e₀ he₀ hr hrR hcover₀ hx hy

end Poincare.AncientVolume.ScalarRatio

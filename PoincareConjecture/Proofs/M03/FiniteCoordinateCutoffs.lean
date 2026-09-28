import PoincareConjecture.Proofs.M03.CoordinateCutoff









set_option autoImplicit false

open scoped ContDiff Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M03

theorem exists_finite_coordinate_cutoffs
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] :
    ∃ (s : Finset M) (r R : M → ℝ)
      (φ : M → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ c ∈ s,
        0 < r c ∧ r c < R c ∧
        Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin n)) c c) (R c) ⊆
          (chartAt (EuclideanSpace ℝ (Fin n)) c).target ∧
        ContDiff ℝ ∞ (φ c) ∧ HasCompactSupport (φ c) ∧
        (∀ z, φ c z ∈ Icc (0 : ℝ) 1) ∧
        EqOn (φ c) (fun _ => 1)
          (Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin n)) c c) (r c)) ∧
        tsupport (φ c) ⊆
          Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin n)) c c) (R c) ∧
        IsCompact ((chartAt (EuclideanSpace ℝ (Fin n)) c).symm '' tsupport (φ c)) ∧
        (chartAt (EuclideanSpace ℝ (Fin n)) c).symm '' tsupport (φ c) ⊆
          (chartAt (EuclideanSpace ℝ (Fin n)) c).source) ∧
      ∀ x : M, ∃ c ∈ s,
        x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) c).source ∧
        chartAt (EuclideanSpace ℝ (Fin n)) c x ∈
          Metric.ball (chartAt (EuclideanSpace ℝ (Fin n)) c c) (r c) := by
  classical
  choose ε hε hεV using fun c : M =>
    Metric.mem_nhds_iff.mp (chart_target_mem_nhds (EuclideanSpace ℝ (Fin n)) c)
  have hr (c : M) : 0 < ε c / 4 := div_pos (hε c) (by norm_num)
  have hrR (c : M) : ε c / 4 < ε c / 2 := by linarith [hε c]
  choose φ hφ hφc hφrange hφone hφsupp using fun c : M =>
    exists_smooth_coordinate_cutoff
      (chartAt (EuclideanSpace ℝ (Fin n)) c c) (hr c) (hrR c)
  let U : M → Set M := fun c =>
    (chartAt (EuclideanSpace ℝ (Fin n)) c).source ∩
      (chartAt (EuclideanSpace ℝ (Fin n)) c) ⁻¹'
        Metric.ball (chartAt (EuclideanSpace ℝ (Fin n)) c c) (ε c / 4)
  have hUo (c : M) : IsOpen (U c) :=
    (chartAt (EuclideanSpace ℝ (Fin n)) c).continuousOn.isOpen_inter_preimage
      (chartAt (EuclideanSpace ℝ (Fin n)) c).open_source Metric.isOpen_ball
  have hUcover : (univ : Set M) ⊆ ⋃ c, U c := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_chart_source _ x, Metric.mem_ball_self (hr x)⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUo hUcover
  refine ⟨s, (fun c => ε c / 4), (fun c => ε c / 2), φ, ?_, ?_⟩
  · intro c _
    have houter : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin n)) c c)
        (ε c / 2) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) c).target :=
      (Metric.closedBall_subset_ball (by linarith [hε c])).trans (hεV c)
    have htarget := (hφsupp c).trans houter
    refine ⟨hr c, hrR c, houter, hφ c, hφc c, hφrange c, hφone c, hφsupp c, ?_, ?_⟩
    · exact (hφc c).image_of_continuousOn
        ((chartAt (EuclideanSpace ℝ (Fin n)) c).continuousOn_symm.mono htarget)
    · rintro _ ⟨z, hz, rfl⟩
      exact (chartAt (EuclideanSpace ℝ (Fin n)) c).map_target (htarget hz)
  · intro x
    obtain ⟨c, hc⟩ := mem_iUnion.mp (hs (mem_univ x))
    obtain ⟨hcs, hx⟩ := mem_iUnion.mp hc
    exact ⟨c, hcs, hx⟩

end PoincareConjecture.Proofs.M03

import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Window
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.LocalControl

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

theorem exists_expanding_source_window_compactness
    {n : ℕ} {s' s : ℝ}
    (Href : PointedRicciFlowCompactnessHypotheses n s' s)
    {J : ℕ → Set ℝ}
    (Fseq : ∀ k, RicciFlow n (Href.sequence.carrier k).carrier (J k))
    (hmetric : ∀ k,
      (Fseq k).metric 0 = (Href.sequence.flow k).flow.metric 0)
    {a b : ℝ} (hab : a < 0 ∧ 0 < b)
    (htime : ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcurv : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ k in atTop,
      ∀ t ∈ Ioo a b, ∀ x : (Href.sequence.carrier k).carrier,
        ((Fseq k).connection t).curvatureTensorNorm x ≤ K) :
    ∃ (N : ℕ) (hsub : ∀ k, Ioo a b ⊆ J (k + N)),
      ∃ H : PointedRicciFlowCompactnessHypotheses n a b,
        H.sequence = sourceWindowSequence Href.sequence.carrier Fseq
          (fun k => (Href.sequence.flow k).base) N hsub
          (hab.1.trans hab.2) := by
  obtain ⟨N, hsub⟩ := exists_source_window_tail htime
  let S := sourceWindowSequence Href.sequence.carrier Fseq
    (fun k => (Href.sequence.flow k).base) N hsub (hab.1.trans hab.2)
  have hball (k : ℕ) (r : ℝ) :
      (S.flow k).zeroBall r = (Href.sequence.flow (k + N)).zeroBall r := by
    change (Href.sequence.carrier (k + N)).metricBall
      ((Fseq (k + N)).metric 0) (Href.sequence.flow (k + N)).base r = _
    rw [hmetric]
    rfl
  have hvolume (k : ℕ) (r : ℝ) :
      (S.flow k).zeroBallVolume r = (Href.sequence.flow (k + N)).zeroBallVolume r := by
    change (Href.sequence.carrier (k + N)).metricHausdorffVolume
      ((Fseq (k + N)).metric 0) ((S.flow k).zeroBall r) = _
    rw [hball, hmetric, ← Href.volume_compatibility (k + N)]
    rfl
  obtain ⟨K, hK, hcurv⟩ := hcurv
  have htail := (Filter.tendsto_add_atTop_nat N).eventually hcurv
  let H : PointedRicciFlowCompactnessHypotheses n a b := {
    time_bounds := hab
    sequence := S
    volume_compatibility := fun _ => rfl
    zero_time_ball_compact := by
      intro A hA
      filter_upwards [(Filter.tendsto_add_atTop_nat N).eventually
        (Href.zero_time_ball_compact A hA)] with k hk
      change IsCompact (closure ((S.flow k).zeroBall A))
      rw [hball]
      exact hk
    spacetime_control := by
      intro A _ I _ _ _ hI
      refine ⟨K, hK, ?_⟩
      filter_upwards [htail] with k hk
      refine ⟨SmoothSpacetimeEmbedding.refl (S.flow k)
        (I ×ˢ (S.flow k).zeroBall A), fun _ _ => rfl, ?_⟩
      exact ⟨hK, fun t ht x _ => hk t (hI ht) x⟩
    all_time_curvature_control := by
      intro A _
      refine ⟨K, hK, ?_⟩
      filter_upwards [htail] with k hk
      dsimp only
      intro _ _ t ht x _
      exact hk t ht x
    noncollapsing := by
      obtain ⟨r, κ, hr, hκ, hvol⟩ := Href.noncollapsing
      refine ⟨r, κ, hr, hκ, ?_⟩
      filter_upwards [(Filter.tendsto_add_atTop_nat N).eventually hvol] with k hk
      rw [hvolume]
      exact hk }
  exact ⟨N, hsub, H, rfl⟩

end PoincareConjecture.M30

import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.CompactLimit












noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.AncientVolume.ScalarRatio

variable {A B ι : Type*} [MetricSpace A] [MetricSpace B]




theorem ball_subset_range_of_uniform_relation_approximation [CompactSpace A]
    (X : ι → Type*) [∀ k, MetricSpace (X k)]
    (Φ : ∀ k, A → X k) (R : ∀ k, X k → B → Prop)
    (ψ : ι → A → B) (e : A → B) (o : A) {ρ : ℝ}
    {l : Filter ι} [l.NeBot]
    (he : Continuous e) (hlim : TendstoUniformly ψ e l)
    (ε : ι → ℝ) (hε : Tendsto ε l (𝓝 0))
    (hrelated : ∀ᶠ k in l, ∀ x : A, R k (Φ k x) (ψ k x))
    (hdist : ∀ᶠ k in l, ∀ (x y : X k) (z w : B),
      R k x z → R k y w → |dist x y - dist z w| ≤ ε k)
    (hcover : ∀ᶠ k in l, ∀ y : B, ∃ x : X k, R k x y)
    (hchart : ∀ᶠ k in l, ∀ y : X k,
      dist (Φ k o) y < ρ → ∃ x : A, Φ k x = y) :
    Metric.ball (e o) ρ ⊆ range e := by
  intro y hy
  have hinside : dist (e o) y < ρ := by
    simpa only [Metric.mem_ball, dist_comm] using hy
  let margin := ρ - dist (e o) y
  have hmargin : 0 < margin := sub_pos.mpr hinside
  apply mem_range_of_uniform_limit_and_approximation he hlim
  intro η hη
  have hcenter : ∀ᶠ k in l, dist (ψ k o) (e o) < margin / 3 :=
    Metric.tendsto_nhds.mp (hlim.tendsto_at o) _ (by positivity)
  have hsmall : ∀ᶠ k in l, ε k < margin / 3 :=
    hε.eventually_lt_const (by positivity)
  have herror : ∀ᶠ k in l, ε k < η := hε.eventually_lt_const hη
  filter_upwards [hrelated, hdist, hcover, hchart, hcenter, hsmall, herror]
    with k hkrel hkdist hkcover hkchart hkcenter hksmall hkerror
  obtain ⟨q, hq⟩ := hkcover y
  have hdistCenter := hkdist (Φ k o) q (ψ k o) y (hkrel o) hq
  have hsource : dist (Φ k o) q < ρ := by
    have hupper := (le_abs_self (dist (Φ k o) q - dist (ψ k o) y)).trans hdistCenter
    have htriangle := dist_triangle (ψ k o) (e o) y
    dsimp only [margin] at hkcenter hksmall
    linarith
  obtain ⟨x, hx⟩ := hkchart q hsource
  have hxrel : R k (Φ k x) y := hx ▸ hq
  have hclose := hkdist (Φ k x) (Φ k x) (ψ k x) y (hkrel x) hxrel
  simp only [dist_self, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] at hclose
  exact ⟨x, hclose.trans_lt hkerror⟩

end Poincare.AncientVolume.ScalarRatio

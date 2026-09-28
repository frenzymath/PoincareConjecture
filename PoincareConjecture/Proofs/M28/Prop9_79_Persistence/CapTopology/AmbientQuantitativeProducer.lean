import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.ConditionalInputProducer
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.RecutDiameter

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

omit [T2Space M] in

theorem eventually_exists_quantitative_cap_recut_of_ambient_differential_bound
    (N : CapCertificate g) {delta : ℕ → ℝ}
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hdelta_pos : ∀ᶠ k in atTop, 0 < delta k)
    {L : ℝ} (hL : 0 < L)
    (hslack : L * N.cap_constant ≤ N.cap_constant + 1)
    (hbound : ∀ᶠ k in atTop,
      ∀ e : PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞,
        e.source = N.carrier →
        e.target = CapCertificate.recutTarget N delta k →
        ∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
          g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
            L * g.tangentNorm x w)
    (hball : ∀ᶠ k in atTop, ∀ y ∈ N.core,
      closure (g.ball y (N.core_radius y)) ⊆
        CapCertificate.recutTarget N delta k) :
    ∀ᶠ k in atTop,
      Nonempty (CapCertificate.QuantitativeCapRecutMargins N
        (CapCertificate.recutTarget N delta k)) := by
  have hrecuts := N.eventually_exists_smooth_precompact_recut
    hdelta hdelta_pos
  filter_upwards [hrecuts, hbound, hball] with k hrec hk hb
  obtain ⟨e, hsource, htarget, _, hins, _, _, _, _⟩ := hrec
  have htarget' : e.target = CapCertificate.recutTarget N delta k := by
    simpa only [CapCertificate.recutTarget] using htarget
  have htarget_subset : e.target ⊆ N.carrier := by
    intro x hx
    exact hins (subset_closure hx)
  have hball' : ∀ y ∈ N.core,
      closure (g.ball y (N.core_radius y)) ⊆ e.target := by
    intro y hy x hx
    exact htarget'.symm ▸ hb y hy hx
  simpa only [htarget'] using
    (N.exists_quantitative_cap_recut_margins_of_differential_bound
      e hsource htarget_subset hL hslack
      (hk e hsource htarget') hball')

omit [T2Space M] in

theorem eventually_exists_old_tensor_conditional_cap_persistence_of_ambient_differential_bound
    (N : CapCertificate g) {eta : ℝ}
    (heta : N.epsilon < eta) (heta_half : eta < 1 / 2)
    {delta : ℕ → ℝ}
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hdelta_pos : ∀ᶠ k in atTop, 0 < delta k)
    {L : ℝ} (hL : 0 < L)
    (hslack : L * N.cap_constant ≤ N.cap_constant + 1)
    (hbound : ∀ᶠ k in atTop,
      ∀ e : PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞,
        e.source = N.carrier →
        e.target = CapCertificate.recutTarget N delta k →
        ∀ x ∈ e.source, ∀ w : TangentSpace (𝓡 3) x,
          g.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x w) ≤
            L * g.tangentNorm x w)
    (hball : ∀ᶠ k in atTop, ∀ y ∈ N.core,
      closure (g.ball y (N.core_radius y)) ⊆
        CapCertificate.recutTarget N delta k) :
    ∃ I : ConditionalPersistenceInput N,
      I.candidate = (fun _ : ℕ => capEndTensor N) ∧
        I.difference_budget = 0 ∧
          ∀ᶠ k in atTop,
            ∃ Q : CapCertificate.QuantitativeCapRecutMargins N
                (CapCertificate.recutTarget N delta k),
              Nonempty (CapCertificate.QuantitativeCapRecutPacket
                N delta k Q) ∧
                Nonempty (ConditionalPersistencePacket N I delta k
                  (I.candidate k)) := by
  have hmargin := eventually_exists_quantitative_cap_recut_of_ambient_differential_bound
    N hdelta hdelta_pos hL hslack hbound hball
  exact eventually_exists_old_tensor_conditional_cap_persistence_with_recut_margins
    N heta heta_half hdelta hdelta_pos hmargin

end PoincareConjecture.M28

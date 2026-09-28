import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.RadialIdentification

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

private theorem exists_strictMono_uniform_subsequence
    {A : ℕ → Type*} {B : Type*} [MetricSpace B]
    {U : Filter ℕ} [U.NeBot] (hU : U ≤ atTop)
    (τ : ℕ → ℕ) (hτ : Tendsto τ atTop atTop)
    (F : ℕ → ∀ j, A j → B) (f : ∀ j, A j → B)
    (hlim : ∀ j, TendstoUniformly (fun k => F k j) (f j) U) :
    ∃ σ : ℕ → ℕ, StrictMono (τ ∘ σ) ∧
      ∀ j, TendstoUniformly (fun k => F (σ k) j) (f j) atTop := by
  have hfinite (m : ℕ) : ∀ᶠ k in U, ∀ j ∈ Finset.range (m + 1),
      ∀ x, dist (f j x) (F k j x) < 1 / ((m : ℝ) + 1) := by
    apply (eventually_all_finset _).mpr
    intro j hj
    exact Metric.tendstoUniformly_iff.mp (hlim j) _ (by positivity)
  obtain ⟨ν, hν, hνgood⟩ := extraction_forall_of_frequently
    (fun m => (hfinite m).frequently.filter_mono hU)
  have hνlim (j : ℕ) : TendstoUniformly (fun k => F (ν k) j) (f j) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [eventually_ge_atTop j,
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const hε] with k hj hk x
    exact (hνgood k j (Finset.mem_range.mpr (by omega)) x).trans hk
  obtain ⟨μ, hμ, hτνμ⟩ := strictMono_subseq_of_tendsto_atTop (hτ.comp hν.tendsto_atTop)
  refine ⟨ν ∘ μ, hτνμ, fun j => ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  exact hμ.tendsto_atTop.eventually (Metric.tendstoUniformly_iff.mp (hνlim j) ε hε)

theorem exists_strictMono_normalized_radius_limits_of_annulusConeRelation
    {X : Type*} [MetricSpace X] {p : X} (hc : RayComparison p)
    {A : ℕ → Type*} {U : Filter ℕ} [U.NeBot] (hU : U ≤ atTop)
    (τ : ℕ → ℕ) (hτ : Tendsto τ atTop atTop)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L (τ k))
    (Φ : ℕ → ∀ j, A j → X)
    (ψ : ℕ → ∀ j, A j → AsymptoticCone p hc)
    (e : ∀ j, A j → AsymptoticCone p hc)
    (ε : ℕ → ℝ)
    (hrel : ∀ k j x, annulusConeRelation hc (L (τ k)) (ε k) (Φ (τ k) j x) (ψ k j x))
    (hlim : ∀ j, TendstoUniformly (fun k => ψ k j) (e j) U) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ j, TendstoUniformly
        (fun k x => dist p (Φ (σ k) j x) / L (σ k))
        (fun x => (asymptoticConeRadius hc (e j x) : ℝ)) atTop := by
  have hrad (j : ℕ) : TendstoUniformly
      (fun k x => dist p (Φ (τ k) j x) / L (τ k))
      (fun x => (asymptoticConeRadius hc (e j x) : ℝ)) U := by
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    filter_upwards [Metric.tendstoUniformly_iff.mp (hlim j) η hη] with k hk x
    rw [← annulusConeRelation_radius hc (hL k) (hrel k j x)]
    have hbound := (lipschitzWith_asymptoticConeRadius hc).dist_le_mul (e j x) (ψ k j x)
    simp only [NNReal.coe_one, one_mul, NNReal.dist_eq, Real.dist_eq] at hbound ⊢
    exact hbound.trans_lt (hk x)
  obtain ⟨σ, hσ, hσlim⟩ := exists_strictMono_uniform_subsequence hU τ hτ
    (fun k j x => dist p (Φ (τ k) j x) / L (τ k))
    (fun j x => (asymptoticConeRadius hc (e j x) : ℝ)) hrad
  exact ⟨τ ∘ σ, hσ, hσlim⟩

end Poincare.AncientVolume.ScalarRatio

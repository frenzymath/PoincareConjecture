import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RayApproximation













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric



theorem exists_minimizing_rays_approximating_finite_escaping_sequences
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ConnectedSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M)
    (hcomparison : ∀ a : ℝ, 0 < a → ∀ α β : ℝ → M,
      α 0 = p → β 0 = p →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        g.edist (α s) (α t) = ENNReal.ofReal |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        g.edist (β s) (β t) = ENNReal.ofReal |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) a,
        (s / a) ^ 2 * (g.edist (α a) (β a)).toReal ^ 2 ≤
          (g.edist (α s) (β s)).toReal ^ 2)
    (m : ℕ) (x : Fin m → ℕ → M)
    (hescape : ∀ j, Tendsto (fun i => (g.edist p (x j i)).toReal) atTop atTop) :
    ∃ ray : Fin m → ℝ → M, (∀ j, ray j 0 = p) ∧
      (∀ j s, 0 ≤ s → ∀ t, 0 ≤ t →
        g.edist (ray j s) (ray j t) = ENNReal.ofReal |s - t|) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j,
        Tendsto (fun i => (g.edist (x j (σ i))
          (ray j ((g.edist p (x j (σ i))).toReal))).toReal /
            (g.edist p (x j (σ i))).toReal) atTop (𝓝 0) := by
  induction m with
  | zero =>
    refine ⟨fun j => Fin.elim0 j, ?_, ?_, id, strictMono_id, ?_⟩ <;> intro j <;> exact Fin.elim0 j
  | succ m ih =>
    obtain ⟨ray₀, hzero₀, hunit₀, σ₀, hσ₀, herr₀⟩ :=
      g.exists_minimizing_ray_approximating_escaping_sequence hc p (x 0)
        (hescape 0) hcomparison
    obtain ⟨rays, hzeros, hunits, σ₁, hσ₁, herrs⟩ :=
      ih (fun j i => x j.succ (σ₀ i))
        (fun j => (hescape j.succ).comp hσ₀.tendsto_atTop)
    refine ⟨Fin.cases ray₀ rays, ?_, ?_, σ₀ ∘ σ₁, hσ₀.comp hσ₁, ?_⟩
    · intro j
      exact Fin.cases hzero₀ hzeros j
    · intro j
      exact Fin.cases hunit₀ hunits j
    · intro j
      refine Fin.cases ?_ (fun k => herrs k) j
      exact herr₀.comp hσ₁.tendsto_atTop

end PoincareConjecture.RiemannianMetric

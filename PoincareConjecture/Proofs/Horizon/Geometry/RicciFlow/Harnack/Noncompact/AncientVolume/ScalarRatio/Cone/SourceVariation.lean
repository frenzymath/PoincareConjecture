import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.FiniteRayApproximation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.RayPerturbation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric




theorem exists_source_radial_variation_of_normalized_distance_limits
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ConnectedSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M)
    (hcomparison : ∀ a b : ℝ, 0 < a → 0 < b → ∀ α β : ℝ → M,
      α 0 = p → β 0 = p →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        g.edist (α s) (α t) = ENNReal.ofReal |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) b, ∀ t ∈ Icc (0 : ℝ) b,
        g.edist (β s) (β t) = ENNReal.ofReal |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) b,
        s ^ 2 + t ^ 2 - 2 * s * t *
          ((a ^ 2 + b ^ 2 - (g.edist (α a) (β b)).toReal ^ 2) / (2 * a * b)) ≤
            (g.edist (α s) (β t)).toReal ^ 2)
    (m : ℕ) (x : Fin (m + 1) → ℕ → M) (scale : ℕ → ℝ)
    (hscale : ∀ i, 0 < scale i) (hscalezero : Tendsto scale atTop (𝓝 0))
    (radius : Fin (m + 1) → ℝ) (hradius : ∀ j, 0 < radius j)
    (hrad : ∀ j, Tendsto (fun i => scale i * (g.edist p (x j i)).toReal)
      atTop (𝓝 (radius j)))
    (D : Fin m → ℝ)
    (hD : ∀ j, Tendsto (fun i => scale i * (g.edist (x j.succ i) (x 0 i)).toReal)
      atTop (𝓝 (D j))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ ray : ℝ → M, ray 0 = p ∧
      (∀ s, 0 ≤ s → ∀ t, 0 ≤ t →
        g.edist (ray s) (ray t) = ENNReal.ofReal |s - t|) ∧
      Tendsto (fun i => scale (σ i) * (g.edist (x 0 (σ i))
        (ray ((g.edist p (x 0 (σ i))).toReal))).toReal) atTop (𝓝 0) ∧
      ∀ j : Fin m, ∀ c : ℝ, 0 < c →
        Tendsto (fun i => (scale (σ i) * (g.edist (x j.succ (σ i))
          (ray (c * (g.edist p (x 0 (σ i))).toReal))).toReal) ^ 2)
          atTop (𝓝 (c ^ 2 * radius 0 ^ 2 + radius j.succ ^ 2 -
            c * (radius 0 ^ 2 + radius j.succ ^ 2 - D j ^ 2))) := by
  have hinv : Tendsto (fun i => (scale i)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hscalezero, Eventually.of_forall hscale⟩)
  have hescape (j : Fin (m + 1)) :
      Tendsto (fun i => (g.edist p (x j i)).toReal) atTop atTop := by
    have hh := (hrad j).pos_mul_atTop (hradius j) hinv
    apply hh.congr
    intro i
    field_simp [(hscale i).ne']
  have hcontraction : ∀ a : ℝ, 0 < a → ∀ α β : ℝ → M,
      α 0 = p → β 0 = p →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        g.edist (α s) (α t) = ENNReal.ofReal |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        g.edist (β s) (β t) = ENNReal.ofReal |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) a,
        (s / a) ^ 2 * (g.edist (α a) (β a)).toReal ^ 2 ≤
          (g.edist (α s) (β s)).toReal ^ 2 := by
    intro a ha α β hα0 hβ0 hα hβ s hs
    have hh := hcomparison a a ha ha α β hα0 hβ0 hα hβ s hs s hs
    convert hh using 1
    field_simp [ha.ne']
    ring
  obtain ⟨rays, hzeros, hunits, σ, hσ, herrs⟩ :=
    g.exists_minimizing_rays_approximating_finite_escaping_sequences hc p hcontraction
      (m + 1) x hescape
  have herr (j : Fin (m + 1)) :
      Tendsto (fun i => scale (σ i) * (g.edist (x j (σ i))
        (rays j ((g.edist p (x j (σ i))).toReal))).toReal) atTop (𝓝 0) := by
    have hh := (herrs j).mul ((hrad j).comp hσ.tendsto_atTop)
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [((hescape j).comp hσ.tendsto_atTop).eventually_gt_atTop 0] with i hi
    dsimp only [Function.comp_apply] at hi ⊢
    field_simp [hi.ne']
  refine ⟨σ, hσ, rays 0, hzeros 0, hunits 0, herr 0, ?_⟩
  let := g.toMetricSpace
  have hunitReal (j : Fin (m + 1)) : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t →
      dist (rays j s) (rays j t) = |s - t| := by
    intro s hs t ht
    change (g.edist (rays j s) (rays j t)).toReal = _
    rw [hunits j s hs t ht, ENNReal.toReal_ofReal (abs_nonneg _)]
  intro j c hc'
  apply Poincare.AncientVolume.ScalarRatio.tendsto_radial_perturbation_sq_of_ray_approximation
    (rays j.succ) (rays 0) ((hzeros j.succ).trans (hzeros 0).symm)
    (hunitReal j.succ) (hunitReal 0) _
    (fun i => scale (σ i)) (fun i => (g.edist p (x j.succ (σ i))).toReal)
    (fun i => (g.edist p (x 0 (σ i))).toReal) (fun i => hscale (σ i))
    (hscalezero.comp hσ.tendsto_atTop) (fun _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg) (fun i => x j.succ (σ i)) (fun i => x 0 (σ i))
    (hradius j.succ) (hradius 0) ((hrad j.succ).comp hσ.tendsto_atTop)
    ((hrad 0).comp hσ.tendsto_atTop) (herr j.succ) (herr 0)
    ((hD j).comp hσ.tendsto_atTop) c hc'
  intro a b ha hb s hs t ht
  exact hcomparison a b ha hb (rays j.succ) (rays 0) (hzeros j.succ) (hzeros 0)
    (fun u hu v hv => hunits j.succ u hu.1 v hv.1)
    (fun u hu v hv => hunits 0 u hu.1 v hv.1) s hs t ht

end PoincareConjecture.RiemannianMetric

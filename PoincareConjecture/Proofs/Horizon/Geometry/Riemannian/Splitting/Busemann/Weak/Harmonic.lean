import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Weak.StrongMaximum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Regularity.Smoothness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Parallel
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.CompactCutoff
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Exhaustion














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem integral_laplacian_eq_zero_of_subharmonic_of_neg_subharmonic
    (D : LeviCivitaData g) {f : M → ℝ} (hf : Continuous f)
    (hsub : ∀ ψ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, f x * D.laplacian ψ x ∂g.volumeMeasure)
    (hnegsub : ∀ ψ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, (-f x) * D.laplacian ψ x ∂g.volumeMeasure)
    (ψ : M → ℝ) (hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ)
    (hc : HasCompactSupport ψ) :
    (∫ x, f x * D.laplacian ψ x ∂g.volumeMeasure) = 0 := by
  let : SecondCountableTopology M := g.secondCountableTopology
  have hnonneg (θ : M → ℝ) (hθ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ θ)
      (hθc : HasCompactSupport θ) (hθ0 : ∀ x, 0 ≤ θ x) :
      (∫ x, f x * D.laplacian θ x ∂g.volumeMeasure) = 0 := by
    have hp := hsub θ hθ hθc hθ0
    have hn := hnegsub θ hθ hθc hθ0
    simp only [neg_mul, integral_neg] at hn
    linarith
  obtain ⟨χ, hχ, hχc, _, hχ01, hχ1, _⟩ :=
    Poincare.Manifold.exists_compact_smooth_cutoff (𝓡 n) hc isOpen_univ (subset_univ _)
  obtain ⟨C₀, hC₀⟩ := hc.exists_bound_of_continuous hψ.continuous
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (x : M) : |ψ x| ≤ C := (hC₀ x).trans (le_max_left _ _)
  let η := fun x => C * χ x
  have hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η := contMDiff_const.mul hχ
  have hηc : HasCompactSupport η := hχc.mul_left
  have hη0 : ∀ x, 0 ≤ η x := fun x => mul_nonneg hC (hχ01 x).1
  have hadd0 : ∀ x, 0 ≤ ψ x + η x := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · have hχx := hχ1.self_of_nhdsSet x hx
      dsimp [η]
      rw [hχx, mul_one]
      linarith [neg_abs_le (ψ x), hbound x]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_add]
      exact hη0 x
  have hηint := hnonneg η hη hηc hη0
  have haddint := hnonneg (fun x => ψ x + η x) (hψ.add hη) (hc.add hηc) hadd0
  have hlapc {θ : M → ℝ} (hθc : HasCompactSupport θ) : HasCompactSupport (D.laplacian θ) :=
    hθc.of_isClosed_subset (isClosed_tsupport _) (D.tsupport_laplacian_subset θ)
  have hintψ : Integrable (fun x => f x * D.laplacian ψ x) g.volumeMeasure :=
    (hf.mul (D.continuous_laplacian hψ)).integrable_of_hasCompactSupport
      (hlapc hc).mul_left
  have hintη : Integrable (fun x => f x * D.laplacian η x) g.volumeMeasure :=
    (hf.mul (D.continuous_laplacian hη)).integrable_of_hasCompactSupport
      (hlapc hηc).mul_left
  simp_rw [D.laplacian_add hψ hη, mul_add] at haddint
  rw [integral_add hintψ hintη, hηint, add_zero] at haddint
  exact haddint

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M]



theorem busemann_weak_harmonic_of_distributional_subharmonic
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : D.NonnegativeRicciCurvature) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hsub : ∀ ψ : M → ℝ, ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, g.busemann γ x * D.laplacian ψ x ∂g.volumeMeasure)
    (hsubrev : ∀ ψ : M → ℝ, ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, g.busemann (fun t => γ (-t)) x * D.laplacian ψ x ∂g.volumeMeasure)
    (ψ : M → ℝ) (hψ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ ψ)
    (hc : HasCompactSupport ψ) :
    (∫ x, g.busemann γ x * D.laplacian ψ x ∂g.volumeMeasure) = 0 := by
  apply D.integral_laplacian_eq_zero_of_subharmonic_of_neg_subharmonic
    (g.continuous_busemann hγ) hsub ?_ ψ hψ hc
  intro θ hθ hθc hθ0
  simpa only [g.busemann_reverse_eq_neg D hm hcomplete hRic hγ] using hsubrev θ hθ hθc hθ0



theorem busemann_smooth_harmonic_of_distributional_subharmonic
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : D.NonnegativeRicciCurvature) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hsub : ∀ ψ : M → ℝ, ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, g.busemann γ x * D.laplacian ψ x ∂g.volumeMeasure)
    (hsubrev : ∀ ψ : M → ℝ, ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, g.busemann (fun t => γ (-t)) x * D.laplacian ψ x ∂g.volumeMeasure) :
    ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (g.busemann γ) ∧
      ∀ x, D.laplacian (g.busemann γ) x = 0 :=
  D.smooth_harmonic_of_distance_lipschitz_of_weak_harmonic (by omega)
    (g.continuous_busemann hγ) (g.abs_busemann_sub_le hγ)
    (g.busemann_weak_harmonic_of_distributional_subharmonic D hm hcomplete hRic hγ hsub hsubrev)



theorem busemann_properties_of_distributional_subharmonic
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : D.NonnegativeRicciCurvature) {γ : ℝ → M}
    (hγ : ∀ s t : ℝ, g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|)
    (hsub : ∀ ψ : M → ℝ, ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, g.busemann γ x * D.laplacian ψ x ∂g.volumeMeasure)
    (hsubrev : ∀ ψ : M → ℝ, ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, g.busemann (fun t => γ (-t)) x * D.laplacian ψ x ∂g.volumeMeasure) :
    (∀ x, Tendsto (fun t => g.busemannApprox γ t x) atTop (𝓝 (g.busemann γ x))) ∧
    (∀ x, Tendsto (fun t => g.busemannApprox (fun s => γ (-s)) t x)
      atTop (𝓝 (g.busemann (fun s => γ (-s)) x))) ∧
    ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (g.busemann γ) ∧
    ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (g.busemann (fun t => γ (-t))) ∧
    (∀ x, g.busemann (fun t => γ (-t)) x = -g.busemann γ x) ∧
    (∀ s, g.busemann γ (γ s) = s) ∧
    (∀ x, D.laplacian (g.busemann γ) x = 0) ∧
    (∀ x, g.inner x (D.gradient (g.busemann γ) x) (D.gradient (g.busemann γ) x) = 1) ∧
    (∀ x v, D.connection (D.gradient (g.busemann γ)) x v = 0) ∧
    (∀ x v w, D.hessian (g.busemann γ) x v w = 0) := by
  obtain ⟨hs, hh⟩ := g.busemann_smooth_harmonic_of_distributional_subharmonic
    D hm hcomplete hRic hγ hsub hsubrev
  have heq : g.busemann (fun t => γ (-t)) = fun x => -g.busemann γ x :=
    funext (g.busemann_reverse_eq_neg D hm hcomplete hRic hγ)
  refine ⟨g.tendsto_busemannApprox hγ,
    g.tendsto_busemannApprox (g.minimizing_line_reverse hγ), hs, ?_,
    g.busemann_reverse_eq_neg D hm hcomplete hRic hγ, g.busemann_apply_line hγ, hh,
    g.busemann_gradient_normSq_eq_one D hcomplete hγ hs,
    g.busemann_connection_gradient_eq_zero D hcomplete hRic hγ hs hh,
    g.busemann_hessian_eq_zero D hcomplete hRic hγ hs hh⟩
  rw [heq]
  exact hs.neg

end PoincareConjecture.RiemannianMetric

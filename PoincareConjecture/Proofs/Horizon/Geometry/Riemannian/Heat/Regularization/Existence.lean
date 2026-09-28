import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.CanonicalEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.Equation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.Line











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RiemannianMetric

open LeviCivitaData




theorem exists_canonical_heat_regularization_unit_bounds_of_contMDiff
    (m : ℕ) (K : ℝ) (hm : 0 < m) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M] [PreconnectedSpace M]
        (g : RiemannianMetric (m + 1) M) (hc : MetricComplete g)
        (D : LeviCivitaData g)
        (_hsec : ∀ x v w, |D.sectionalCurvature x v w| ≤ K)
        (hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
          -(m : ℝ) * K * g.inner x v v ≤ D.ricci x v v)
        (Ω : ℕ → Set M) (S : ∀ j, Poincare.Manifold.SmoothDomain (m + 1) (Ω j))
        (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
        (O : M) (f : M → ℝ), ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ f →
        (∀ x, |f x - (g.edist O x).toReal| ≤ 1) →
        (∀ x, g.tangentNorm x (D.gradient f x) ≤ 2) →
        let H := canonicalConservativeHeatKernelData D hm hc hK hRic S hΩmono hcover
        let F : ℝ × M → ℝ := fun p => ∫ y, f y * H.kernel p.2 y p.1 ∂g.volumeMeasure
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 (m + 1))) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ) →
        (∀ t, 0 < t → ∀ x, Integrable (fun y => f y * H.kernel x y t) g.volumeMeasure) ∧
        (∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F (s, x))
          (D.laplacian (fun y => F (t, y)) x) t) ∧
        TendstoUniformly (fun t x => F (t, x)) f (𝓝[>] 0) ∧
        (∀ t ∈ Ioc 0 1, ∀ x,
          |F (t, x) - f x| ≤ C ∧
          g.tangentNorm x (D.gradient (fun y => F (t, y)) x) ≤ C) := by
  obtain ⟨C₀, hC₀, hdisp⟩ :=
    exists_canonical_kernel_integral_displacement_bound m K hm hK
  let C₁ := Real.sqrt ((2 + 6 * heatCutoffConstant) ^ 2 + 1) *
    Real.exp ((((m + 1 : ℕ) : ℝ) - 1) * K)
  refine ⟨max C₀ C₁, hC₀.trans_le (le_max_left _ _), ?_⟩
  intro M _ _ _ _ _ _ _ g hc D hsec hRic Ω S hΩmono hcover O f hf happrox hgrad
  let H := canonicalConservativeHeatKernelData D hm hc hK hRic S hΩmono hcover
  dsimp only
  intro hF
  obtain ⟨hint, hlim, hb⟩ :=
    hdisp M g hc D hRic Ω S hΩmono hcover f hf hgrad
  have hkernel : ∀ x y t, H.kernel x y t = dirichletExhaustionKernel
      (fun j => Dirichlet.heatKernelContinuousTime D (S j)) t x y := fun _ _ _ => rfl
  have hgradient := H.kernel_evolution_gradient_bound_of_exhaustion_kernel
    (by omega) hc hK hsec O S hΩmono hcover (fun t _ x y => hkernel x y t)
    hf happrox hgrad hF (fun _ _ _ => rfl)
  have hk : 0 ≤ (m : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
  have hRic' : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
      -((m : ℝ) * K) * g.inner x v v ≤ D.ricci x v v := by
    simpa only [neg_mul] using hRic
  refine ⟨hint, ?_, hlim, ?_⟩
  · intro t ht x
    exact H.hasDerivAt_kernel_integral_of_exhaustion_of_contMDiff D hc hk hRic'
      S hΩmono hcover hkernel O hf happrox hgrad hF ht x
  · intro t ht x
    exact ⟨(hb t ht x).trans (le_max_left _ _),
      (hgradient t ht x).trans (le_max_right C₀ C₁)⟩



theorem exists_canonical_heat_regularization_unit_bounds
    (m : ℕ) (K : ℝ) (hm : 0 < m) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M] [PreconnectedSpace M]
        (g : RiemannianMetric (m + 1) M) (hc : MetricComplete g)
        (D : LeviCivitaData g)
        (_hsec : ∀ x v w, |D.sectionalCurvature x v w| ≤ K)
        (hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
          -(m : ℝ) * K * g.inner x v v ≤ D.ricci x v v)
        (Ω : ℕ → Set M) (S : ∀ j, Poincare.Manifold.SmoothDomain (m + 1) (Ω j))
        (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
        (O : M) (f : M → ℝ), ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ f →
        (∀ x, |f x - (g.edist O x).toReal| ≤ 1) →
        (∀ x, g.tangentNorm x (D.gradient f x) ≤ 2) →
        let H := canonicalConservativeHeatKernelData D hm hc hK.le hRic S hΩmono hcover
        let F : ℝ × M → ℝ := fun p => ∫ y, f y * H.kernel p.2 y p.1 ∂g.volumeMeasure
        (∀ t, 0 < t → ∀ x, Integrable (fun y => f y * H.kernel x y t) g.volumeMeasure) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 (m + 1))) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ) ∧
        (∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F (s, x))
          (D.laplacian (fun y => F (t, y)) x) t) ∧
        TendstoUniformly (fun t x => F (t, x)) f (𝓝[>] 0) ∧
        (∀ t ∈ Ioc 0 1, ∀ x,
          |F (t, x) - f x| ≤ C ∧
          g.tangentNorm x (D.gradient (fun y => F (t, y)) x) ≤ C) := by
  obtain ⟨C, hC, hreg⟩ :=
    exists_canonical_heat_regularization_unit_bounds_of_contMDiff m K hm hK.le
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ g hc D hsec hRic Ω S hΩmono hcover O f hf happrox hgrad
  let H := canonicalConservativeHeatKernelData D hm hc hK.le hRic S hΩmono hcover
  have hLip : ∀ x y, |f y - f x| ≤ 2 * (g.edist x y).toReal := by
    intro x y
    rw [abs_sub_comm]
    exact g.abs_sub_le_mul_toReal_edist_of_derivative_bound
      (hf.of_le (by simp)) (K := 2) (by norm_num)
      (fun z => (D.gradient_norm_le_iff f z (by norm_num)).mp (hgrad z)) x y
  have hF := H.contMDiffOn_integral_of_exhaustion_kernel (by omega) D hc hK hsec
    S hΩmono hcover (fun _ _ _ => rfl) hf.continuous hLip
  obtain ⟨hint, hheat, hlim, hb⟩ :=
    hreg M g hc D hsec hRic Ω S hΩmono hcover O f hf happrox hgrad hF
  exact ⟨hint, hF, hheat, hlim, hb⟩



theorem exists_heat_regularization_unit_bounds
    (n : ℕ) (K : ℝ) (hn : 0 < n) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M] [NoncompactSpace M]
        (g : RiemannianMetric n M), MetricComplete g →
        ∀ (D : LeviCivitaData g),
          (∀ x v w, |D.sectionalCurvature x v w| ≤ K) →
          ∀ (O : M) (f : M → ℝ), ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f →
            (∀ x, |f x - (g.edist O x).toReal| ≤ 1) →
            (∀ x, g.tangentNorm x (D.gradient f x) ≤ 2) →
            ∃ F : ℝ × M → ℝ,
              ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F
                (Ioi 0 ×ˢ univ) ∧
              (∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F (s, x))
                (D.laplacian (fun y => F (t, y)) x) t) ∧
              TendstoUniformly (fun t x => F (t, x)) f (𝓝[>] 0) ∧
              (∀ t ∈ Ioc 0 1, ∀ x,
                |F (t, x) - f x| ≤ C ∧
                g.tangentNorm x (D.gradient (fun y => F (t, y)) x) ≤ C) := by
  cases n with
  | zero => omega
  | succ m =>
    by_cases hm : m = 0
    · subst m
      refine ⟨2 * Real.sqrt 2, by positivity, ?_⟩
      intro M _ _ _ _ _ _ _ _ g hc D _ _ f hf _ hgrad
      exact g.exists_heat_regularization_unit_bounds_dim_one D hc hf hgrad
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      obtain ⟨C, hC, hreg⟩ :=
        exists_canonical_heat_regularization_unit_bounds m K hmpos hK
      refine ⟨C, hC, ?_⟩
      intro M _ _ _ _ _ _ _ _ g hc D hsec O f hf happrox hgrad
      have hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
          -(m : ℝ) * K * g.inner x v v ≤ D.ricci x v v := by
        intro x v
        simpa [Nat.cast_add] using
          D.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le x K (hsec x) v
      obtain ⟨Ω, S, hnest, hcover, _, _⟩ := D.exists_canonical_dirichletHeatKernel_exhaustion
      have hΩmono : Monotone Ω := monotone_nat_of_le_succ fun j =>
        subset_closure.trans (hnest j)
      let H := canonicalConservativeHeatKernelData D hmpos hc hK.le hRic S hΩmono hcover
      let F : ℝ × M → ℝ := fun p => ∫ y, f y * H.kernel p.2 y p.1 ∂g.volumeMeasure
      obtain ⟨_, hF, hheat, hlim, hb⟩ :=
        hreg M g hc D hsec hRic Ω S hΩmono hcover O f hf happrox hgrad
      exact ⟨F, hF, hheat, hlim, hb⟩

end PoincareConjecture.RiemannianMetric

import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.LipschitzApproximation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Hessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.Existence









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric



theorem exists_uniform_smoothDistanceLike_of_heat_estimates
    (n : ℕ) {k A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M] [T3Space M] [PreconnectedSpace M]
        [NoncompactSpace M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g),
        MetricComplete g → (∀ x, D.curvatureTensorNorm x ≤ k) →
        ∀ (O : M) (u : M → ℝ), ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u →
        (∀ x, |u x - (g.edist O x).toReal| ≤ 1) →
        ∀ F : HeatSolution g D,
        (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x, |F.toFun x t - u x| ≤ A) →
        (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x v,
          |mvfderiv (𝓡 n) (fun y ↦ F.toFun y t) x v| ≤ A * g.tangentNorm x v) →
        ∃ h : SmoothDistanceLike g D O, h.bound = C := by
  have hK : (0 : ℝ) < max 1 k := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨H, hH, hessian⟩ :=
    LeviCivitaData.exists_uniform_time_one_hessian_bound (n := n) hK hA
  refine ⟨max (2 * (A + 1) + 1) (max A H),
    lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro M _ _ _ _ _ _ g D hc hcurv O u hu happrox F hvalue hgradient
  have hsec := fun x v w ↦ D.abs_sectionalCurvature_le_max_one x v w k (hcurv x)
  refine ⟨SmoothDistanceLike.of_additive_estimates g D O
    (F.contMDiff_slice (by norm_num : (0 : ℝ) < 1)) (by linarith : 0 ≤ A + 1)
    (g.abs_sub_distance_le_of_approximation O happrox
      (hvalue 1 (by norm_num) le_rfl))
    (hgradient 1 (by norm_num) le_rfl)
    (D.hessian_quadratic_le_of_abs_le
      (hessian g D hc F u hu hsec hvalue hgradient)), rfl⟩




theorem exists_uniform_smoothDistanceLike_of_heat_gradient_estimates
    (n : ℕ) {k A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M] [T3Space M] [PreconnectedSpace M]
        [NoncompactSpace M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g),
        MetricComplete g → (∀ x, D.curvatureTensorNorm x ≤ k) →
        ∀ (O : M) (u : M → ℝ), ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u →
        (∀ x, |u x - (g.edist O x).toReal| ≤ 1) →
        ∀ F : HeatSolution g D,
        (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x,
          |F.toFun x t - u x| ≤ A) →
        (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x,
          g.tangentNorm x (D.gradient (fun y ↦ F.toFun y t) x) ≤ A) →
        ∃ h : SmoothDistanceLike g D O, h.bound = C := by
  obtain ⟨C, hC, hassemble⟩ :=
    exists_uniform_smoothDistanceLike_of_heat_estimates n (k := k) hA
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ g D hc hcurv O u hu happrox F hvalue hgradient
  apply hassemble g D hc hcurv O u hu happrox F hvalue
  intro t ht ht1 x v
  exact (D.gradient_norm_le_iff (fun y ↦ F.toFun y t) x hA).mp
    (hgradient t ht ht1 x) v



theorem exists_uniform_smoothDistanceLike_dim_one {k : ℝ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
        [IsManifold (𝓡 1) ∞ M] [T3Space M] [PreconnectedSpace M]
        [NoncompactSpace M]
        (g : RiemannianMetric 1 M) (D : LeviCivitaData g),
        MetricComplete g → (∀ x, D.curvatureTensorNorm x ≤ k) →
        ∀ O : M, ∃ h : SmoothDistanceLike g D O, h.bound = C := by
  have hA : (0 : ℝ) ≤ 2 * Real.sqrt 2 := by positivity
  obtain ⟨C, hC, assemble⟩ :=
    exists_uniform_smoothDistanceLike_of_heat_estimates 1 (k := k) hA
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ g D hc hcurv O
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨u, hu, happrox, hgrad⟩ := g.exists_smooth_distance_approx O
  obtain ⟨F, hF, hheat, _, hbound⟩ := g.exists_heat_regularization_unit_bounds_dim_one
    D hc hu (fun x ↦ (D.gradient_norm_le_iff u x (by norm_num)).mpr (hgrad x))
  let solution : HeatSolution g D :=
    { toFun := fun x t ↦ F (t, x)
      smooth := hF.comp
        (contMDiffOn_snd.prodMk contMDiffOn_fst) (fun p hp ↦ ⟨hp.2, hp.1⟩)
      heatEquation := hheat }
  exact assemble g D hc hcurv O u hu happrox solution
    (fun t ht ht1 x ↦ (hbound t ⟨ht, ht1⟩ x).1)
    (fun t ht ht1 x ↦
      (D.gradient_norm_le_iff (fun y ↦ F (t, y)) x hA).mp
        (hbound t ⟨ht, ht1⟩ x).2)




theorem exists_uniform_smoothDistanceLike (n : ℕ) {k : ℝ} (hk : 0 ≤ k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M] [T3Space M] [PreconnectedSpace M]
        [NoncompactSpace M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g),
        MetricComplete g → (∀ x, D.curvatureTensorNorm x ≤ k) →
        ∀ O : M, ∃ h : SmoothDistanceLike g D O, h.bound = C := by
  by_cases hn0 : n = 0
  · subst n
    refine ⟨1, by norm_num, ?_⟩
    intro M _ _ _ _ _ _ g D
    have hdim := dimension_pos_of_noncompact (M := M) (n := 0)
    omega
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hK : (0 : ℝ) < max 1 k := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨A, hA, evolve⟩ := exists_heat_regularization_unit_bounds n (max 1 k) hn hK
  obtain ⟨C, hC, assemble⟩ :=
    exists_uniform_smoothDistanceLike_of_heat_gradient_estimates n (k := k) hA.le
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ g D hc hcurv O
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨u, hu, happrox, hgrad⟩ := g.exists_smooth_distance_approx O
  obtain ⟨F, hF, hheat, _, hbound⟩ := evolve M g hc D
    (fun x v w ↦ D.abs_sectionalCurvature_le_max_one x v w k (hcurv x))
    O u hu happrox
    (fun x ↦ (D.gradient_norm_le_iff u x (by norm_num)).mpr (hgrad x))
  let solution : HeatSolution g D :=
    { toFun := fun x t ↦ F (t, x)
      smooth := hF.comp
        (contMDiffOn_snd.prodMk contMDiffOn_fst) (fun p hp ↦ ⟨hp.2, hp.1⟩)
      heatEquation := hheat }
  exact assemble g D hc hcurv O u hu happrox solution
    (fun t ht ht1 x ↦ (hbound t ⟨ht, ht1⟩ x).1)
    (fun t ht ht1 x ↦ (hbound t ⟨ht, ht1⟩ x).2)

end PoincareConjecture.RiemannianMetric

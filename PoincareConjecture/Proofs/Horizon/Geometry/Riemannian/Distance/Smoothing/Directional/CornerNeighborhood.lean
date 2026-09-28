import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.ConstraintsDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.ConstraintsSubset
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.RadialNeighborhood
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Quantitative








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology
namespace PoincareConjecture.RiemannianMetric


theorem exists_distance_smoothing_on_compact_with_common_level_constraints
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -K ≤ D.sectionalCurvature x v w)
    (p : M) {ι : Type*} [Finite ι] (f h : ι → M → ℝ)
    {U : Set M} (hU : IsOpen U)
    (hf : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) U)
    (hh : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i) U)
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hpair : ∀ i x, x ∈ U →
      g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (D.gradient (h i) x) ≤ 1 ∧
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * δ)
    (hhess : ∀ i x, x ∈ U → ∀ v : TangentSpace (𝓡 n) x,
      D.hessian (f i) x v v ≤ C * g.inner x v v ∧
      D.hessian (h i) x v v ≤ C * g.inner x v v)
    {S T : Set M} (hT : IsCompact T) (hS : IsClosed S) (hST : S ⊆ T)
    {r₀ R : ℝ} (hr₀ : 0 < r₀)
    (hrad : ∀ x ∈ T, r₀ ≤ (g.edist p x).toReal ∧ (g.edist p x).toReal < R)
    (hball : ∀ x, g.edist p x ≤ ENNReal.ofReal R → x ∈ U)
    (hlevel : ∀ i x, x ∈ S → f i x = f i p)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ rho : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho ∧
      (∀ x ∈ T, |rho x - (g.edist p x).toReal| ≤ ε) ∧
      (∀ x ∈ T, g.tangentNorm x (D.gradient rho x) ≤ 1 + η) ∧
      (∀ x ∈ T, ∀ v : TangentSpace (𝓡 n) x,
        D.hessian rho x v v ≤ (4 / (3 * r₀) + K * R / 4 + η) * g.inner x v v) ∧
      ∀ i x, x ∈ S →
        |g.inner x (D.gradient rho x) (D.gradient (f i) x)| ≤
          4 * Real.sqrt δ + C * R / 2 + η ∧
        |g.inner x (D.gradient rho x) (D.gradient (h i) x)| ≤
          4 * Real.sqrt δ + C * R / 2 + η := by
  have hgn (x : M) (v : TangentSpace (𝓡 n) x) : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  let F : ι ⊕ ι → M → ℝ := Sum.elim f h
  let d := fun x => (g.edist p x).toReal
  let H := 4 / (3 * r₀) + K * R / 4
  let B := 4 * Real.sqrt δ + C * R / 2
  have hTU : T ⊆ U := by
    intro x hx
    apply hball
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top p x)]
    exact ENNReal.ofReal_le_ofReal (hrad x hx).2.le
  have hFnorm : ∀ i x, x ∈ S → g.tangentNorm x (D.gradient (F i) x) ≤ (1 : ℝ) := by
    intro i x hx
    cases i with
    | inl i => exact (hpair i x (hTU (hST hx))).1
    | inr i => exact (hpair i x (hTU (hST hx))).2.1
  have hlocal : ∀ x ∈ T, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ e : ℝ, 0 < e → ∃ rho : M → ℝ,
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho V ∧
        (∀ y ∈ V, |rho y - d y| ≤ e) ∧
        (∀ y ∈ V, g.tangentNorm y (D.gradient rho y) ≤ 1 + η / 4) ∧
        (∀ y ∈ V, ∀ v : TangentSpace (𝓡 n) y,
          D.hessian rho y v v ≤ (H + η / 4) * g.inner y v v) ∧
        ∀ i y, y ∈ V → y ∈ S →
          -(B + η / 2) ≤ mvfderiv (𝓡 n) rho y (D.gradient (F i) y) ∧
            mvfderiv (𝓡 n) rho y (D.gradient (F i) y) ≤ B + η / 2 := by
    intro x hx
    have hdx : 0 < d x := hr₀.trans_le (hrad x hx).1
    have hpx : p ≠ x := by
      intro hp
      subst x
      simp only [d, edist, Manifold.riemannianEDist_self, ENNReal.toReal_zero,
        lt_self_iff_false] at hdx
    have hH : 4 / (3 * d x) + K * d x / 4 ≤ H := by
      have hden : 4 / (3 * d x) ≤ 4 / (3 * r₀) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left (hrad x hx).1 (by norm_num))
      have hKrad := mul_le_mul_of_nonneg_left (hrad x hx).2.le hK
      dsimp only [H]
      linarith
    by_cases hxS : x ∈ S
    · obtain ⟨W, hW, hxW, hWU, hsupports⟩ :=
        g.exists_radial_support_neighborhood_of_common_level D hc hpx hU hf hh
          (hrad x hx).2 hball hδ hC hpair hhess (fun i => hlevel i x hxS)
          (show 0 < η / 4 by positivity)
      let Bx := 4 * Real.sqrt δ + C * d x / 2 + η / 4
      have hFsmooth : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (F i) W := by
        intro i
        cases i with
        | inl i => exact (hf i).mono hWU
        | inr i => exact (hh i).mono hWU
      have hsupp : ∀ y ∈ W, ∃ (V : Set M) (q : M → ℝ),
          IsOpen V ∧ y ∈ V ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q V ∧
          q y = d y ∧ (∀ z ∈ V, d z ≤ q z) ∧
          g.inner y (D.gradient q y) (D.gradient q y) = 1 ∧
          ∀ i, |g.inner y (D.gradient q y) (D.gradient (F i) y)| ≤ Bx := by
        intro y hy
        obtain ⟨_, V, q, hV, hyV, hq, hvalue, hupper, hunit, hbounds⟩ := hsupports y hy
        refine ⟨V, q, hV, hyV, hq, hvalue, hupper, hunit, ?_⟩
        intro i
        cases i with
        | inl i => exact (hbounds i).1
        | inr i => exact (hbounds i).2
      obtain ⟨V, hV, hxV, _, _, happrox⟩ :=
        g.exists_local_distance_smoothing_with_directional_bounds_of_upper_supports
          D hc hK hsec p x hpx F (fun _ => Bx) hW hxW hFsmooth hsupp
          (show 0 < η / 4 by positivity)
      refine ⟨V, hV, hxV, ?_⟩
      intro e he
      obtain ⟨rho, hrho, herr, hgrad, hess, hdir⟩ := happrox e he
      have hB : Bx + η / 4 ≤ B + η / 2 := by
        have hCrad := mul_le_mul_of_nonneg_left (hrad x hx).2.le hC
        dsimp only [Bx, B]
        linarith
      refine ⟨rho, hrho, herr, hgrad, ?_, ?_⟩
      · intro y hy v
        exact (hess y hy v).trans (mul_le_mul_of_nonneg_right
          (add_le_add hH le_rfl) (hgn y v))
      · intro i y hy _
        rw [← D.inner_gradient rho]
        exact abs_le.mp ((hdir i y hy).trans hB)
    · obtain ⟨V, hV, hxV, _, happrox⟩ :=
        g.exists_local_distance_smoothing_with_bounds D hc hK hsec p x hpx
          (show 0 < η / 4 by positivity)
      refine ⟨V ∩ Sᶜ, hV.inter hS.isOpen_compl, ⟨hxV, hxS⟩, ?_⟩
      intro e he
      obtain ⟨rho, hrho, herr, hgrad, hess⟩ := happrox e he
      refine ⟨rho, hrho.mono inter_subset_left,
        fun y hy => herr y hy.1, fun y hy => hgrad y hy.1, ?_, ?_⟩
      · intro y hy v
        exact (hess y hy.1 v).trans (mul_le_mul_of_nonneg_right
          (add_le_add hH le_rfl) (hgn y v))
      · intro i y hy hyS
        exact False.elim (hy.2 hyS)
  obtain ⟨rho, hrho, herr, hgrad, hess, hdir⟩ :=
    D.exists_contMDiff_directional_approx_on_compact_subset_of_local hT hST
      (g.continuous_toReal_edist p).continuousOn
      (show 0 ≤ 1 + η / 4 by positivity) (by norm_num : (0 : ℝ) ≤ 1)
      (fun i x => D.gradient (F i) x)
      (fun _ _ => -(B + η / 2)) (fun _ _ => B + η / 2) hFnorm hlocal
      hε (show 0 < η / 2 by positivity)
  refine ⟨rho, hrho, herr, ?_, ?_, ?_⟩
  · intro x hx
    exact (hgrad x hx).trans (by linarith)
  · intro x hx v
    apply (hess x hx v).trans
    exact mul_le_mul_of_nonneg_right (show H + η / 4 + η / 2 ≤ H + η by linarith)
      (hgn x v)
  · intro i x hx
    have hbound (j : ι ⊕ ι) :
        |g.inner x (D.gradient rho x) (D.gradient (F j) x)| ≤ B + η := by
      rw [D.inner_gradient]
      have hj := hdir j x hx
      apply abs_le.mpr
      constructor <;> linarith [hj.1, hj.2]
    exact ⟨hbound (.inl i), hbound (.inr i)⟩

end PoincareConjecture.RiemannianMetric

import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.LipschitzApproximation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

private def heatCutoffProfile : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private theorem exists_heatCutoffProfile_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z, |deriv heatCutoffProfile z| ≤ C := by
  obtain ⟨B, hB⟩ := heatCutoffProfile.hasCompactSupport.deriv.exists_bound_of_continuous
    (heatCutoffProfile.contDiff (n := 1)).continuous_deriv_one
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z
  exact (hB z).trans (le_max_right _ _)


noncomputable def heatCutoffConstant : ℝ :=
  Classical.choose exists_heatCutoffProfile_bound

theorem heatCutoffConstant_pos : 0 < heatCutoffConstant :=
  (Classical.choose_spec exists_heatCutoffProfile_bound).1

private theorem heatCutoffProfile_deriv_le (z : ℝ) :
    |deriv heatCutoffProfile z| ≤ heatCutoffConstant :=
  (Classical.choose_spec exists_heatCutoffProfile_bound).2 z

namespace LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [PreconnectedSpace M] {g : RiemannianMetric n M}



theorem exists_distance_cutoff (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M) {u : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (happrox : ∀ x, |u x - (g.edist O x).toReal| ≤ 1)
    (hgrad : ∀ x, g.tangentNorm x (D.gradient u x) ≤ 2)
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ η : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η ∧ HasCompactSupport η ∧
      (∀ x, η x ∈ Icc 0 1) ∧
      (∀ x, (g.edist O x).toReal ≤ R → η x = 1) ∧
      (tsupport η ⊆ {x | (g.edist O x).toReal ≤ 5 * R}) ∧
      (∀ x, g.tangentNorm x (D.gradient η x) ≤ heatCutoffConstant / R) := by
  let f : ℝ → ℝ := fun z ↦ heatCutoffProfile (z / (2 * R))
  let η : M → ℝ := f ∘ u
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hden : 0 < 2 * R := by positivity
  have hf : ContDiff ℝ ∞ f := heatCutoffProfile.contDiff.comp (contDiff_id.div_const _)
  have hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η := hf.contMDiff.comp hu
  have hout (x : M) (hx : 5 * R < (g.edist O x).toReal) : η x = 0 := by
    apply heatCutoffProfile.zero_of_le_dist
    change 2 ≤ dist (u x / (2 * R)) 0
    rw [Real.dist_eq, sub_zero]
    have hu0 := (abs_le.mp (happrox x)).1
    apply le_trans ?_ (le_abs_self _)
    apply (le_div_iff₀ hden).mpr
    linarith
  have hsupp : tsupport η ⊆ {x | (g.edist O x).toReal ≤ 5 * R} := by
    apply closure_minimal ?_ (isClosed_le (g.continuous_toReal_edist O) continuous_const)
    intro x hx
    by_contra h
    exact hx (show η x = 0 from hout x (lt_of_not_ge h))
  have hcompact : HasCompactSupport η := by
    apply HasCompactSupport.of_support_subset_isCompact
      (g.isCompact_closedBall_of_metricComplete hcomplete O (5 * R))
    intro x hx
    have hx' := hsupp (subset_closure hx)
    change g.edist O x ≤ ENNReal.ofReal (5 * R)
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top O x)]
    exact ENNReal.ofReal_le_ofReal hx'
  refine ⟨η, hη, hcompact, ?_, ?_, hsupp, ?_⟩
  · intro x
    exact ⟨heatCutoffProfile.nonneg, heatCutoffProfile.le_one⟩
  · intro x hx
    apply heatCutoffProfile.one_of_mem_closedBall
    change dist (u x / (2 * R)) 0 ≤ 1
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hden, div_le_one hden]
    apply abs_le.mpr
    have hd : 0 ≤ (g.edist O x).toReal := ENNReal.toReal_nonneg
    have hu := abs_le.mp (happrox x)
    constructor <;> linarith
  · intro x
    have hd : deriv f (u x) = deriv heatCutoffProfile (u x / (2 * R)) / (2 * R) := by
      have hb : HasDerivAt (fun z : ℝ => heatCutoffProfile z)
          (deriv heatCutoffProfile (u x / (2 * R))) (u x / (2 * R)) :=
        (heatCutoffProfile.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp) _ |>.hasDerivAt
      have hc : HasDerivAt (fun z : ℝ => z / (2 * R)) (1 / (2 * R)) (u x) :=
        (hasDerivAt_id (u x)).div_const (2 * R)
      have h := hb.comp (u x) hc
      simpa only [f, Function.comp_def, div_eq_mul_inv, one_mul] using h.deriv
    rw [show η = f ∘ u from rfl,
      D.gradient_comp ((hu x).mdifferentiableAt (by simp))
        (hf.differentiable (by simp) (u x))]
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change ‖deriv f (u x) • D.gradient u x‖ ≤ heatCutoffConstant / R
    rw [norm_smul, Real.norm_eq_abs, hd, abs_div, abs_of_pos hden]
    have hbound := div_le_div_of_nonneg_right
      (heatCutoffProfile_deriv_le (u x / (2 * R))) hden.le
    calc
      _ ≤ (heatCutoffConstant / (2 * R)) * 2 :=
        mul_le_mul hbound (hgrad x) (Real.sqrt_nonneg _)
          (div_nonneg (heatCutoffConstant_pos.le) hden.le)
      _ = _ := by field_simp



theorem exists_intrinsic_ball_cutoff (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M) {R : ℝ} (hR : 1 ≤ R) :
    ∃ η : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η ∧ HasCompactSupport η ∧
      (∀ x, η x ∈ Icc 0 1) ∧
      (∀ x, (g.edist O x).toReal ≤ R → η x = 1) ∧
      (tsupport η ⊆ {x | (g.edist O x).toReal ≤ 5 * R}) ∧
      (∀ x, g.inner x (D.gradient η x) (D.gradient η x) ≤
        (heatCutoffConstant / R) ^ 2) := by
  obtain ⟨u, hu, he, hd⟩ := g.exists_smooth_distance_approx O
  have hg (x : M) : g.tangentNorm x (D.gradient u x) ≤ 2 :=
    (D.gradient_norm_le_iff u x (by norm_num)).mpr (hd x)
  obtain ⟨η, hη, hc, hr, hone, hs, hgη⟩ := D.exists_distance_cutoff
    hcomplete O hu he hg hR
  refine ⟨η, hη, hc, hr, hone, hs, fun x ↦ ?_⟩
  have hnonneg : 0 ≤ g.inner x (D.gradient η x) (D.gradient η x) := by
    by_cases hv : D.gradient η x = 0
    · simp [hv]
    · exact (g.pos x _ hv).le
  have h := (sq_le_sq₀ (Real.sqrt_nonneg
    (g.inner x (D.gradient η x) (D.gradient η x)))
    (le_trans (Real.sqrt_nonneg _) (hgη x))).mpr (hgη x)
  simpa only [RiemannianMetric.tangentNorm, Real.sq_sqrt hnonneg] using h

end LeviCivitaData

end PoincareConjecture

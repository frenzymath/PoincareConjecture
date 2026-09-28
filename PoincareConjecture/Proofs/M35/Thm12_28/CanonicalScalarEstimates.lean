import PoincareConjecture.Proofs.M35.Thm12_28.CapScalarEstimates
import PoincareConjecture.Proofs.M35.Thm12_28.EvolvingNeckScalar
import PoincareConjecture.Proofs.M35.RawFlow.BlowupTimes

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35

theorem canonical_scalar_analytic_controls (P : M35StandardCapPredecessors) :
    ∃ delta A : ℝ, 0 < delta ∧ 0 < A ∧
      ∀ (g₀ : StandardInitialMetric) (F : MaximalStandardCapFlow g₀),
        ∃ H : ℝ, 0 < H ∧ ∀ (atlas : StandardCylinderAtlas) (epsilon C : ℝ),
          epsilon ≤ delta → ∀ t ∈ Ico 0 F.base.lifetime, ∀ x : StandardCapSpace,
            H ≤ (F.connection t).scalarCurvature x →
            StandardCanonicalAlternative atlas F t x epsilon C →
            (∀ v : TangentSpace (𝓡 3) x, (F.metric t).inner x v v = 1 →
              |mvfderiv (𝓡 3) (F.connection t).scalarCurvature x v| ≤
                max A C * (F.connection t).scalarCurvature x ^ (3 / 2 : ℝ)) ∧
            |(F.connection t).laplacian (F.connection t).scalarCurvature x +
                2 * (F.connection t).ricciNormSq x| ≤
              max A C * ((F.connection t).scalarCurvature x) ^ 2 := by
  obtain ⟨delta, A, hdelta, hA, hneck⟩ := exists_evolving_neck_scalar_bounds P
  refine ⟨delta, A, hdelta, hA, ?_⟩
  intro g₀ F
  obtain ⟨H, hH, hduration⟩ := F.base.exists_unit_backward_duration_threshold
  refine ⟨H, hH, ?_⟩
  intro atlas epsilon C hedelta t ht x hR hcanonical
  have hpos : 0 < (F.connection t).scalarCurvature x := hH.trans_le hR
  have hpow : 0 ≤ (F.connection t).scalarCurvature x ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hpos.le _
  have hneck_bound {I : Set ℝ} (N : StandardEvolvingNeck atlas F t epsilon x I)
      (hI : Icc (-1 : ℝ) 0 ⊆ I) :=
    hneck epsilon hedelta atlas g₀ F t x I N hI
  have hraise (h :
      (∀ v : TangentSpace (𝓡 3) x, (F.metric t).inner x v v = 1 →
        |mvfderiv (𝓡 3) (F.connection t).scalarCurvature x v| ≤
          A * (F.connection t).scalarCurvature x ^ (3 / 2 : ℝ)) ∧
      |(F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x| ≤
        A * ((F.connection t).scalarCurvature x) ^ 2) :
      (∀ v : TangentSpace (𝓡 3) x, (F.metric t).inner x v v = 1 →
        |mvfderiv (𝓡 3) (F.connection t).scalarCurvature x v| ≤
          max A C * (F.connection t).scalarCurvature x ^ (3 / 2 : ℝ)) ∧
      |(F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x| ≤
        max A C * ((F.connection t).scalarCurvature x) ^ 2 :=
    ⟨fun v hv => (h.1 v hv).trans (mul_le_mul_of_nonneg_right (le_max_left A C) hpow),
      h.2.trans (mul_le_mul_of_nonneg_right (le_max_left A C) (sq_nonneg _))⟩
  cases hcanonical with
  | cap N =>
    have h := N.scalar_analytic_bounds
    exact ⟨fun v hv => (h.1 v hv).le.trans
      (mul_le_mul_of_nonneg_right (le_max_right A C) hpow),
      h.2.le.trans (mul_le_mul_of_nonneg_right (le_max_right A C) (sq_nonneg _))⟩
  | initial_neck N _ =>
    apply hraise (hneck_bound N ?_)
    have hd := hduration t ht x hR
    change 1 ≤ t * (F.connection t).scalarCurvature x at hd
    intro u hu
    exact ⟨by nlinarith [hu.1], hu.2⟩
  | evolving_neck N =>
    apply hraise (hneck_bound N ?_)
    intro u hu
    exact ⟨by linarith [N.epsilon_pos, hu.1], hu.2⟩

theorem exists_guarded_scalar_bound_of_canonical (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (F : MaximalStandardCapFlow g₀)
    (atlas : StandardCylinderAtlas)
    (hcanonical : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico 0 F.base.lifetime, ∀ x : StandardCapSpace,
        StandardCanonicalAlternative atlas F t x epsilon C) :
    ∃ A H : ℝ, 0 < A ∧ 0 < H ∧ ∀ t ∈ Ico 0 F.base.lifetime,
      ∀ x : StandardCapSpace, H ≤ (F.connection t).scalarCurvature x →
        (F.connection t).laplacian (F.connection t).scalarCurvature x +
            2 * (F.connection t).ricciNormSq x ≤
          A * ((F.connection t).scalarCurvature x) ^ 2 := by
  obtain ⟨delta, A, hdelta, hA, hflows⟩ := canonical_scalar_analytic_controls P
  obtain ⟨H, hH, hbound⟩ := hflows g₀ F
  let epsilon := min delta (1 / 4)
  have he : 0 < epsilon := lt_min hdelta (by norm_num)
  have hehalf : epsilon < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨C, _hC, hc⟩ := hcanonical epsilon he hehalf
  refine ⟨max A C, H, hA.trans_le (le_max_left _ _), hH, ?_⟩
  intro t ht x hR
  exact (le_abs_self _).trans
    (hbound atlas epsilon C (min_le_left _ _) t ht x hR (hc t ht x)).2

theorem exists_guarded_scalar_gradient_of_canonical (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (F : MaximalStandardCapFlow g₀)
    (atlas : StandardCylinderAtlas)
    (hcanonical : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico 0 F.base.lifetime, ∀ x : StandardCapSpace,
        StandardCanonicalAlternative atlas F t x epsilon C) :
    ∃ A H : ℝ, 0 < A ∧ 0 < H ∧ ∀ t ∈ Ico 0 F.base.lifetime,
      ∀ x : StandardCapSpace, H ≤ (F.connection t).scalarCurvature x →
        ∀ v : TangentSpace (𝓡 3) x, (F.metric t).inner x v v = 1 →
          |mvfderiv (𝓡 3) (F.connection t).scalarCurvature x v| ≤
            A * (F.connection t).scalarCurvature x ^ (3 / 2 : ℝ) := by
  obtain ⟨delta, A, hdelta, hA, hflows⟩ := canonical_scalar_analytic_controls P
  obtain ⟨H, hH, hbound⟩ := hflows g₀ F
  let epsilon := min delta (1 / 4)
  have he : 0 < epsilon := lt_min hdelta (by norm_num)
  have hehalf : epsilon < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨C, _, hc⟩ := hcanonical epsilon he hehalf
  exact ⟨max A C, H, hA.trans_le (le_max_left _ _), hH,
    fun t ht x hR => (hbound atlas epsilon C (min_le_left _ _) t ht x hR (hc t ht x)).1⟩

end PoincareConjecture.M35

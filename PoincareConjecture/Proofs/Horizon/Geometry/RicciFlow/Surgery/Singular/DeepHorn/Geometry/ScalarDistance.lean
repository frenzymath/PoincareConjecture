import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.TerminalEstimates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

universe u

namespace PoincareConjecture.DeepHorn

private theorem transition_deriv_zero {s : ℝ} (hs : s ∉ Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition s = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at hs
  rcases hs with hs | hs
  · have h : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [gt_mem_nhds hs] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    simpa using h.deriv_eq
  · have h : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [lt_mem_nhds hs] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    simpa using h.deriv_eq

private theorem transition_deriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, |deriv Real.smoothTransition s| ≤ C := by
  have hs : tsupport (deriv Real.smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
    apply closure_minimal ?_ isClosed_Icc
    intro s hs
    by_contra h
    exact hs (transition_deriv_zero h)
  have hc : HasCompactSupport (deriv Real.smoothTransition) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hs
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).continuous_deriv_one
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hcont
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro s
  simpa only [Real.norm_eq_abs] using (hC s).trans (le_max_left C 1)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem derivative_bound_of_unit {f : M → ℝ} (x : M) {C : ℝ}
    (_hC : 0 ≤ C)
    (hunit : ∀ v : TangentSpace (𝓡 n) x, g.inner x v v = 1 →
      |mvfderiv (𝓡 n) f x v| ≤ C) (v : TangentSpace (𝓡 n) x) :
    |mvfderiv (𝓡 n) f x v| ≤ C * g.tangentNorm x v := by
  by_cases hv : v = 0
  · subst v
    simp [RiemannianMetric.tangentNorm]
  have hp : 0 < g.tangentNorm x v := Real.sqrt_pos.mpr (g.pos x v hv)
  have hsq : g.tangentNorm x v ^ 2 = g.inner x v v :=
    Real.sq_sqrt (g.pos x v hv).le
  have hu : g.inner x ((g.tangentNorm x v)⁻¹ • v)
      ((g.tangentNorm x v)⁻¹ • v) = 1 := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← hsq]
    field_simp
  have hh := hunit ((g.tangentNorm x v)⁻¹ • v) hu
  simp only [map_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hp)] at hh
  have hm := mul_le_mul_of_nonneg_left hh hp.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul, mul_comm] using hm

omit [IsManifold (𝓡 n) ∞ M] in
private theorem scalar_comp_derivative {f : M → ℝ} {F : ℝ → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hF : DifferentiableAt ℝ F (f x)) (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (F ∘ f) x v = deriv F (f x) * mvfderiv (𝓡 n) f x v := by
  rw [mvfderiv_comp x hF.mdifferentiableAt hf]
  simp only [ContinuousLinearMap.comp_apply, mvfderiv, mfderiv_eq_fderiv]
  rw [hF.hasDerivAt.hasFDerivAt.fderiv]
  change mvfderiv (𝓡 n) f x v * deriv F (f x) = _
  exact mul_comm _ _

theorem exists_scalar_level_distance {K B : ℝ} (hK : 0 < K) (hB : 0 < B) :
    ∃ d : ℝ, 0 < d ∧
      ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        {g : RiemannianMetric n M} (D : LeviCivitaData g),
        (∀ x, K ≤ D.scalarCurvature x →
          ∀ v : TangentSpace (𝓡 n) x, g.inner x v v = 1 →
            |mvfderiv (𝓡 n) D.scalarCurvature x v| ≤
              B * D.scalarCurvature x ^ (3 / 2 : ℝ)) →
        ∀ x y : M, 2 * K ≤ D.scalarCurvature x →
          D.scalarCurvature y ≤ K → ENNReal.ofReal d ≤ g.edist x y := by
  obtain ⟨C, hC, hCbound⟩ := transition_deriv_bound
  let L : ℝ := C / K * (B * (2 * K) ^ (3 / 2 : ℝ))
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L⁻¹, inv_pos.mpr hL, ?_⟩
  intro n M _ _ _ g D hgrad
  let phi : ℝ → ℝ := fun s => Real.smoothTransition (s / K - 1)
  have hphi : ContDiff ℝ ∞ phi :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.div_const K).sub contDiff_const)
  have hphi_deriv (s : ℝ) : deriv phi s =
      deriv Real.smoothTransition (s / K - 1) / K := by
    have hh := ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable (by simp)
      (s / K - 1)).hasDerivAt.comp s
      (((hasDerivAt_id s).div_const K).sub_const 1)
    simpa only [phi, Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using hh.deriv
  let psi := phi ∘ D.scalarCurvature
  have hscalar : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature :=
    D.contMDiff_scalarCurvature
  have hpsi : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 psi :=
    (hphi.contMDiff.comp hscalar).of_le (by simp)
  have hbound (x : M) (v : TangentSpace (𝓡 n) x) :
      |mvfderiv (𝓡 n) psi x v| ≤ L * g.tangentNorm x v := by
    have hn : 0 ≤ g.tangentNorm x v := Real.sqrt_nonneg _
    rw [scalar_comp_derivative (hscalar.mdifferentiable (by simp) x)
      (hphi.differentiable (by simp) _), hphi_deriv]
    by_cases hx : D.scalarCurvature x / K - 1 ∈ Icc (0 : ℝ) 1
    · have hxlo : K ≤ D.scalarCurvature x := by
        have := (le_div_iff₀ hK).mp (show 1 ≤ D.scalarCurvature x / K by linarith [hx.1])
        simpa using this
      have hxhi : D.scalarCurvature x ≤ 2 * K := by
        exact (div_le_iff₀ hK).mp (by linarith [hx.2])
      have hR : 0 ≤ D.scalarCurvature x := hK.le.trans hxlo
      have hunit := derivative_bound_of_unit x
        (mul_nonneg hB.le (Real.rpow_nonneg hR _)) (hgrad x hxlo) v
      rw [abs_mul, abs_div, abs_of_pos hK]
      calc
        _ ≤ (C / K) * (B * D.scalarCurvature x ^ (3 / 2 : ℝ) * g.tangentNorm x v) :=
          mul_le_mul (div_le_div_of_nonneg_right (hCbound _) hK.le) hunit
            (abs_nonneg _) (by positivity)
        _ ≤ L * g.tangentNorm x v := by
          dsimp [L]
          have hr := Real.rpow_le_rpow hR hxhi (by norm_num : (0 : ℝ) ≤ 3 / 2)
          nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hB.le)
            (show 0 ≤ C / K * g.tangentNorm x v by positivity)]
    · rw [transition_deriv_zero hx]
      simp only [zero_div, zero_mul, abs_zero]
      positivity
  intro x y hx hy
  have hpx : psi x = 1 := Real.smoothTransition.one_of_one_le
    (by exact
      (show 1 ≤ D.scalarCurvature x / K - 1 from by
        have := (le_div_iff₀ hK).mpr hx
        linarith))
  have hpy : psi y = 0 := Real.smoothTransition.zero_of_nonpos
    (by exact sub_nonpos.mpr ((div_le_one hK).mpr hy))
  let Ln : ℝ≥0 := ⟨L, hL.le⟩
  have hd := g.edist_le_mul_edist_of_derivative_bound hpsi
    (K := Ln) hL hbound x y
  rw [hpx, hpy] at hd
  have hLn : (Ln : ℝ≥0∞) = ENNReal.ofReal L :=
    ENNReal.ofReal_coe_nnreal.symm
  rw [hLn] at hd
  have he : (1 : ℝ≥0∞) ≤ ENNReal.ofReal L * g.edist x y := by
    simpa only [edist_dist, Real.dist_eq, sub_zero, abs_one, ENNReal.ofReal_one,
      NNReal.coe_mk] using hd
  calc
    ENNReal.ofReal L⁻¹ = (ENNReal.ofReal L)⁻¹ * 1 := by
      rw [ENNReal.ofReal_inv_of_pos hL, mul_one]
    _ ≤ (ENNReal.ofReal L)⁻¹ * (ENNReal.ofReal L * g.edist x y) :=
      mul_le_mul_right he _
    _ = g.edist x y := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top, one_mul]

end PoincareConjecture.DeepHorn

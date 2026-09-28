import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.GaugeCoefficientRegularity
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem gauge_coefficients_uniform_bounds (F : RicciFlow n M (Icc a b)) (p : M)
    {K : Set (E × E)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsub : K ⊆ (chartAt E p).target ×ˢ {V : E | V ≠ 0}) :
    let A : ℝ → E × E → ℝ := fun t z =>
      ((F.metric t).pullbackCoefficients (chartAt E p).symm z.1 z.2 z.2)⁻¹
    let R : ℝ → E × E → E := fun t z => A t z • coordinateChristoffel
      ((F.metric t).pullbackCoefficients (chartAt E p).symm) z.1 z.2 z.2
    ∃ mu Lambda : ℝ, 0 < mu ∧ 0 < Lambda ∧ ∃ L_A L_R : NNReal,
      (∀ t ∈ Icc a b, ∀ z ∈ K, mu ≤ A t z ∧ A t z ≤ Lambda) ∧
      (∀ t ∈ Icc a b, LipschitzOnWith L_A (A t) K) ∧
      (∀ t ∈ Icc a b, LipschitzOnWith L_R (R t) K) := by
  let A : ℝ → E × E → ℝ := fun t z =>
    ((F.metric t).pullbackCoefficients (chartAt E p).symm z.1 z.2 z.2)⁻¹
  let R : ℝ → E × E → E := fun t z => A t z • coordinateChristoffel
    ((F.metric t).pullbackCoefficients (chartAt E p).symm) z.1 z.2 z.2
  change ∃ mu Lambda : ℝ, 0 < mu ∧ 0 < Lambda ∧ ∃ L_A L_R : NNReal,
    (∀ t ∈ Icc a b, ∀ z ∈ K, mu ≤ A t z ∧ A t z ≤ Lambda) ∧
    (∀ t ∈ Icc a b, LipschitzOnWith L_A (A t) K) ∧
    (∀ t ∈ Icc a b, LipschitzOnWith L_R (R t) K)
  have hparam : ContDiff ℝ ∞
      (fun z : ℝ × (E × E) => ((z.1, z.2.1), z.2.2)) := by fun_prop
  have hAraw := (gauge_principal_contDiffOn F p).comp hparam.contDiffOn
    (s := Icc a b ×ˢ K) (fun _ hz => ⟨⟨hz.1, (hsub hz.2).1⟩, (hsub hz.2).2⟩)
  have hA : ContDiffOn ℝ ∞ (fun z : ℝ × (E × E) => A z.1 z.2) (Icc a b ×ˢ K) := hAraw
  have hGraw := (gauge_christoffel_contDiffOn F p).comp hparam.contDiffOn
    (s := Icc a b ×ˢ K) (fun _ hz => ⟨⟨hz.1, (hsub hz.2).1⟩, mem_univ _⟩)
  have hR : ContDiffOn ℝ ∞ (fun z : ℝ × (E × E) => R z.1 z.2) (Icc a b ×ˢ K) :=
    hA.smul hGraw
  have hcompact : IsCompact (Icc a b ×ˢ K) := isCompact_Icc.prod hK
  have hconvex : Convex ℝ (Icc a b ×ˢ K) := (convex_Icc a b).prod hconv
  obtain ⟨L_A, hLA⟩ := hA.exists_lipschitzOnWith (by simp) hconvex hcompact
  obtain ⟨L_R, hLR⟩ := hR.exists_lipschitzOnWith (by simp) hconvex hcompact
  have hpos (z : ℝ × (E × E)) (hz : z ∈ Icc a b ×ˢ K) : 0 < A z.1 z.2 :=
    inv_pos.mpr (chart_metric_pairing_pos F p z.1 (hsub hz.2).1 (hsub hz.2).2)
  have hbounds : ∃ mu Lambda : ℝ, 0 < mu ∧ 0 < Lambda ∧
      ∀ z ∈ Icc a b ×ˢ K, mu ≤ A z.1 z.2 ∧ A z.1 z.2 ≤ Lambda := by
    by_cases hne : (Icc a b ×ˢ K).Nonempty
    · obtain ⟨zmin, hzmin, hmin⟩ := hcompact.exists_isMinOn hne hA.continuousOn
      obtain ⟨zmax, hzmax, hmax⟩ := hcompact.exists_isMaxOn hne hA.continuousOn
      exact ⟨A zmin.1 zmin.2, A zmax.1 zmax.2, hpos zmin hzmin,
        hpos zmax hzmax, fun _ hz => ⟨hmin hz, hmax hz⟩⟩
    · exact ⟨1, 1, zero_lt_one, zero_lt_one, fun z hz => (hne ⟨z, hz⟩).elim⟩
  obtain ⟨mu, Lambda, hmu, hLambda, hbounds⟩ := hbounds
  have hdist (t : ℝ) (z w : E × E) : dist (t, z) (t, w) = dist z w := by
    change max (dist t t) (dist z w) = dist z w
    simp only [dist_self, max_eq_right dist_nonneg]
  refine ⟨mu, Lambda, hmu, hLambda, L_A, L_R,
    (fun t ht z hz => hbounds (t, z) ⟨ht, hz⟩), ?_, ?_⟩
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [hdist] using
      hLA.dist_le_mul (t, z) ⟨ht, hz⟩ (t, w) ⟨ht, hw⟩
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [hdist] using
      hLR.dist_le_mul (t, z) ⟨ht, hz⟩ (t, w) ⟨ht, hw⟩

theorem gauge_rhs_difference_bound (F : RicciFlow n M (Icc a b)) (p : M)
    {K : Set (E × E)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsub : K ⊆ (chartAt E p).target ×ˢ {V : E | V ≠ 0}) :
    let A : ℝ → E × E → ℝ := fun t z =>
      ((F.metric t).pullbackCoefficients (chartAt E p).symm z.1 z.2 z.2)⁻¹
    let G : ℝ → E × E → E := fun t z => coordinateChristoffel
      ((F.metric t).pullbackCoefficients (chartAt E p).symm) z.1 z.2 z.2
    ∃ Lambda : ℝ, 0 < Lambda ∧ ∃ L_A L_R : NNReal,
      ∀ t ∈ Icc a b, ∀ z ∈ K, ∀ w ∈ K, ∀ W W' : E,
        ‖A t z • (W + G t z) - A t w • (W' + G t w)‖ ≤
          Lambda * ‖W - W'‖ + ((L_A : ℝ) * ‖W'‖ + L_R) * ‖z - w‖ := by
  let A : ℝ → E × E → ℝ := fun t z =>
    ((F.metric t).pullbackCoefficients (chartAt E p).symm z.1 z.2 z.2)⁻¹
  let G : ℝ → E × E → E := fun t z => coordinateChristoffel
    ((F.metric t).pullbackCoefficients (chartAt E p).symm) z.1 z.2 z.2
  let R : ℝ → E × E → E := fun t z => A t z • G t z
  change ∃ Lambda : ℝ, 0 < Lambda ∧ ∃ L_A L_R : NNReal,
    ∀ t ∈ Icc a b, ∀ z ∈ K, ∀ w ∈ K, ∀ W W' : E,
      ‖A t z • (W + G t z) - A t w • (W' + G t w)‖ ≤
        Lambda * ‖W - W'‖ + ((L_A : ℝ) * ‖W'‖ + L_R) * ‖z - w‖
  obtain ⟨mu, Lambda, hmu, hLambda, L_A, L_R, hbounds, hLA, hLR⟩ :=
    gauge_coefficients_uniform_bounds F p hK hconv hsub
  refine ⟨Lambda, hLambda, L_A, L_R, ?_⟩
  intro t ht z hz w hw W W'
  have hAz : ‖A t z‖ ≤ Lambda := by
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hmu (hbounds t ht z hz).1)]
    exact (hbounds t ht z hz).2
  have hAdiff : ‖A t z - A t w‖ ≤ (L_A : ℝ) * ‖z - w‖ := by
    simpa only [dist_eq_norm] using (hLA t ht).dist_le_mul z hz w hw
  have hRdiff : ‖R t z - R t w‖ ≤ (L_R : ℝ) * ‖z - w‖ := by
    simpa only [dist_eq_norm] using (hLR t ht).dist_le_mul z hz w hw
  have heq : A t z • (W + G t z) - A t w • (W' + G t w) =
      A t z • (W - W') + (A t z - A t w) • W' + (R t z - R t w) := by
    dsimp only [R]
    simp only [smul_add, smul_sub, sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖A t z • (W - W')‖ + ‖(A t z - A t w) • W'‖ + ‖R t z - R t w‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖A t z‖ * ‖W - W'‖ + ‖A t z - A t w‖ * ‖W'‖ + ‖R t z - R t w‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ Lambda * ‖W - W'‖ + ((L_A : ℝ) * ‖z - w‖) * ‖W'‖ +
        (L_R : ℝ) * ‖z - w‖ :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hAz (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hAdiff (norm_nonneg _))) hRdiff
    _ = _ := by ring

end PoincareConjecture.M63

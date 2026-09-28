import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.Cutoff











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [IsManifold (𝓡 n) ∞ M] in

theorem contMDiffOn_gaussian_weight {ρ : M → ℝ}
    (hρ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ) (T : ℝ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ -(ρ p.2 ^ 2) / (16 * (2 * T - p.1)))
      (Iio (2 * T) ×ˢ univ) := by
  intro p hp
  have hden : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M ↦ 16 * (2 * T - q.1)) p :=
    contMDiffAt_const.mul (contMDiffAt_const.sub contMDiffAt_fst)
  have hn : 16 * (2 * T - p.1) ≠ 0 := by
    have hp' : p.1 < 2 * T := hp.1
    linarith
  exact (((((hρ.comp contMDiff_snd) p).pow 2).neg).div₀ hden hn).contMDiffWithinAt

omit [IsManifold (𝓡 n) ∞ M] in

theorem continuousOn_gaussian_weight {ρ : M → ℝ}
    (hρ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ) {T b : ℝ}
    (hT : 0 < T) (hb : b ≤ T) :
    ContinuousOn (fun p : ℝ × M ↦ -(ρ p.2 ^ 2) / (16 * (2 * T - p.1)))
      (Icc 0 b ×ˢ univ) := by
  apply (contMDiffOn_gaussian_weight hρ T).continuousOn.mono
  intro p hp
  refine ⟨?_, mem_univ _⟩
  change p.1 < 2 * T
  have := hp.1.2
  linarith


theorem exists_smooth_distance_majorant [T3Space M] [PreconnectedSpace M]
    (D : LeviCivitaData g) (O : M) :
    ∃ ρ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ ∧
      (∀ x, (g.edist O x).toReal ≤ ρ x) ∧
      (∀ x, g.inner x (D.gradient ρ x) (D.gradient ρ x) ≤ 4) := by
  obtain ⟨u, hu, herr, hgrad⟩ := g.exists_smooth_distance_approx O
  refine ⟨fun x ↦ u x + 1, hu.add contMDiff_const, ?_, ?_⟩
  · intro x
    have := (abs_le.mp (herr x)).1
    linarith
  · intro x
    have hg : D.gradient (fun y ↦ u y + 1) x = D.gradient u x := by
      apply (g.inner_isInvertible x).injective
      ext v
      simp only [D.inner_gradient]
      rw [mvfderiv_fun_add ((hu x).mdifferentiableAt (by simp)) mdifferentiableAt_const]
      simp [mvfderiv]
    rw [hg]
    have hnorm := (D.gradient_norm_le_iff u x (by norm_num : (0 : ℝ) ≤ 2)).mpr
      (hgrad x)
    have hnonneg : 0 ≤ g.inner x (D.gradient u x) (D.gradient u x) := by
      by_cases h : D.gradient u x = 0
      · simp [h]
      · exact (g.pos x _ h).le
    have hsq := Real.sq_sqrt hnonneg
    change Real.sqrt _ ≤ 2 at hnorm
    nlinarith [Real.sqrt_nonneg (g.inner x (D.gradient u x) (D.gradient u x))]



theorem gaussian_weight_differential_inequality (D : LeviCivitaData g)
    {ρ : M → ℝ} (hρ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ)
    (hgrad : ∀ x, g.inner x (D.gradient ρ x) (D.gradient ρ x) ≤ 4)
    {T t : ℝ} (ht : t < 2 * T) (x : M) :
    deriv (fun s ↦ -(ρ x ^ 2) / (16 * (2 * T - s))) t +
      g.inner x (D.gradient (fun y ↦ -(ρ y ^ 2) / (16 * (2 * T - t))) x)
        (D.gradient (fun y ↦ -(ρ y ^ 2) / (16 * (2 * T - t))) x) ≤ 0 := by
  have hd0 : 0 < 16 * (2 * T - t) := by linarith
  have hd : HasDerivAt (fun s ↦ -(ρ x ^ 2) / (16 * (2 * T - s)))
      (-(16 * ρ x ^ 2) / (16 * (2 * T - t)) ^ 2) t := by
    convert! (hasDerivAt_const t (-(ρ x ^ 2))).div
      (((hasDerivAt_const t (2 * T)).sub (hasDerivAt_id t)).const_mul 16) hd0.ne' using 1
    simp [Pi.sub_apply, id_eq]
    ring
  have hg : D.gradient (fun y ↦ -(ρ y ^ 2) / (16 * (2 * T - t))) x =
      (-(2 * ρ x) / (16 * (2 * T - t))) • D.gradient ρ x := by
    have hpoly : HasDerivAt (fun z : ℝ ↦ -(z ^ 2) / (16 * (2 * T - t)))
        (-(2 * ρ x) / (16 * (2 * T - t))) (ρ x) := by
      simpa only [Pi.neg_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
        show (2 : ℕ) - 1 = 1 by rfl, pow_one, mul_one] using
        (((hasDerivAt_id (ρ x)).pow 2).neg.div_const (16 * (2 * T - t)))
    simpa only [Function.comp_def, hpoly.deriv] using
      D.gradient_comp ((hρ x).mdifferentiableAt (by simp)) hpoly.differentiableAt
  rw [hd.deriv, hg]
  simp only [map_smul, smul_apply, smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (hgrad x) (sq_nonneg (ρ x))
  have hid : -(16 * ρ x ^ 2) / (16 * (2 * T - t)) ^ 2 +
      (-(2 * ρ x) / (16 * (2 * T - t))) *
        ((-(2 * ρ x) / (16 * (2 * T - t))) *
          g.inner x (D.gradient ρ x) (D.gradient ρ x)) =
      (4 * (ρ x ^ 2 * g.inner x (D.gradient ρ x) (D.gradient ρ x) -
        4 * ρ x ^ 2)) / (16 * (2 * T - t)) ^ 2 := by
    field_simp [hd0.ne']
    ring
  rw [hid]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (sq_nonneg _)



theorem exp_gaussian_weight_le {ρ r T t a : ℝ}
    (hr : 0 ≤ r) (hρ : r ≤ ρ) (hT : 0 < T) (ha : 0 < a)
    (hTsmall : T ≤ 1 / (32 * a)) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Real.exp (-(ρ ^ 2) / (16 * (2 * T - t))) ≤ Real.exp (-a * r ^ 2) := by
  apply Real.exp_le_exp.mpr
  have hd0 : 0 < 16 * (2 * T - t) := by linarith
  have hsmall : T * (32 * a) ≤ 1 := (le_div_iff₀ (by positivity)).mp hTsmall
  have hcoeff : a * (16 * (2 * T - t)) ≤ 1 := by nlinarith
  apply (div_le_iff₀ hd0).mpr
  have hsq : r ^ 2 ≤ ρ ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg r)
  nlinarith

end PoincareConjecture.LeviCivitaData

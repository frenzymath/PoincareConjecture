import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Plane.TailCorrection.TriangularFamily
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Plane.TailCorrection.SlowCutoff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Manifold

namespace Poincare.Manifold.PlaneDiffeomorph

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

private theorem exists_uniform_strip_bound
    {f : ℝ × ℝ → ℝ} (hf : Continuous f) {B T : ℝ}
    (hfix : ∀ p ∈ Icc (0 : ℝ) 1, ∀ y, y ≤ B ∨ T ≤ y → f (p, y) = 0) :
    ∃ M ≥ 0, ∀ p ∈ Icc (0 : ℝ) 1, ∀ y, |f (p, y)| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hf.continuousOn (s := Icc (0 : ℝ) 1 ×ˢ Icc B T))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp y
  by_cases hy : y ∈ Icc B T
  · have hbound : |f (p, y)| ≤ C := by simpa using hC (p, y) ⟨hp, hy⟩
    exact hbound.trans (le_max_left _ _)
  · have hy' : y ≤ B ∨ T ≤ y := by
      simp only [mem_Icc, not_and_or, not_le] at hy
      exact hy.imp le_of_lt le_of_lt
    rw [hfix p hp y hy', abs_zero]
    exact le_max_right _ _

theorem exists_compactly_supported_family_of_triangular_tail
    (D : ℝ → Diffeomorph (𝓡 2) (𝓡 2) E₂ E₂ ∞)
    (hD : ContDiff ℝ ∞ (fun z : ℝ × E₂ => D z.1 z.2))
    {L A B T : ℝ}
    (hDfix : ∀ p ∈ Icc (0 : ℝ) 1, ∀ x : E₂,
      x 0 ≤ L ∨ x 1 ≤ B ∨ T ≤ x 1 → D p x = x)
    (shift ρ κ : ℝ × ℝ → ℝ) (hshift : ContDiff ℝ ∞ shift) (hκ : ContDiff ℝ ∞ κ)
    (hκρ : ∀ p ∈ Icc (0 : ℝ) 1, ∀ y, κ (p, ρ (p, y)) = y)
    (hκpos : ∀ p ∈ Icc (0 : ℝ) 1, ∀ y, 0 < deriv (fun s => κ (p, s)) y)
    (hshiftfix : ∀ p ∈ Icc (0 : ℝ) 1, ∀ y, y ≤ B ∨ T ≤ y → shift (p, y) = 0)
    (hρfix : ∀ p ∈ Icc (0 : ℝ) 1, ∀ y, y ≤ B ∨ T ≤ y → ρ (p, y) = y)
    (hshift0 : ∀ y, shift (0, y) = 0) (hshift1 : ∀ y, shift (1, y) = 0)
    (hρ0 : ∀ y, ρ (0, y) = y) (hρ1 : ∀ y, ρ (1, y) = y)
    (htail : ∀ p ∈ Icc (0 : ℝ) 1, ∀ x : E₂, A ≤ x 0 →
      D p x = !₂[x 0 + shift (p, x 1), ρ (p, x 1)]) :
    ∃ F : ℝ → Diffeomorph (𝓡 2) (𝓡 2) E₂ E₂ ∞,
      ContDiff ℝ ∞ (fun z : ℝ × E₂ => F z.1 z.2) ∧
      (∀ x, F 0 x = D 0 x) ∧ (∀ x, F 1 x = D 1 x) ∧
      ∃ S : Set E₂, IsCompact S ∧ ∀ p x, x ∉ S → F p x = x := by
  let σ : ℝ → ℝ := fun p => Real.smoothTransition (3 * p - 1)
  have hσ : ContDiff ℝ ∞ σ := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hσrange (p : ℝ) : σ p ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hσ0 : σ 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hσ1 : σ 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  let Λ : ℝ × ℝ → ℝ := fun z => shift (σ z.1, z.2)
  let K : ℝ × ℝ → ℝ := fun z => κ (σ z.1, z.2)
  have hΛ : ContDiff ℝ ∞ Λ := hshift.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd)
  have hK : ContDiff ℝ ∞ K := hκ.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd)
  have hKfix (p y : ℝ) (hy : y ≤ B ∨ T ≤ y) : K (p, y) = y := by
    have := hκρ (σ p) (hσrange p) y
    simpa only [K, hρfix (σ p) (hσrange p) y hy] using this
  have hκfix (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (y : ℝ)
      (hy : y ≤ B ∨ T ≤ y) : κ (p, y) - y = 0 := by
    have := hκρ p hp y
    rw [hρfix p hp y hy] at this
    exact sub_eq_zero.mpr this
  obtain ⟨M, hM, hshiftbound⟩ := exists_uniform_strip_bound hshift.continuous hshiftfix
  obtain ⟨N, hN, hκbound⟩ := exists_uniform_strip_bound
    (hκ.continuous.sub continuous_snd) hκfix
  have hΛbound (p y : ℝ) : |Λ (p, y)| ≤ M := hshiftbound _ (hσrange p) y
  have hKbound (p y : ℝ) : |K (p, y) - y| ≤ N := hκbound _ (hσrange p) y
  have hKpos (p y : ℝ) : 0 < deriv (fun s => K (p, s)) y :=
    hκpos _ (hσrange p) y
  have hK0 (y : ℝ) : K (0, y) = y := by
    have := hκρ 0 (by norm_num) y
    simpa only [K, hσ0, hρ0] using this
  have hK1 (y : ℝ) : K (1, y) = y := by
    have := hκρ 1 (by norm_num) y
    simpa only [K, hσ1, hρ1] using this
  have hΛ0 (y : ℝ) : Λ (0, y) = 0 := by simp only [Λ, hσ0, hshift0]
  have hΛ1 (y : ℝ) : Λ (1, y) = 0 := by simp only [Λ, hσ1, hshift1]
  obtain ⟨η, b, hLb, hη, hηrange, hηleft, hηright, hηslow⟩ := exists_slow_cutoff L M hM
  let f : (ℝ × ℝ) × ℝ → ℝ :=
    fun z => z.2 + η z.1.2 * (K (z.1.1, z.2) - z.2)
  have hf : ContDiff ℝ ∞ f := contDiff_snd.add
    ((hη.comp (contDiff_snd.comp contDiff_fst)).mul
      ((hK.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)).sub contDiff_snd))
  have hfderiv (q : ℝ × ℝ) (y : ℝ) :
      deriv (fun s => f (q, s)) y = 1 + η q.2 * (deriv (fun s => K (q.1, s)) y - 1) := by
    have hdK := ((hK.comp ((contDiff_const (c := q.1)).prodMk contDiff_id)).differentiable
      (by simp) y).hasDerivAt
    convert! ((hasDerivAt_id y).add
      ((hdK.sub (hasDerivAt_id y)).const_mul (η q.2))).deriv using 1
  have hfpos (q : ℝ × ℝ) (y : ℝ) : 0 < deriv (fun s => f (q, s)) y := by
    rw [hfderiv]
    obtain ⟨hη0, hη1⟩ := hηrange q.2
    rcases hη0.eq_or_lt with hzero | hpos
    · rw [← hzero]
      norm_num
    · have hmul := mul_pos hpos (hKpos q.1 y)
      nlinarith
  have hfbound (q : ℝ × ℝ) : ∃ C : ℝ, ∀ y, |f (q, y) - y| ≤ C := by
    refine ⟨N, ?_⟩
    intro y
    have hηabs : |η q.2| ≤ 1 := by simpa [abs_of_nonneg (hηrange q.2).1] using (hηrange q.2).2
    calc
      |f (q, y) - y| = |η q.2| * |K (q.1, y) - y| := by simp [f, abs_mul]
      _ ≤ 1 * N := mul_le_mul hηabs (hKbound q.1 y) (abs_nonneg _) (by norm_num)
      _ = N := one_mul _
  obtain ⟨U, hU, hUeq⟩ := exists_vertical_triangular_family f hf hfpos hfbound
  let g : (ℝ × ℝ) × ℝ → ℝ := fun z => z.2 - η z.2 * Λ z.1
  have hg : ContDiff ℝ ∞ g := contDiff_snd.sub
    ((hη.comp contDiff_snd).mul (hΛ.comp contDiff_fst))
  have hgderiv (q : ℝ × ℝ) (x : ℝ) :
      deriv (fun s => g (q, s)) x = 1 - deriv η x * Λ q := by
    have hdη := (hη.differentiable (by simp) x).hasDerivAt
    convert! ((hasDerivAt_id x).sub (hdη.mul_const (Λ q))).deriv using 1
  have hgpos (q : ℝ × ℝ) (x : ℝ) : 0 < deriv (fun s => g (q, s)) x := by
    rw [hgderiv]
    have hprod : |deriv η x * Λ q| < 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hΛbound q.1 q.2) (abs_nonneg _)).trans_lt (hηslow x)
    have := (abs_lt.mp hprod).2
    linarith
  have hgbound (q : ℝ × ℝ) : ∃ C : ℝ, ∀ x, |g (q, x) - x| ≤ C := by
    refine ⟨M, ?_⟩
    intro x
    have hηabs : |η x| ≤ 1 := by simpa [abs_of_nonneg (hηrange x).1] using (hηrange x).2
    calc
      |g (q, x) - x| = |η x| * |Λ q| := by
        rw [show g (q, x) - x = -(η x * Λ q) by dsimp [g]; ring, abs_neg, abs_mul]
      _ ≤ 1 * M := mul_le_mul hηabs (hΛbound q.1 q.2) (abs_nonneg _) (by norm_num)
      _ = M := one_mul _
  obtain ⟨W, hW, hWeq⟩ := exists_horizontal_triangular_family g hg hgpos hgbound
  let F (p : ℝ) : Diffeomorph (𝓡 2) (𝓡 2) E₂ E₂ ∞ := ((D (σ p)).trans (U p)).trans (W p)
  have hFeq (p : ℝ) (x : E₂) : F p x = W p (U p (D (σ p) x)) := rfl
  have hF : ContDiff ℝ ∞ (fun z : ℝ × E₂ => F z.1 z.2) :=
    hW.comp (contDiff_fst.prodMk (hU.comp (contDiff_fst.prodMk
      (hD.comp ((hσ.comp contDiff_fst).prodMk contDiff_snd)))))
  have hU0 (x : E₂) : U 0 x = x := by
    rw [hUeq]
    ext i
    fin_cases i <;> simp [f, hK0]
  have hU1 (x : E₂) : U 1 x = x := by
    rw [hUeq]
    ext i
    fin_cases i <;> simp [f, hK1]
  have hW0 (x : E₂) : W 0 x = x := by
    rw [hWeq]
    ext i
    fin_cases i <;> simp [g, hΛ0]
  have hW1 (x : E₂) : W 1 x = x := by
    rw [hWeq]
    ext i
    fin_cases i <;> simp [g, hΛ1]
  refine ⟨F, hF, (fun x => by rw [hFeq, hσ0, hU0, hW0]),
    (fun x => by rw [hFeq, hσ1, hU1, hW1]), ?_⟩
  let C : ℝ := max A (b + M)
  let S : Set E₂ := (fun z : ℝ × ℝ => (!₂[z.1, z.2] : E₂)) '' (Icc L C ×ˢ Icc B T)
  have hmap : Continuous (fun z : ℝ × ℝ => (!₂[z.1, z.2] : E₂)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  refine ⟨S, (isCompact_Icc.prod isCompact_Icc).image hmap, ?_⟩
  intro p x hx
  have hp := hσrange p
  by_cases hxl : x 0 ≤ L
  · have hηx := hηleft (x 0) hxl
    rw [hFeq, hDfix _ hp x (Or.inl hxl), hUeq, hWeq]
    ext i
    fin_cases i <;> simp [f, g, hηx]
  · by_cases hxy : x 1 ≤ B ∨ T ≤ x 1
    · have hshiftx : Λ (p, x 1) = 0 := hshiftfix _ hp _ hxy
      have hκx := hKfix p (x 1) hxy
      rw [hFeq, hDfix _ hp x (Or.inr hxy), hUeq, hWeq]
      ext i
      fin_cases i <;> simp [f, g, hshiftx, hκx]
    · have hxC : C ≤ x 0 := by
        by_contra! hxC
        apply hx
        refine ⟨(x 0, x 1), ⟨⟨le_of_not_ge hxl, hxC.le⟩, ?_⟩, ?_⟩
        · simp only [not_or, not_le] at hxy
          exact ⟨hxy.1.le, hxy.2.le⟩
        · ext i
          fin_cases i <;> simp
      have hxA : A ≤ x 0 := (le_max_left _ _).trans hxC
      have hηx : η (x 0 + Λ (p, x 1)) = 1 := by
        apply hηright
        have hCM : b + M ≤ x 0 := (le_max_right _ _).trans hxC
        have hshiftlo := (abs_le.mp (hΛbound p (x 1))).1
        linarith
      have hκx : K (p, ρ (σ p, x 1)) = x 1 := hκρ _ hp _
      have hηx' : η (x 0 + shift (σ p, x 1)) = 1 := hηx
      rw [hFeq, htail _ hp x hxA, hUeq, hWeq]
      ext i
      fin_cases i <;> simp [f, g, hκx, hηx', Λ]

end Poincare.Manifold.PlaneDiffeomorph

import PoincareConjecture.Proofs.M13.Metric

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M13

variable {n : ℕ} {M : Type*} {N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]

theorem pathELength_eq_lintegral_tangentNorm (g : RiemannianMetric n M)
    (γ : ℝ → M) (a b : ℝ) :
    g.pathELength γ a b =
      ∫⁻ t in Set.Ioo a b,
        ENNReal.ofReal (g.tangentNorm (γ t) (mfderiv 𝓘(ℝ) (𝓡 n) γ t 1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength (𝓡 n) γ a b = _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t _
  dsimp only
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

theorem homothety_pathELength (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (γ : ℝ → M) (a b : ℝ)
    (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 γ (Set.Icc a b)) :
    h.pathELength (f ∘ γ) a b = ENNReal.ofReal (Real.sqrt Q) * g.pathELength γ a b := by
  rw [pathELength_eq_lintegral_tangentNorm, pathELength_eq_lintegral_tangentNorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  have hγt : MDifferentiableAt 𝓘(ℝ) (𝓡 n) γ t :=
    ((hγ.mdifferentiableOn one_ne_zero) t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  rw [mfderiv_comp t (f.mdifferentiable (by simp) (γ t)) hγt]
  change ENNReal.ofReal (h.tangentNorm (f (γ t))
    (mfderiv (𝓡 n) (𝓡 n) f (γ t) (mfderiv 𝓘(ℝ) (𝓡 n) γ t 1))) = _
  rw [homothety_tangentNorm g h f Q hQ hf, ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]

theorem edist_le_pathELength (g : RiemannianMetric n M) {x y : M} {γ : ℝ → M}
    {a b : ℝ} (hγ : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 γ (Set.Icc a b))
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) :
    g.edist x y ≤ g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_le_pathELength hγ ha hb hab

theorem exists_pathELength_lt (g : RiemannianMetric n M) {x y : M} {r : ℝ≥0∞}
    (hr : g.edist x y < r) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧
      ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 γ (Set.Icc 0 1) ∧ g.pathELength γ 0 1 < r := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.exists_lt_of_riemannianEDist_lt hr

theorem homothety_edist (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (x y : M) :
    h.edist (f x) (f y) = ENNReal.ofReal (Real.sqrt Q) * g.edist x y := by
  let c := ENNReal.ofReal (Real.sqrt Q)
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hQ)).ne'
  have hct : c ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  change h.edist (f x) (f y) = c * g.edist x y
  apply le_antisymm
  · apply (ENNReal.inv_mul_le_iff hc0 hct).1
    apply le_of_forall_gt
    intro r hr
    rcases exists_pathELength_lt g hr with ⟨γ, hγ0, hγ1, hγ, hγlt⟩
    have hbound : h.edist (f x) (f y) ≤ c * g.pathELength γ 0 1 := by
      rw [← homothety_pathELength g h f Q hQ hf γ 0 1 hγ]
      exact edist_le_pathELength h
        ((f.contMDiff.of_le (by simp)).comp_contMDiffOn hγ)
        (by simp [Function.comp_apply, hγ0]) (by simp [Function.comp_apply, hγ1])
        zero_le_one
    calc
      c⁻¹ * h.edist (f x) (f y) ≤ c⁻¹ * (c * g.pathELength γ 0 1) :=
        mul_le_mul_right hbound _
      _ = g.pathELength γ 0 1 := ENNReal.inv_mul_cancel_left hc0 hct
      _ < r := hγlt
  · apply le_of_forall_gt
    intro r hr
    rcases exists_pathELength_lt h hr with ⟨η, hη0, hη1, hη, hηlt⟩
    have hη' : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 (f.symm ∘ η) (Set.Icc 0 1) :=
      (f.symm.contMDiff.of_le (by simp)).comp_contMDiffOn hη
    have heq : f ∘ (f.symm ∘ η) = η := by
      ext t
      exact f.apply_symm_apply (η t)
    have hlen := homothety_pathELength g h f Q hQ hf (f.symm ∘ η) 0 1 hη'
    rw [heq] at hlen
    calc
      c * g.edist x y ≤ c * g.pathELength (f.symm ∘ η) 0 1 :=
        mul_le_mul_right (edist_le_pathELength g hη'
          (by simp [Function.comp_apply, hη0]) (by simp [Function.comp_apply, hη1])
          zero_le_one) c
      _ = h.pathELength η 0 1 := hlen.symm
      _ < r := hηlt

theorem homothety_ball_image (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (x : M) (r : ℝ) :
    f '' g.ball x r = h.ball (f x) (Real.sqrt Q * r) := by
  have hc0 : ENNReal.ofReal (Real.sqrt Q) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hQ)).ne'
  have hball (y : M) : y ∈ g.ball x r ↔ f y ∈ h.ball (f x) (Real.sqrt Q * r) := by
    change g.edist x y < ENNReal.ofReal r ↔
      h.edist (f x) (f y) < ENNReal.ofReal (Real.sqrt Q * r)
    rw [homothety_edist g h f Q hQ hf, ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
    exact (ENNReal.mul_right_strictMono hc0 ENNReal.ofReal_ne_top).lt_iff_lt.symm
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hball z).1 hz
  · intro hy
    refine ⟨f.symm y, (hball (f.symm y)).2 ?_, f.apply_symm_apply y⟩
    simpa only [f.apply_symm_apply] using hy

end PoincareConjecture.M13

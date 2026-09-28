import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.Local
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.Forward








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_forward_integralCurve_of_compact_confinement
    {X : (x : M) → TangentSpace (𝓡 n) x} {U K : Set M} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) U) {x : M} (hx : x ∈ K)
    (hconf : ∀ a b : ℝ, a < 0 → 0 < b → ∀ γ : ℝ → M, γ 0 = x →
      (∀ t ∈ Ioo a b, γ t ∈ U) → IsMIntegralCurveOn (I := 𝓡 n) γ X (Ioo a b) →
      ∀ t ∈ Ico 0 b, γ t ∈ K) :
    ∃ a < 0, ∃ γ : ℝ → M, γ 0 = x ∧ (∀ t ∈ Ioi a, γ t ∈ U) ∧
      IsMIntegralCurveOn (I := 𝓡 n) γ X (Ioi a) ∧
      ∀ t : ℝ, 0 ≤ t → γ t ∈ K := by
  obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_local_integralCurves hU hK hKU hX
  let d := δ / 2
  have hd : 0 < d := half_pos hδ
  have htwo : 2 * d = δ := by dsimp [d]; ring
  have hXone := hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hfinite (i : ℕ) : ∃ γ : ℝ → M, γ 0 = x ∧
      (∀ t ∈ Ioo (-d) ((i : ℝ) * d + d), γ t ∈ U) ∧
      IsMIntegralCurveOn (I := 𝓡 n) γ X (Ioo (-d) ((i : ℝ) * d + d)) := by
    induction i with
    | zero =>
      obtain ⟨γ, hγ0, hγU, hγ⟩ := hlocal x hx
      have hsub : Ioo (-d) (((0 : ℕ) : ℝ) * d + d) ⊆ Ioo (-δ) δ := by
        simp only [Nat.cast_zero, zero_mul, zero_add]
        apply Ioo_subset_Ioo <;> linarith
      exact ⟨γ, hγ0, fun t ht => hγU t (hsub ht), hγ.mono hsub⟩
    | succ i ih =>
      obtain ⟨α, hα0, hαU, hα⟩ := ih
      let s : ℝ := i * d
      have hs : 0 ≤ s := mul_nonneg (Nat.cast_nonneg _) hd.le
      have hsK : α s ∈ K :=
        hconf (-d) (s + d) (neg_lt_zero.mpr hd) (by linarith) α hα0 hαU hα
          s ⟨hs, lt_add_of_pos_right _ hd⟩
      obtain ⟨β, hβ0, hβU, hβ⟩ := hlocal (α s) hsK
      let β' : ℝ → M := fun t => β (t - s)
      have hβ'U : ∀ t ∈ Ioo (s - δ) (s + δ), β' t ∈ U := by
        intro t ht
        exact hβU (t - s) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hβ' : IsMIntegralCurveOn (I := 𝓡 n) β' X (Ioo (s - δ) (s + δ)) := by
        apply (hβ.comp_add (-s)).mono
        intro t ht
        change t + -s ∈ Ioo (-δ) δ
        constructor <;> linarith [ht.1, ht.2]
      obtain ⟨γ, heqα, _, hγU, hγ⟩ := exists_gluing_of_integralCurves hU hXone
        isOpen_Ioo isOpen_Ioo (convex_Ioo _ _) (convex_Ioo _ _) hαU hβ'U hα hβ'
        (show s ∈ Ioo (-d) (s + d) ∩ Ioo (s - δ) (s + δ) from
          ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩)
        (by simpa only [β', sub_self] using hβ0.symm)
      have hsub : Ioo (-d) (((i + 1 : ℕ) : ℝ) * d + d) ⊆
          Ioo (-d) (s + d) ∪ Ioo (s - δ) (s + δ) := by
        intro t ht
        by_cases hts : t < s + d
        · exact Or.inl ⟨ht.1, hts⟩
        · right
          have hsdef : s = (i : ℝ) * d := rfl
          simp only [Nat.cast_add, Nat.cast_one] at ht
          constructor <;> nlinarith [ht.2, le_of_not_gt hts]
      refine ⟨γ, (heqα ⟨by linarith, by change 0 < s + d; linarith⟩).trans hα0,
        fun t ht => hγU t (hsub ht), hγ.mono hsub⟩
  apply exists_forward_integralCurve_of_finite_integralCurves hU hXone
  intro k
  obtain ⟨i, hi⟩ := exists_nat_gt (((k : ℝ) + 1) / d)
  have hik : (k : ℝ) + 1 < (i : ℝ) * d := (div_lt_iff₀ hd).mp hi
  obtain ⟨γ, hγ0, hγU, hγ⟩ := hfinite i
  refine ⟨-d, (i : ℝ) * d + d, neg_lt_zero.mpr hd, by linarith,
    γ, hγ0, hγU, hγ, ?_⟩
  intro t ht
  exact hconf (-d) ((i : ℝ) * d + d) (neg_lt_zero.mpr hd) (by positivity)
    γ hγ0 hγU hγ t ⟨ht.1, by linarith [ht.2]⟩

end Poincare.Manifold

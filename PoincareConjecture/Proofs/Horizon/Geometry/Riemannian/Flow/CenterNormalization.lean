import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.CompactSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Flow.Normalization









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_bounded_positive_rescaling_eq_one_near_compact
    (g : RiemannianMetric n M)
    {X : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X))
    {K : Set M} (hK : IsCompact K) :
    ∃ (b : M → ℝ) (C : ℝ),
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ b ∧
      (∀ x, 0 < b x) ∧ (∀ x ∈ K, b =ᶠ[𝓝 x] 1) ∧
      0 ≤ C ∧ ∀ x, g.tangentNorm x (b x • X x) ≤ C := by
  obtain ⟨χ, hχ, hχcompact, _, hχrange, hχone⟩ :=
    PoincareConjecture.exists_contMDiff_cutoff_of_isCompact (n := n) hK isOpen_univ (subset_univ K)
  let s := g.boundedFieldScale X
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ s := g.contMDiff_boundedFieldScale hX
  have hspos (x : M) : 0 < s x := g.boundedFieldScale_pos X x
  have hsle (x : M) : s x ≤ 1 := by
    have hinner : 0 ≤ g.inner x (X x) (X x) := by
      by_cases hx : X x = 0
      · simp [hx]
      · exact (g.pos x (X x) hx).le
    exact (inv_le_one₀ (by linarith : 0 < 1 + g.inner x (X x) (X x))).mpr
      (by linarith)
  let b : M → ℝ := fun x => χ x + (1 - χ x) * s x
  have hb : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ b :=
    hχ.add ((contMDiff_const.sub hχ).mul hs)
  have hbpos (x : M) : 0 < b x := by
    dsimp only [b]
    rcases (hχrange x).2.eq_or_lt with h | h
    · simp only [h, sub_self, zero_mul, add_zero, zero_lt_one]
    · exact add_pos_of_nonneg_of_pos (hχrange x).1
        (mul_pos (sub_pos.mpr h) (hspos x))
  have hble (x : M) : b x ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (hsle x) (sub_nonneg.mpr (hχrange x).2)
    dsimp only [b]
    nlinarith only [h]
  have hnorm : Continuous (fun x => g.tangentNorm x (X x)) := by
    have hi : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun x => g.inner x (X x) (X x)) := by
      intro x
      have h := ((g.contMDiff x).clm_bundle_apply (hX x)).clm_bundle_apply (hX x)
      simpa using (contMDiffAt_totalSpace.mp h).2
    exact hi.continuous.sqrt
  obtain ⟨A, hA⟩ := hχcompact.bddAbove_image hnorm.continuousOn
  refine ⟨b, max 1 A, hb, hbpos, ?_, (zero_le_one.trans (le_max_left _ _)), ?_⟩
  · intro x hx
    filter_upwards [hχone x hx] with y hy
    simp only [b, hy, Pi.one_apply, sub_self, zero_mul, add_zero]
  · intro x
    by_cases hx : x ∈ tsupport χ
    · have hnormbound : g.tangentNorm x (X x) ≤ A := hA ⟨x, hx, rfl⟩
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      change ‖X x‖ ≤ A at hnormbound
      change ‖b x • X x‖ ≤ max 1 A
      rw [norm_smul, Real.norm_of_nonneg (hbpos x).le]
      calc
        b x * ‖X x‖ ≤ 1 * ‖X x‖ := mul_le_mul_of_nonneg_right (hble x) (norm_nonneg _)
        _ ≤ max 1 A := by simpa only [one_mul] using hnormbound.trans (le_max_right _ _)
    · have hzero := image_eq_zero_of_notMem_tsupport hx
      have hbx : b x = s x := by simp only [b, hzero, sub_zero, one_mul, zero_add]
      rw [hbx]
      exact (g.tangentNorm_boundedField_le_one X x).trans (le_max_left _ _)




theorem exists_smooth_globalFlow_of_rescaling_eq_one_near_compact
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {X : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X))
    {K : Set M} (hK : IsCompact K) :
    ∃ (b : M → ℝ) (C : ℝ) (Φ : ℝ → M → M),
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ b ∧
      (∀ x, 0 < b x) ∧ (∀ x ∈ K, b =ᶠ[𝓝 x] 1) ∧
      0 ≤ C ∧ (∀ x, g.tangentNorm x (b x • X x) ≤ C) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) (fun y => b y • X y)) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ) := by
  obtain ⟨b, C, hb, hbpos, hbone, hC, hbound⟩ :=
    g.exists_bounded_positive_rescaling_eq_one_near_compact hX hK
  obtain ⟨Φ, hi, hcurve, hadd, hΦ⟩ := g.exists_smooth_globalFlow_of_bounded_speed hc
    (fun x => (hb x).smul_section (hX x)) hC hbound
  exact ⟨b, C, Φ, hb, hbpos, hbone, hC, hbound, hi, hcurve, hadd, hΦ⟩

end PoincareConjecture.RiemannianMetric

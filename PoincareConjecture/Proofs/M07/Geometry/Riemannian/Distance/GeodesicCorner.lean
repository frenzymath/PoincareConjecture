import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.CornerRigidity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ExponentialRays
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.BrokenSegment

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem tangentNorm_smul_nonneg (g : RiemannianMetric n M)
    (p : M) (v : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 ≤ t) :
    g.tangentNorm p (t • v) = t * g.tangentNorm p v := by
  simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]

theorem normalized_initial_eq_neg_of_minimizing_broken_geodesics_of_exponential
    (g : RiemannianMetric n M) (p : M)
    (e : EuclideanSpace ℝ (Fin n) → M) {r : ℝ} (hr : 0 < r)
    (hexp : ∀ v : EuclideanSpace ℝ (Fin n), g.tangentNorm p v < r →
      ∃ η : ℝ → M, g.IsGeodesicOn η (Icc (0 : ℝ) 1) ∧ η 0 = p ∧
        HasDerivAt (fun t => extChartAt (𝓡 n) p (η t)) v 0 ∧ η 1 = e v)
    (hchord : ∀ θ : ℝ, 1 < θ → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ v w : EuclideanSpace ℝ (Fin n), ‖v‖ < ρ → ‖w‖ < ρ →
        g.edist (e v) (e w) ≤ ENNReal.ofReal (θ * g.tangentNorm p (w - v)))
    {α β : ℝ → M}
    (hα : g.IsGeodesicOn α (Icc (0 : ℝ) 1))
    (hβ : g.IsGeodesicOn β (Icc (0 : ℝ) 1))
    (hα0 : α 0 = p) (hβ0 : β 0 = p)
    {w₁ w₂ : EuclideanSpace ℝ (Fin n)}
    (hαv : HasDerivAt (fun t => extChartAt (𝓡 n) p (α t)) w₁ 0)
    (hβv : HasDerivAt (fun t => extChartAt (𝓡 n) p (β t)) w₂ 0)
    (hA : 0 < g.tangentNorm p w₁) (hB : 0 < g.tangentNorm p w₂)
    (hαupper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (α s) (α t) ≤ ENNReal.ofReal (|s - t| * g.tangentNorm p w₁))
    (hβupper : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (β s) (β t) ≤ ENNReal.ofReal (|s - t| * g.tangentNorm p w₂))
    (hdist : g.edist (α 1) (β 1) =
      ENNReal.ofReal (g.tangentNorm p w₁ + g.tangentNorm p w₂)) :
    (g.tangentNorm p w₂)⁻¹ • w₂ = -((g.tangentNorm p w₁)⁻¹ • w₁) := by
  let A := g.tangentNorm p w₁
  let B := g.tangentNorm p w₂
  let u₁ : EuclideanSpace ℝ (Fin n) := A⁻¹ • w₁
  let u₂ : EuclideanSpace ℝ (Fin n) := B⁻¹ • w₂
  have hunit₁ : g.tangentNorm p u₁ = 1 := by
    rw [tangentNorm_smul_nonneg g p w₁ (inv_nonneg.mpr hA.le)]
    exact inv_mul_cancel₀ hA.ne'
  have hunit₂ : g.tangentNorm p u₂ = 1 := by
    rw [tangentNorm_smul_nonneg g p w₂ (inv_nonneg.mpr hB.le)]
    exact inv_mul_cancel₀ hB.ne'
  apply g.eq_neg_of_radial_edist_eq p e hchord hunit₁ hunit₂
    (lt_min hr (lt_min hA hB))
  intro η hη hηsmall
  have hηr : η < r := hηsmall.trans_le (min_le_left _ _)
  have hηA : η < A := hηsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hηB : η < B := hηsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htA : η / A ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos hη hA).le, (div_le_one hA).mpr hηA.le⟩
  have htB : η / B ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos hη hB).le, (div_le_one hB).mpr hηB.le⟩
  have hsmul₁ : (η / A) • w₁ = η • u₁ := by simp only [u₁, smul_smul, div_eq_mul_inv]
  have hsmul₂ : (η / B) • w₂ = η • u₂ := by simp only [u₂, smul_smul, div_eq_mul_inv]
  have hr₁ : g.tangentNorm p ((η / A) • w₁) < r := by
    rw [hsmul₁, tangentNorm_smul_nonneg g p u₁ hη.le, hunit₁, mul_one]
    exact hηr
  have hr₂ : g.tangentNorm p ((η / B) • w₂) < r := by
    rw [hsmul₂, tangentNorm_smul_nonneg g p u₂ hη.le, hunit₂, mul_one]
    exact hηr
  have hread₁ := g.exponential_eq_geodesic_of_unit_initial_data p e hexp hα hα0 hαv htA hr₁
  have hread₂ := g.exponential_eq_geodesic_of_unit_initial_data p e hexp hβ hβ0 hβv htB hr₂
  rw [hsmul₁] at hread₁
  rw [hsmul₂] at hread₂
  rw [hread₁, hread₂]
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hnear {C : ℝ} (hC : 0 < C) (hηC : η < C) :
      |η / C - 0| * C = η ∧ |0 - η / C| * C = η ∧
      |1 - η / C| * C = C - η ∧ |η / C - 1| * C = C - η := by
    have ht : 0 ≤ η / C := (div_pos hη hC).le
    have ht1 : η / C ≤ 1 := (div_le_one hC).mpr hηC.le
    have hmul : η / C * C = η := div_mul_cancel₀ η hC.ne'
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg ht,
      abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonpos (sub_nonpos.mpr ht1), hmul]
    constructor
    · simpa [hmul]
    · exact ⟨trivial, by rw [sub_mul, one_mul, hmul], by rw [neg_sub, sub_mul, one_mul, hmul]⟩
  obtain ⟨ha₀, _, ha₁, _⟩ := hnear hA hηA
  obtain ⟨_, hb₀, _, hb₁⟩ := hnear hB hηB
  have hax : EDist.edist (α 1) (α (η / A)) ≤ ENNReal.ofReal (A - η) := by
    have hh := hαupper 1 (by simp) (η / A) htA
    simpa only [A, ha₁] using! hh
  have hxc : EDist.edist (α (η / A)) p ≤ ENNReal.ofReal η := by
    have hh := hαupper (η / A) htA 0 (by simp)
    rw [hα0] at hh
    simpa only [A, ha₀] using! hh
  have hcy : EDist.edist p (β (η / B)) ≤ ENNReal.ofReal η := by
    have hh := hβupper 0 (by simp) (η / B) htB
    rw [hβ0] at hh
    simpa only [B, hb₀] using! hh
  have hyb : EDist.edist (β (η / B)) (β 1) ≤ ENNReal.ofReal (B - η) := by
    have hh := hβupper (η / B) htB 1 (by simp)
    simpa only [B, hb₁] using! hh
  have hh := Poincare.MetricCurves.edist_eq_of_broken_segment hη.le hηA.le hη.le hηB.le
    hdist hax hxc hcy hyb
  simpa only [two_mul] using! hh

end PoincareConjecture.RiemannianMetric

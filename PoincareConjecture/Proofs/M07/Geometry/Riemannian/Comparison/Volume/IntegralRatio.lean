import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Model

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

theorem lintegral_cross_le {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    {a b c : ℝ} (hcross : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo b c,
      F s * G t ≤ F t * G s) :
    (∫⁻ s in Ioo b c, F s) * (∫⁻ t in Ioo a b, G t)
      ≤ (∫⁻ t in Ioo a b, F t) * (∫⁻ s in Ioo b c, G s) := by
  have hL : (∫⁻ s in Ioo b c, F s) * (∫⁻ t in Ioo a b, G t)
      = ∫⁻ s in Ioo b c, (∫⁻ t in Ioo a b, F s * G t) := by
    rw [← lintegral_mul_const _ hF]
    exact lintegral_congr fun s => (lintegral_const_mul (F s) hG).symm
  have hR : (∫⁻ t in Ioo a b, F t) * (∫⁻ s in Ioo b c, G s)
      = ∫⁻ s in Ioo b c, (∫⁻ t in Ioo a b, F t * G s) := by
    have hinner : ∀ s : ℝ,
        (∫⁻ t in Ioo a b, F t * G s) = (∫⁻ t in Ioo a b, F t) * G s :=
      fun s => lintegral_mul_const (G s) hF
    simp_rw [hinner]
    exact (lintegral_const_mul _ hG).symm
  rw [hL, hR]
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  exact setLIntegral_mono' measurableSet_Ioo fun t ht => hcross t ht s hs

theorem angular_lintegral_cross_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {A B : Ω → ℝ≥0∞} {C D : ℝ≥0∞}
    (hA : Measurable A) (hB : Measurable B)
    (hcross : ∀ ω, B ω * C ≤ A ω * D) :
    (∫⁻ ω, B ω ∂μ) * C ≤ (∫⁻ ω, A ω ∂μ) * D := by
  rw [← lintegral_mul_const C hB, ← lintegral_mul_const D hA]
  exact lintegral_mono hcross

theorem angular_cumulative_cross_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F : Ω → ℝ → ℝ≥0∞} {G : ℝ → ℝ≥0∞}
    (hF : Measurable (fun p : Ω × ℝ => F p.1 p.2)) (hG : Measurable G)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ ≤ r₂)
    (hcross : ∀ ω, ∀ t ∈ Ioo (0 : ℝ) r₁, ∀ s ∈ Ioo r₁ r₂,
      F ω s * G t ≤ F ω t * G s) :
    (∫⁻ ω, (∫⁻ t in Ioo (0 : ℝ) r₂, F ω t) ∂μ) *
        (∫⁻ t in Ioo (0 : ℝ) r₁, G t)
      ≤ (∫⁻ ω, (∫⁻ t in Ioo (0 : ℝ) r₁, F ω t) ∂μ) *
        (∫⁻ t in Ioo (0 : ℝ) r₂, G t) := by
  have hFslice : ∀ ω : Ω, Measurable (F ω) :=
    fun ω => hF.comp measurable_prodMk_left
  have hFcum : ∀ s : Set ℝ,
      Measurable (fun ω : Ω => ∫⁻ t in s, F ω t) :=
    fun s => Measurable.lintegral_prod_right' (ν := volume.restrict s) hF
  have hsplit : ∀ H : ℝ → ℝ≥0∞,
      (∫⁻ t in Ioo (0 : ℝ) r₂, H t) =
        (∫⁻ t in Ioo (0 : ℝ) r₁, H t) + ∫⁻ t in Ioo r₁ r₂, H t := by
    intro H
    have hset : Ioo (0 : ℝ) r₁ ∪ Ico r₁ r₂ = Ioo (0 : ℝ) r₂ :=
      Set.Ioo_union_Ico_eq_Ioo hr₁ h12
    have hdisj : Disjoint (Ioo (0 : ℝ) r₁) (Ico r₁ r₂) :=
      Set.disjoint_left.2 fun x hx hx' => absurd hx'.1 (not_le.2 hx.2)
    rw [← hset, lintegral_union measurableSet_Ico hdisj]
    congr 1
    exact setLIntegral_congr (Ioo_ae_eq_Ico (a := r₁) (b := r₂)).symm
  let A : ℝ≥0∞ := ∫⁻ ω, (∫⁻ t in Ioo (0 : ℝ) r₁, F ω t) ∂μ
  let B : ℝ≥0∞ := ∫⁻ ω, (∫⁻ t in Ioo r₁ r₂, F ω t) ∂μ
  let C : ℝ≥0∞ := ∫⁻ t in Ioo (0 : ℝ) r₁, G t
  let D : ℝ≥0∞ := ∫⁻ t in Ioo r₁ r₂, G t
  have houter :
      (∫⁻ ω, (∫⁻ t in Ioo (0 : ℝ) r₂, F ω t) ∂μ) = A + B := by
    rw [show A = _ from rfl, show B = _ from rfl,
      ← lintegral_add_left (hFcum (Ioo (0 : ℝ) r₁))]
    exact lintegral_congr fun ω => hsplit (F ω)
  have hBC : B * C ≤ A * D := by
    apply angular_lintegral_cross_le μ (hFcum (Ioo (0 : ℝ) r₁))
      (hFcum (Ioo r₁ r₂))
    intro ω
    exact lintegral_cross_le (hFslice ω) hG (hcross ω)
  rw [houter]
  rw [hsplit G]
  change (A + B) * C ≤ A * (C + D)
  calc
    (A + B) * C = A * C + B * C := by rw [add_mul]
    _ ≤ A * C + A * D := by
      simpa [add_comm] using add_le_add_left hBC (A * C)
    _ = A * (C + D) := by rw [mul_add]

theorem antitoneOn_angular_cumulative_ratio {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F : Ω → ℝ → ℝ≥0∞} {G : ℝ → ℝ≥0∞} {R : ℝ}
    (hF : Measurable (fun p : Ω × ℝ => F p.1 p.2)) (hG : Measurable G)
    (hmodel : ∀ r ∈ Ioo (0 : ℝ) R,
      (∫⁻ t in Ioo (0 : ℝ) r, G t) ≠ 0 ∧
        (∫⁻ t in Ioo (0 : ℝ) r, G t) ≠ ⊤)
    (hcross : ∀ ω, ∀ t ∈ Ioo (0 : ℝ) R, ∀ s ∈ Ioo (0 : ℝ) R,
      t ≤ s → F ω s * G t ≤ F ω t * G s) :
    AntitoneOn (fun r : ℝ =>
      (∫⁻ ω, (∫⁻ t in Ioo (0 : ℝ) r, F ω t) ∂μ) /
        (∫⁻ t in Ioo (0 : ℝ) r, G t)) (Ioo 0 R) := by
  intro r hr s hs hrs
  have hc := angular_cumulative_cross_le μ hF hG hr.1 hrs
    (fun ω t ht u hu => hcross ω t ⟨ht.1, ht.2.trans hr.2⟩
      u ⟨hr.1.trans hu.1, hu.2.trans hs.2⟩ (ht.2.trans hu.1).le)
  change
    (∫⁻ ω, (∫⁻ t in Ioo (0 : ℝ) s, F ω t) ∂μ) /
        (∫⁻ t in Ioo (0 : ℝ) s, G t) ≤
      (∫⁻ ω, (∫⁻ t in Ioo (0 : ℝ) r, F ω t) ∂μ) /
        (∫⁻ t in Ioo (0 : ℝ) r, G t)
  apply (ENNReal.div_le_iff (hmodel s hs).1 (hmodel s hs).2).2
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
    (ENNReal.le_div_iff_mul_le (Or.inl (hmodel r hr).1)
      (Or.inl (hmodel r hr).2)).2 hc

end PoincareConjecture.RiemannianMetric

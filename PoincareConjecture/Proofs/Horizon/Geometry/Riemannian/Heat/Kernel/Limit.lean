import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Local
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma norm_integral_test_mul_sub_le
    {φ U V : M → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hU : ContinuousOn U (tsupport φ)) (hV : ContinuousOn V (tsupport φ)) {δ : ℝ}
    (hUV : ∀ x ∈ tsupport φ, ‖U x - V x‖ ≤ δ) :
    ‖(∫ x, φ x * U x ∂g.volumeMeasure) -
      (∫ x, φ x * V x ∂g.volumeMeasure)‖ ≤
      δ * ∫ x, ‖φ x‖ ∂g.volumeMeasure := by
  have hφi := hφ.integrable_of_hasCompactSupport (μ := g.volumeMeasure) hφc
  have hφU : Integrable (fun x => φ x * U x) g.volumeMeasure :=
    ((hφ.continuousOn.mul hU).integrableOn_compact hφc).integrable_of_forall_notMem_eq_zero
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hφV : Integrable (fun x => φ x * V x) g.volumeMeasure :=
    ((hφ.continuousOn.mul hV).integrableOn_compact hφc).integrable_of_forall_notMem_eq_zero
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  rw [← integral_sub hφU hφV]
  calc
    _ ≤ ∫ x, δ * ‖φ x‖ ∂g.volumeMeasure := by
      apply norm_integral_le_of_norm_le (hφi.norm.const_mul δ)
      filter_upwards [] with x
      by_cases hx : x ∈ tsupport φ
      · rw [← mul_sub, norm_mul]
        exact (mul_le_mul_of_nonneg_left (hUV x hx) (norm_nonneg _)).trans_eq
          (mul_comm _ _)
      · simp [image_eq_zero_of_notMem_tsupport hx]
    _ = _ := integral_const_mul _ _

theorem tendstoUniformlyOn_integral_test_mul
    {F : ℕ → ℝ × M → ℝ} {U : ℝ × M → ℝ} {s : Set ℝ}
    {φ : M → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hF : ∀ᶠ j in atTop, ∀ t ∈ s, ContinuousOn (fun x => F j (t, x)) (tsupport φ))
    (hU : ∀ t ∈ s, ContinuousOn (fun x => U (t, x)) (tsupport φ))
    (hlim : TendstoUniformlyOn F U atTop (s ×ˢ tsupport φ)) :
    TendstoUniformlyOn (fun j t => ∫ x, φ x * F j (t, x) ∂g.volumeMeasure)
      (fun t => ∫ x, φ x * U (t, x) ∂g.volumeMeasure) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at hlim ⊢
  intro ε hε
  let C := ∫ x, ‖φ x‖ ∂g.volumeMeasure
  have hC : 0 ≤ C := integral_nonneg (fun _ => norm_nonneg _)
  have hδ : 0 < ε / (C + 1) := div_pos hε (by positivity)
  filter_upwards [hlim (ε / (C + 1)) hδ, hF] with j hj hFj
  intro t ht
  rw [dist_comm, dist_eq_norm]
  have hb := norm_integral_test_mul_sub_le (g := g) hφ hφc
    (hFj t ht) (hU t ht) (fun x hx => by
      simpa only [dist_eq_norm, norm_sub_rev] using (hj (t, x) ⟨ht, hx⟩).le)
  have heq : ε / (C + 1) * (C + 1) = ε := div_mul_cancel₀ ε (by positivity)
  exact hb.trans_lt (by change ε / (C + 1) * C < ε; nlinarith)

theorem integral_test_mul_sub_eq_of_tendstoUniformlyOn
    (D : LeviCivitaData g) {F : ℕ → ℝ × M → ℝ} {U : ℝ × M → ℝ}
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ j, ContinuousOn (F j) (Icc a b ×ˢ univ))
    (hU : ContinuousOn U (Icc a b ×ˢ univ))
    (hlim : TendstoUniformlyOn F U atTop (Icc a b ×ˢ tsupport φ))
    (hweak : ∀ᶠ j in atTop,
      (∫ x, φ x * F j (b, x) ∂g.volumeMeasure) -
        (∫ x, φ x * F j (a, x) ∂g.volumeMeasure) =
      ∫ t in a..b, ∫ x, F j (t, x) * D.laplacian φ x ∂g.volumeMeasure) :
    (∫ x, φ x * U (b, x) ∂g.volumeMeasure) -
        (∫ x, φ x * U (a, x) ∂g.volumeMeasure) =
      ∫ t in a..b, ∫ x, U (t, x) * D.laplacian φ x ∂g.volumeMeasure := by
  have hFc (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      Continuous (fun x => F j (t, x)) := by
    rw [← continuousOn_univ]
    exact (hF j).comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ => ⟨ht, mem_univ x⟩)
  have hUc (t : ℝ) (ht : t ∈ Icc a b) : Continuous (fun x => U (t, x)) := by
    rw [← continuousOn_univ]
    exact hU.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x _ => ⟨ht, mem_univ x⟩)
  have hl := tendstoUniformlyOn_integral_test_mul (g := g) hφ.continuous hφc
    (Eventually.of_forall (fun j t ht => (hFc j t ht).continuousOn))
    (fun t ht => (hUc t ht).continuousOn) hlim
  have hr := tendstoUniformlyOn_integral_test_mul (g := g) (D.continuous_laplacian hφ)
    (D.hasCompactSupport_laplacian hφc)
    (Eventually.of_forall (fun j t ht => (hFc j t ht).continuousOn))
    (fun t ht => (hUc t ht).continuousOn)
    (hlim.mono (prod_mono Subset.rfl (D.tsupport_laplacian_subset φ)))
  have hcont (j : ℕ) : ContinuousOn
      (fun t => ∫ x, D.laplacian φ x * F j (t, x) ∂g.volumeMeasure) (Icc a b) := by
    apply continuousOn_integral_of_compact_support hφc.isCompact
    · exact ((D.continuous_laplacian hφ).comp continuous_snd).continuousOn.mul
        ((hF j).mono (prod_mono Subset.rfl (subset_univ _)))
    · intro t x _ hx
      simp [D.laplacian_eq_zero_of_notMem_tsupport hx]
  rw [← uIcc_of_le hab] at hr hcont
  have hr' := hr.tendsto_intervalIntegral_of_continuousOn (μ := volume)
    (Eventually.of_forall hcont)
  simp_rw [mul_comm (D.laplacian φ _) (F _ _), mul_comm (D.laplacian φ _) (U _)] at hr'
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hl.tendsto_at ⟨hab, le_rfl⟩).sub (hl.tendsto_at ⟨le_rfl, hab⟩)) hr' hweak

theorem integral_test_mul_heat_sub_of_tendstoUniformlyOn [PreconnectedSpace M]
    (D : LeviCivitaData g) {F : ℕ → ℝ × M → ℝ} {U : ℝ × M → ℝ}
    (hF : ∀ j, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (F j) (Ioi 0 ×ˢ univ))
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hU : ContinuousOn U (Icc a b ×ˢ univ))
    (hlim : TendstoUniformlyOn F U atTop (Icc a b ×ˢ tsupport φ))
    (hheat : ∀ᶠ j in atTop, ∀ t ∈ Icc a b, ∀ x ∈ tsupport φ,
      HasDerivAt (fun s => F j (s, x)) (D.laplacian (fun y => F j (t, y)) x) t) :
    (∫ x, φ x * U (b, x) ∂g.volumeMeasure) -
        (∫ x, φ x * U (a, x) ∂g.volumeMeasure) =
      ∫ t in a..b, ∫ x, U (t, x) * D.laplacian φ x ∂g.volumeMeasure := by
  apply D.integral_test_mul_sub_eq_of_tendstoUniformlyOn hφ hφc hab
    (fun j => (hF j).continuousOn.mono
      (prod_mono (fun t ht => ha.trans_le ht.1) Subset.rfl)) hU hlim
  filter_upwards [hheat] with j hj
  exact D.integral_test_mul_heat_sub_on_tsupport (hF j) hφ hφc ha hab hj

theorem hasDerivAt_integral_test_mul_of_tendstoUniformlyOn_domains [PreconnectedSpace M]
    (D : LeviCivitaData g) {F : ℕ → ℝ × M → ℝ} {U : ℝ × M → ℝ}
    {Ω : ℕ → Set M} (hΩ : ∀ j, IsOpen (Ω j))
    (hF : ∀ j, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (F j) (Ioi 0 ×ˢ Ω j))
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφΩ : ∀ᶠ j in atTop, tsupport φ ⊆ Ω j)
    {s : Set ℝ} (hs : IsOpen s) (hs0 : s ⊆ Ioi 0)
    (hU : ∀ t ∈ s, ContinuousOn (fun x => U (t, x)) (tsupport φ))
    (hlim : TendstoUniformlyOn F U atTop (s ×ˢ tsupport φ))
    (hheat : ∀ᶠ j in atTop, ∀ t ∈ s, ∀ x ∈ tsupport φ,
      HasDerivAt (fun r => F j (r, x)) (D.laplacian (fun y => F j (t, y)) x) t)
    {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (fun r => ∫ x, φ x * U (r, x) ∂g.volumeMeasure)
      (∫ x, U (t, x) * D.laplacian φ x ∂g.volumeMeasure) t := by
  have hFc : ∀ᶠ j in atTop, ∀ r ∈ s,
      ContinuousOn (fun x => F j (r, x)) (tsupport φ) := by
    filter_upwards [hφΩ] with j hj
    intro r hr
    exact (hF j).continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => ⟨hs0 hr, hj hx⟩)
  have hl := tendstoUniformlyOn_integral_test_mul (g := g) hφ.continuous hφc hFc hU hlim
  have hr := tendstoUniformlyOn_integral_test_mul (g := g) (D.continuous_laplacian hφ)
    (D.hasCompactSupport_laplacian hφc)
    (hFc.mono (fun j hj r hr => (hj r hr).mono (D.tsupport_laplacian_subset φ)))
    (fun r hr => (hU r hr).mono (D.tsupport_laplacian_subset φ))
    (hlim.mono (prod_mono Subset.rfl (D.tsupport_laplacian_subset φ)))
  simp_rw [mul_comm (D.laplacian φ _) (F _ _), mul_comm (D.laplacian φ _) (U _)] at hr
  apply hasDerivAt_of_tendstoUniformlyOn hs hr ?_ (fun r hr => hl.tendsto_at hr) ht
  filter_upwards [hheat, hφΩ] with j hj hφj
  intro r hr
  exact D.hasDerivAt_integral_test_mul_of_heatEquationOn (hΩ j) (hF j) hφ hφc hφj
    (hs0 hr) (hj r hr)

theorem hasDerivAt_integral_test_mul_of_tendstoUniformlyOn [PreconnectedSpace M]
    (D : LeviCivitaData g) {F : ℕ → ℝ × M → ℝ} {U : ℝ × M → ℝ}
    (hF : ∀ j, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (F j) (Ioi 0 ×ˢ univ))
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) {s : Set ℝ} (hs : IsOpen s) (hs0 : s ⊆ Ioi 0)
    (hU : ∀ t ∈ s, Continuous (fun x => U (t, x)))
    (hlim : TendstoUniformlyOn F U atTop (s ×ˢ tsupport φ))
    (hheat : ∀ᶠ j in atTop, ∀ t ∈ s, ∀ x ∈ tsupport φ,
      HasDerivAt (fun r => F j (r, x)) (D.laplacian (fun y => F j (t, y)) x) t)
    {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (fun r => ∫ x, φ x * U (r, x) ∂g.volumeMeasure)
      (∫ x, U (t, x) * D.laplacian φ x ∂g.volumeMeasure) t :=
  D.hasDerivAt_integral_test_mul_of_tendstoUniformlyOn_domains (fun _ => isOpen_univ) hF
    hφ hφc (Eventually.of_forall (fun _ => subset_univ _)) hs hs0
    (fun r hr => (hU r hr).continuousOn) hlim hheat ht

theorem hasDerivAt_integral_test_mul_of_exhaustion [PreconnectedSpace M]
    (D : LeviCivitaData g) {Ω : ℕ → Set M} (hΩ : ∀ j, IsOpen (Ω j))
    (hmono : Monotone Ω) (hcover : ⋃ j, Ω j = univ)
    {F : ℕ → ℝ × M → ℝ} {U : ℝ × M → ℝ}
    (hF : ∀ j, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (F j) (Ioi 0 ×ˢ Ω j))
    (hheat : ∀ j t, 0 < t → ∀ x ∈ Ω j,
      HasDerivAt (fun r => F j (r, x)) (D.laplacian (fun y => F j (t, y)) x) t)
    (hlim : TendstoLocallyUniformlyOn F U atTop (Ioi 0 ×ˢ univ))
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun r => ∫ x, φ x * U (r, x) ∂g.volumeMeasure)
      (∫ x, U (t, x) * D.laplacian φ x ∂g.volumeMeasure) t := by
  obtain ⟨N, hN⟩ := hφc.isCompact.elim_directed_cover Ω hΩ
    (by rw [hcover]; exact subset_univ _) hmono.directed_le
  have hφΩ : ∀ᶠ j in atTop, tsupport φ ⊆ Ω j :=
    eventually_atTop.mpr ⟨N, fun j hj => hN.trans (hmono hj)⟩
  have hc : IsCompact (Icc (t / 2) (t + 1) ×ˢ tsupport φ) := isCompact_Icc.prod hφc
  have hpos : Icc (t / 2) (t + 1) ⊆ Ioi (0 : ℝ) := by
    intro r hr
    change 0 < r
    linarith [hr.1]
  have hl := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hc).mp
    (hlim.mono (prod_mono hpos (subset_univ _)))
  have hFc : ∀ᶠ j in atTop, ContinuousOn (F j) (Icc (t / 2) (t + 1) ×ˢ tsupport φ) := by
    filter_upwards [hφΩ] with j hj
    exact (hF j).continuousOn.mono (prod_mono hpos hj)
  have hUc := hl.continuousOn hFc.frequently
  apply D.hasDerivAt_integral_test_mul_of_tendstoUniformlyOn_domains hΩ hF hφ hφc hφΩ
    isOpen_Ioo (Ioo_subset_Icc_self.trans hpos) ?_
    (hl.mono (prod_mono Ioo_subset_Icc_self Subset.rfl)) ?_ (by constructor <;> linarith)
  · intro r hr
    exact hUc.comp (continuousOn_const.prodMk continuousOn_id)
      (fun x hx => ⟨Ioo_subset_Icc_self hr, hx⟩)
  · filter_upwards [hφΩ] with j hj
    intro r hr x hx
    exact hheat j r (hpos (Ioo_subset_Icc_self hr)) x (hj hx)

end PoincareConjecture.LeviCivitaData

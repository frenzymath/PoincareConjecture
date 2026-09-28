import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.AncientCompactness

variable {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]

theorem time_lipschitz_of_interior_tendsto
    {f : ℕ → ℝ → Y} {g : ℝ → Y} {a b L : ℝ} (hab : a < b)
    (hg : ContinuousOn g (Icc a b))
    (hconv : ∀ t ∈ Ioo a b, Tendsto (fun k => f k t) atTop (𝓝 (g t)))
    (hL : ∀ᶠ k in atTop, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      dist (f k s) (f k t) ≤ L * |s - t|) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, dist (g s) (g t) ≤ L * |s - t| := by
  have hdist : ContinuousOn (fun p : ℝ × ℝ => dist (g p.1) (g p.2))
      (Icc a b ×ˢ Icc a b) := by
    have hfst : ContinuousOn (fun p : ℝ × ℝ => g p.1) (Icc a b ×ˢ Icc a b) :=
      hg.comp continuousOn_fst (fun _ hp => hp.1)
    have hsnd : ContinuousOn (fun p : ℝ × ℝ => g p.2) (Icc a b ×ˢ Icc a b) :=
      hg.comp continuousOn_snd (fun _ hp => hp.2)
    exact fun p hp => Filter.Tendsto.dist (hfst p hp) (hsnd p hp)
  intro s hs t ht
  have hclosure : (s, t) ∈ closure (Ioo a b ×ˢ Ioo a b) := by
    rw [closure_prod_eq, closure_Ioo hab.ne]
    exact ⟨hs, ht⟩
  apply ContinuousWithinAt.closure_le hclosure
    ((hdist (s, t) ⟨hs, ht⟩).mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self))
    (show ContinuousWithinAt (fun p : ℝ × ℝ => L * |p.1 - p.2|)
      (Ioo a b ×ˢ Ioo a b) (s, t) by fun_prop)
  intro p hp
  apply le_of_tendsto ((hconv p.1 hp.1).dist (hconv p.2 hp.2))
  exact hL.mono (fun k hk => hk p.1 ⟨hp.1.1.le, hp.1.2.le⟩
    p.2 ⟨hp.2.1.le, hp.2.2.le⟩)

theorem tendstoUniformlyOn_past_of_time_lipschitz
    {f : ℕ → ℝ × X → Y} {g : ℝ × X → Y} {U : Set X}
    (hconv : ∀ K : Set (ℝ × X), IsCompact K → K ⊆ Iio 0 ×ˢ U →
      TendstoUniformlyOn f g atTop K)
    (hg : ∀ x ∈ U, ContinuousOn (fun t : ℝ => g (t, x)) (Icc (-1) 0))
    (htime : ∀ V : Set X, IsCompact V → V ⊆ U →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ k in atTop,
        ∀ x ∈ V, ∀ s ∈ Icc (-1) 0, ∀ t ∈ Icc (-1) 0,
          dist (f k (s, x)) (f k (t, x)) ≤ L * |s - t|)
    {K : Set (ℝ × X)} (hK : IsCompact K) (hKU : K ⊆ Iic 0 ×ˢ U) :
    TendstoUniformlyOn f g atTop K := by
  let V : Set X := Prod.snd '' K
  have hV : IsCompact V := hK.image continuous_snd
  have hVU : V ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hKU hz).2
  obtain ⟨L, hL, hLip⟩ := htime V hV hVU
  have hgLip (x : X) (hx : x ∈ V) :
      ∀ s ∈ Icc (-1) 0, ∀ t ∈ Icc (-1) 0,
        dist (g (s, x)) (g (t, x)) ≤ L * |s - t| := by
    apply time_lipschitz_of_interior_tendsto (f := fun k t => f k (t, x))
      (by norm_num) (hg x (hVU hx))
    · intro t ht
      exact (hconv {(t, x)} isCompact_singleton
        (singleton_subset_iff.mpr ⟨ht.2, hVU hx⟩)).tendsto_at (mem_singleton _)
    · exact hLip.mono (fun k hk => hk x hx)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ : ℝ := min (1 / 2) (ε / (4 * (L + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδone : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδsmall : 2 * L * δ < ε / 2 := by
    have hd := (le_div_iff₀ (by positivity : 0 < 4 * (L + 1))).mp
      (show δ ≤ ε / (4 * (L + 1)) from min_le_right _ _)
    nlinarith
  let shift : ℝ × X → ℝ × X := fun z => (min z.1 (-δ), z.2)
  have hshift : Continuous shift := (continuous_fst.min continuous_const).prodMk continuous_snd
  have hshiftU : shift '' K ⊆ Iio 0 ×ˢ U := by
    rintro _ ⟨z, hz, rfl⟩
    change min z.1 (-δ) < 0 ∧ z.2 ∈ U
    exact ⟨lt_of_le_of_lt (min_le_right _ _) (by linarith), (hKU hz).2⟩
  have hshiftconv := (Metric.tendstoUniformlyOn_iff.mp
    (hconv (shift '' K) (hK.image hshift) hshiftU)) (ε / 2) (by positivity)
  filter_upwards [hLip, hshiftconv] with k hk hkc z hz
  have hxV : z.2 ∈ V := mem_image_of_mem Prod.snd hz
  have hnear_f : dist (f k z) (f k (shift z)) ≤ L * δ := by
    by_cases hfar : z.1 ≤ -δ
    · simp only [shift, min_eq_left hfar, Prod.mk.eta, dist_self]
      positivity
    · have ht : z.1 ∈ Icc (-1) 0 := ⟨by linarith, (hKU hz).1⟩
      have hs : -δ ∈ Icc (-1) 0 := ⟨by linarith, by linarith⟩
      have hdiff : |z.1 - -δ| ≤ δ := by
        rw [abs_of_nonneg (by linarith)]
        linarith [ht.2]
      simpa only [shift, min_eq_right (le_of_not_ge hfar), Prod.mk.eta] using
        (hk z.2 hxV z.1 ht (-δ) hs).trans (mul_le_mul_of_nonneg_left hdiff hL)
  have hnear_g : dist (g (shift z)) (g z) ≤ L * δ := by
    by_cases hfar : z.1 ≤ -δ
    · simp only [shift, min_eq_left hfar, Prod.mk.eta, dist_self]
      positivity
    · have ht : z.1 ∈ Icc (-1) 0 := ⟨by linarith, (hKU hz).1⟩
      have hs : -δ ∈ Icc (-1) 0 := ⟨by linarith, by linarith⟩
      have hdiff : |z.1 - -δ| ≤ δ := by
        rw [abs_of_nonneg (by linarith)]
        linarith [ht.2]
      simpa only [shift, min_eq_right (le_of_not_ge hfar), Prod.mk.eta, dist_comm] using
        (hgLip z.2 hxV z.1 ht (-δ) hs).trans (mul_le_mul_of_nonneg_left hdiff hL)
  have hinterior := hkc (shift z) (mem_image_of_mem shift hz)
  have htriangle := dist_triangle (f k z) (f k (shift z)) (g z)
  have htriangle' := dist_triangle (f k (shift z)) (g (shift z)) (g z)
  rw [dist_comm] at hinterior ⊢
  linarith

theorem tendstoUniformlyOn_past_of_locallyUniformlyOn
    {f : ℕ → ℝ × X → Y} {g : ℝ × X → Y} {U : Set X}
    (hconv : TendstoLocallyUniformlyOn f g atTop (Iio 0 ×ˢ U))
    (hg : ∀ x ∈ U, ContinuousOn (fun t : ℝ => g (t, x)) (Icc (-1) 0))
    (htime : ∀ V : Set X, IsCompact V → V ⊆ U →
      ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ k in atTop,
        ∀ x ∈ V, ∀ s ∈ Icc (-1) 0, ∀ t ∈ Icc (-1) 0,
          dist (f k (s, x)) (f k (t, x)) ≤ L * |s - t|)
    {K : Set (ℝ × X)} (hK : IsCompact K) (hKU : K ⊆ Iic 0 ×ˢ U) :
    TendstoUniformlyOn f g atTop K := by
  apply tendstoUniformlyOn_past_of_time_lipschitz (g := g) (U := U) _ hg htime hK hKU
  intro C hC hCU
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hC).mp (hconv.mono hCU)

end PoincareConjecture.AncientCompactness

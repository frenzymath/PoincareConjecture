import PoincareConjecture.Proofs.M35.RadialGauge.SourceBounds
import PoincareConjecture.Proofs.M35.RadialGauge.TimeSmoothness
import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelMeasurability
import PoincareConjecture.Proofs.M35.RadialGauge.PicardContraction











set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))


structure PicardSlabControl (T eta : ℝ) (u : ℝ → V → ℝ) : Prop where
  measurable : StronglyMeasurable (fun p : Icc 0 T × V => u p.1.1 p.2)
  smooth : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (u s)
  bounded : ∀ k : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
    ‖iteratedFDeriv ℝ k (u s) x‖ ≤ C
  weighted : ∀ s ∈ Icc 0 T, ∀ x,
    (1 + ‖x‖) * ‖u s x‖ ≤ eta ∧
    (1 + ‖x‖) * ‖fderiv ℝ (u s) x‖ ≤ eta



theorem PicardSlabControl.source
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ} {T eta : ℝ}
    (hu : PicardSlabControl T eta u) (hT : 0 ≤ T)
    (hbm : StronglyMeasurable (fun p : Icc 0 T × V => b p.1.1 p.2))
    (hGm : Measurable (fun p : (Icc 0 T × V) × ℝ => G p.1.1.1 p.1.2 p.2))
    (hbs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (b s))
    (hGs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (fun p : V × ℝ => G s p.1 p.2))
    (hbb : ∀ k : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ k (b s) x‖ ≤ C)
    (hGb : ∀ k : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ k (fun p : V × ℝ => G s p.1 p.2) (x, z)‖ ≤ C) :
    StronglyMeasurable (fun p : Icc 0 T × V =>
      gaugeSource (b p.1.1) (G p.1.1) (u p.1.1) p.2) ∧
    (∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (gaugeSource (b s) (G s) (u s))) ∧
    (∀ k : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ k (gaugeSource (b s) (G s) (u s)) x‖ ≤ C) := by
  have : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  refine ⟨gaugeSource_stronglyMeasurable
    (b := fun s : Icc 0 T => b s.1) (G := fun s : Icc 0 T => G s.1)
    (u := fun s : Icc 0 T => u s.1) hbm hGm hu.measurable
    (fun s => (hu.smooth s.1 s.2).differentiable (by simp)),
    fun s hs => gaugeSource_contDiff (hbs s hs) (hGs s hs) (hu.smooth s hs), ?_⟩
  have hbounded := gaugeSource_uniform_bounded_derivatives
    (b := fun s : Icc 0 T => b s.1) (G := fun s : Icc 0 T => G s.1)
    (u := fun s : Icc 0 T => u s.1)
    (fun s => hbs s.1 s.2) (fun s => hGs s.1 s.2) (fun s => hu.smooth s.1 s.2)
    (fun s x => show |u s.1 x| ≤ eta from by
      have hw := (hu.weighted s.1 s.2 x).1
      rw [Real.norm_eq_abs] at hw
      nlinarith [mul_nonneg (norm_nonneg x) (abs_nonneg (u s.1 x))])
    (fun k => by
      obtain ⟨C, hC⟩ := hbb k
      exact ⟨C, fun s => hC s.1 s.2⟩)
    (fun k => by
      obtain ⟨C, hC⟩ := hu.bounded k
      exact ⟨C, fun s => hC s.1 s.2⟩)
    (fun k => by
      obtain ⟨C, hC⟩ := hGb k
      exact ⟨C, fun s => hC s.1 s.2⟩)
  intro k
  obtain ⟨C, hC⟩ := hbounded k
  exact ⟨C, fun s hs => hC ⟨s, hs⟩⟩




theorem PicardSlabControl.duhamel
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {u : ℝ → V → ℝ}
    {T eta B L C : ℝ} (hu : PicardSlabControl T eta u)
    (hT : 0 ≤ T) (heta : 0 ≤ eta) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hbm : StronglyMeasurable (fun p : Icc 0 T × V => b p.1.1 p.2))
    (hGm : Measurable (fun p : (Icc 0 T × V) × ℝ => G p.1.1.1 p.1.2 p.2))
    (hbs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (b s))
    (hGs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (fun p : V × ℝ => G s p.1 p.2))
    (hbb : ∀ k : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ k (b s) x‖ ≤ C)
    (hGb : ∀ k : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ k (fun p : V × ℝ => G s p.1 p.2) (x, z)‖ ≤ C)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ B)
    (hGzero : ∀ s ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * |G s x 0| ≤ C)
    (hGlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |G s x a - G s x c| ≤ L * |a - c|)
    (hsmall : (B * eta + eta ^ 2 + L * eta + C) * heatC1Gain (n + 1) T ≤ eta) :
    PicardSlabControl T eta (gaugeDuhamel b G u) := by
  obtain ⟨hsm, hss, hsb⟩ := hu.source hT hbm hGm hbs hGs hbb hGb
  let f (s : ℝ) := gaugeSource (b s) (G s) (u s)
  let F := slabSourceExtension T f
  have hFm : StronglyMeasurable (Function.uncurry F) :=
    slabSourceExtension_stronglyMeasurable hsm
  have hFeq (s : ℝ) (hs : s ∈ Icc 0 T) : F s = f s :=
    slabSourceExtension_of_mem hs f
  have hFs (s : ℝ) (hs : s ∈ Icc 0 T) : ContDiff ℝ ∞ (F s) := by
    rw [hFeq s hs]
    exact hss s hs
  have hFb : ∀ k : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ k (F s) x‖ ≤ C := by
    intro k
    obtain ⟨D, hD⟩ := hsb k
    refine ⟨D, fun s hs x => ?_⟩
    rw [hFeq s hs]
    exact hD s hs x
  have heq (s : ℝ) (hs : s ∈ Icc 0 T) : heatDuhamel F s = gaugeDuhamel b G u s :=
    heatDuhamel_slabSourceExtension hs f
  have hsource := gaugeSource_weighted_bound heta hB hL hb hGzero hGlip
    (fun s hs x => by simpa only [Real.norm_eq_abs] using (hu.weighted s hs x).1)
    (fun s hs x => (hu.weighted s hs x).2)
  have hS : 0 ≤ B * eta + eta ^ 2 + L * eta + C := by positivity
  constructor
  · have hm := (heatDuhamel_stronglyMeasurable hFm).comp_measurable
      (g := fun p : Icc 0 T × V => (p.1.1, p.2)) (by fun_prop)
    convert hm using 1
    funext p
    exact congrFun (heq p.1.1 p.1.2).symm p.2
  · intro s hs
    rw [← heq s hs]
    exact (heatDuhamel_contDiff_and_iterated_bound hs.1 hFm
      (fun t ht => hFs t ⟨ht.1, ht.2.trans hs.2⟩) (fun k => by
        obtain ⟨D, hD⟩ := hFb k
        exact ⟨D, fun t ht => hD t ⟨ht.1, ht.2.trans hs.2⟩⟩)).1
  · intro k
    obtain ⟨D, hD⟩ := heatDuhamel_slab_bounded_derivatives hT hFm hFs hFb k
    refine ⟨D, fun s hs x => ?_⟩
    rw [← heq s hs]
    exact hD s hs x
  · intro s hs x
    rw [← heq s hs]
    have hsub : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc le_rfl hs.2
    have h := heatDuhamel_c1_bound hS hs.1 hFm
      (fun t ht => (hFs t (hsub ht)).of_le (by simp))
      (fun t ht => by
        obtain ⟨D, hD⟩ := hFb 1
        exact ⟨D, fun y => by
          simpa only [norm_iteratedFDeriv_one] using hD t (hsub ⟨ht.1, ht.2.le⟩) y⟩)
      (fun t ht y => by
        rw [hFeq t (hsub ht)]
        exact hsource t (hsub ht) y) x
    have hgain : (B * eta + eta ^ 2 + L * eta + C) * heatC1Gain (n + 1) s ≤ eta :=
      (mul_le_mul_of_nonneg_left (heatC1Gain_mono hs.1 hs.2) hS).trans hsmall
    exact ⟨h.1.trans hgain, h.2.trans hgain⟩



theorem gaugePicard_slab_control
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {T eta B L C : ℝ}
    (hT : 0 ≤ T) (heta : 0 ≤ eta) (hB : 0 ≤ B) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hbm : StronglyMeasurable (fun p : Icc 0 T × V => b p.1.1 p.2))
    (hGm : Measurable (fun p : (Icc 0 T × V) × ℝ => G p.1.1.1 p.1.2 p.2))
    (hbs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (b s))
    (hGs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (fun p : V × ℝ => G s p.1 p.2))
    (hbb : ∀ k : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ k (b s) x‖ ≤ C)
    (hGb : ∀ k : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ k (fun p : V × ℝ => G s p.1 p.2) (x, z)‖ ≤ C)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ B)
    (hGzero : ∀ s ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * |G s x 0| ≤ C)
    (hGlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |G s x a - G s x c| ≤ L * |a - c|)
    (hsmall : (B * eta + eta ^ 2 + L * eta + C) * heatC1Gain (n + 1) T ≤ eta) :
    ∀ k, PicardSlabControl T eta (gaugePicard b G k) := by
  intro k
  induction k with
  | zero =>
      constructor
      · exact stronglyMeasurable_const
      · intro s hs
        exact contDiff_const
      · intro k
        exact ⟨0, fun s hs x => by simp [gaugePicard]⟩
      · intro s hs x
        constructor <;> simpa [gaugePicard] using heta
  | succ k ih =>
      exact ih.duhamel hT heta hB hL hC hbm hGm hbs hGs hbb hGb hb hGzero hGlip hsmall

end PoincareConjecture.M35.RadialGauge

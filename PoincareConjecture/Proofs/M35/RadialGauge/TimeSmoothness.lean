import PoincareConjecture.Proofs.M35.RadialGauge.HeatSmoothness
import PoincareConjecture.Proofs.M35.RadialGauge.SpatialMeasurability
import PoincareConjecture.Proofs.M35.RadialGauge.HeatTimeGain











set_option autoImplicit false

open Set Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

universe u

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem finiteIntegral_hasFDerivAt
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : A → V → F} (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ a, ContDiff ℝ ∞ (f a))
    {C D : ℝ} (hC : ∀ a x, ‖f a x‖ ≤ C)
    (hD : ∀ a x, ‖fderiv ℝ (f a) x‖ ≤ D) (x : V) :
    HasFDerivAt (fun y => ∫ a, f a y ∂μ) (∫ a, fderiv ℝ (f a) x ∂μ) x := by
  have hdm := spatial_fderiv_stronglyMeasurable hfm
    (fun a => (hf a).differentiable (by simp))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := univ) (F' := fun y a => fderiv ℝ (f a) y) (bound := fun _ => D) (by simp)
  · exact Eventually.of_forall (fun y =>
      (hfm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  · exact (integrable_const C).mono'
      (hfm.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Eventually.of_forall (fun a => hC a x))
  · exact (hdm.comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · exact Eventually.of_forall (fun a y _ => hD a y)
  · exact integrable_const D
  · exact Eventually.of_forall (fun a y _ =>
      ((hf a).differentiable (by simp) y).hasFDerivAt)

private theorem finiteIntegral_contDiff_nat (k : ℕ)
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : A → V → F} (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hbound : ∀ j : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ j (f a) x‖ ≤ C) :
    ContDiff ℝ k (fun x => ∫ a, f a x ∂μ) := by
  induction k generalizing F with
  | zero =>
      obtain ⟨C, hC⟩ := hbound 0
      apply contDiff_zero.mpr
      apply continuous_of_dominated (bound := fun _ : A => C)
      · intro x
        exact (hfm.comp_measurable
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · intro x
        exact Eventually.of_forall (fun a => by
          simpa only [norm_iteratedFDeriv_zero] using hC a x)
      · exact integrable_const C
      · exact Eventually.of_forall (fun a => (hf a).continuous)
  | succ k ih =>
      have hdf (a : A) := (contDiff_infty_iff_fderiv.mp (hf a)).2
      have hdm := spatial_fderiv_stronglyMeasurable hfm
        (fun a => (hf a).differentiable (by simp))
      have hdb : ∀ j : ℕ, ∃ C : ℝ, ∀ a x,
          ‖iteratedFDeriv ℝ j (fderiv ℝ (f a)) x‖ ≤ C := by
        intro j
        obtain ⟨C, hC⟩ := hbound (j + 1)
        exact ⟨C, fun a x => by simpa only [norm_iteratedFDeriv_fderiv] using hC a x⟩
      obtain ⟨C, hC⟩ := hbound 0
      obtain ⟨D, hD⟩ := hbound 1
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun x => ∫ a, fderiv ℝ (f a) x ∂μ, ih hdm hdf hdb, ?_⟩
      intro x
      exact finiteIntegral_hasFDerivAt μ hfm hf
        (fun a y => by simpa only [norm_iteratedFDeriv_zero] using hC a y)
        (fun a y => by simpa only [norm_iteratedFDeriv_one] using hD a y) x

private theorem finiteIntegral_contDiff
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : A → V → F} (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hbound : ∀ j : ℕ, ∃ C : ℝ, ∀ a x, ‖iteratedFDeriv ℝ j (f a) x‖ ≤ C) :
    ContDiff ℝ ∞ (fun x => ∫ a, f a x ∂μ) :=
  contDiff_infty.mpr (fun k => finiteIntegral_contDiff_nat k μ hfm hf hbound)

private theorem finiteIntegral_iteratedFDeriv_norm_le (k : ℕ)
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : A → V → F} (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hbound : ∀ j : ℕ, ∃ B : ℝ, ∀ a x, ‖iteratedFDeriv ℝ j (f a) x‖ ≤ B)
    {C : ℝ} (hk : ∀ a x, ‖iteratedFDeriv ℝ k (f a) x‖ ≤ C) (x : V) :
    ‖iteratedFDeriv ℝ k (fun y => ∫ a, f a y ∂μ) x‖ ≤ C * μ.real univ := by
  induction k generalizing F with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      apply norm_integral_le_of_norm_le_const
      exact Eventually.of_forall (fun a => by
        simpa only [norm_iteratedFDeriv_zero] using hk a x)
  | succ k ih =>
      have hdf (a : A) := (contDiff_infty_iff_fderiv.mp (hf a)).2
      have hdm := spatial_fderiv_stronglyMeasurable hfm
        (fun a => (hf a).differentiable (by simp))
      have hdb : ∀ j : ℕ, ∃ B : ℝ, ∀ a x,
          ‖iteratedFDeriv ℝ j (fderiv ℝ (f a)) x‖ ≤ B := by
        intro j
        obtain ⟨B, hB⟩ := hbound (j + 1)
        exact ⟨B, fun a x => by simpa only [norm_iteratedFDeriv_fderiv] using hB a x⟩
      obtain ⟨B, hB⟩ := hbound 0
      obtain ⟨D, hD⟩ := hbound 1
      have hderiv : fderiv ℝ (fun y => ∫ a, f a y ∂μ) =
          fun y => ∫ a, fderiv ℝ (f a) y ∂μ := by
        funext y
        exact (finiteIntegral_hasFDerivAt μ hfm hf
          (fun a z => by simpa only [norm_iteratedFDeriv_zero] using hB a z)
          (fun a z => by simpa only [norm_iteratedFDeriv_one] using hD a z) y).fderiv
      rw [← norm_iteratedFDeriv_fderiv, hderiv]
      exact ih hdm hdf hdb
        (fun a y => by simpa only [norm_iteratedFDeriv_fderiv] using hk a y)

private theorem heatFamily_stronglyMeasurable
    {A : Type*} [MeasurableSpace A]
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : A → V → F} (hf : StronglyMeasurable (Function.uncurry f))
    {elapsed : A → ℝ} (he : Measurable elapsed) :
    StronglyMeasurable (fun p : A × V => heatAverage (elapsed p.1) (f p.1) p.2) := by
  have h : StronglyMeasurable (fun q : (A × V) × V =>
      f q.1.1 (q.1.2 + Real.sqrt (2 * elapsed q.1.1) • q.2)) :=
    hf.comp_measurable (g := fun q : (A × V) × V =>
      (q.1.1, q.1.2 + Real.sqrt (2 * elapsed q.1.1) • q.2)) (by fun_prop)
  exact h.integral_prod_right'




theorem heatDuhamel_contDiff_and_iterated_bound
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → V → F} {t : ℝ} (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ ∞ (f s))
    (hbound : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 t, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ C) :
    ContDiff ℝ ∞ (heatDuhamel f t) ∧
      ∀ (k : ℕ) (C : ℝ), (∀ s ∈ Icc 0 t, ∀ x, ‖iteratedFDeriv ℝ k (f s) x‖ ≤ C) →
        ∀ x, ‖iteratedFDeriv ℝ k (heatDuhamel f t) x‖ ≤ C * t := by
  let S := Ioc (0 : ℝ) t
  let μ : Measure S := Measure.comap Subtype.val volume
  have hμ : μ univ = volume (Ioc (0 : ℝ) t) := by
    rw [show μ = Measure.comap Subtype.val volume from rfl,
      comap_subtype_coe_apply measurableSet_Ioc]
    rw [Set.image_univ, Subtype.range_coe]
  have : IsFiniteMeasure μ := ⟨by rw [hμ]; simp⟩
  have hμreal : μ.real univ = t := by
    rw [measureReal_def, hμ, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal ht]
  let H (s : S) (x : V) := heatAverage (t - s.1) (f s.1) x
  have hHs (s : S) : s.1 ∈ Icc 0 t := ⟨s.2.1.le, s.2.2⟩
  have hHm : StronglyMeasurable (Function.uncurry H) :=
    heatFamily_stronglyMeasurable (f := fun s : S => f s.1)
      (by
        change StronglyMeasurable (fun p : S × V => f p.1.1 p.2)
        exact hfm.comp_measurable (g := fun p : S × V => (p.1.1, p.2)) (by fun_prop))
      (show Measurable (fun s : S => t - s.1) by fun_prop)
  have hHsmooth (s : S) : ContDiff ℝ ∞ (H s) :=
    heatAverage_contDiff (hf s.1 (hHs s)) (fun j => by
      obtain ⟨C, hC⟩ := hbound j
      exact ⟨C, hC s.1 (hHs s)⟩) _
  have hHb : ∀ j : ℕ, ∃ C : ℝ, ∀ s x, ‖iteratedFDeriv ℝ j (H s) x‖ ≤ C := by
    intro j
    obtain ⟨C, hC⟩ := hbound j
    refine ⟨C, fun s x => ?_⟩
    exact heatAverage_iteratedFDeriv_norm_le j (hf s.1 (hHs s)) (fun k => by
      obtain ⟨B, hB⟩ := hbound k
      exact ⟨B, hB s.1 (hHs s)⟩) (hC s.1 (hHs s)) _ x
  have heq : heatDuhamel f t = fun x => ∫ s, H s x ∂μ := by
    funext x
    rw [heatDuhamel, intervalIntegral.integral_of_le ht]
    exact (integral_subtype_comap measurableSet_Ioc
      (fun s => heatAverage (t - s) (f s) x)).symm
  rw [heq]
  refine ⟨finiteIntegral_contDiff μ hHm hHsmooth hHb, ?_⟩
  intro k C hC x
  rw [← hμreal]
  apply finiteIntegral_iteratedFDeriv_norm_le k μ hHm hHsmooth hHb
  intro s y
  exact heatAverage_iteratedFDeriv_norm_le k (hf s.1 (hHs s)) (fun j => by
    obtain ⟨B, hB⟩ := hbound j
    exact ⟨B, hB s.1 (hHs s)⟩) (hC s.1 (hHs s)) _ y



theorem heatDuhamel_slab_bounded_derivatives
    {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → V → F} {T : ℝ} (hT : 0 ≤ T)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (f s))
    (hbound : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (f s) x‖ ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (heatDuhamel f t) x‖ ≤ C := by
  intro j
  obtain ⟨C, hC⟩ := hbound j
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, hT⟩ 0)
  refine ⟨C * T, fun t ht x => ?_⟩
  have h := (heatDuhamel_contDiff_and_iterated_bound ht.1 hfm
    (fun s hs => hf s ⟨hs.1, hs.2.trans ht.2⟩) (fun k => by
      obtain ⟨B, hB⟩ := hbound k
      exact ⟨B, fun s hs => hB s ⟨hs.1, hs.2.trans ht.2⟩⟩)).2 j C
      (fun s hs => hC s ⟨hs.1, hs.2.trans ht.2⟩) x
  exact h.trans (mul_le_mul_of_nonneg_left ht.2 hC0)

end PoincareConjecture.M35.RadialGauge

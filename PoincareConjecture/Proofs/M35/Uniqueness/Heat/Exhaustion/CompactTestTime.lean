import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.DefectHeatTestBound
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

theorem compact_family_integral_hasDerivAt
    {a b t : ℝ} (ht : t ∈ Ioo a b) {E : Set V} (hE : IsCompact E)
    (f d : ℝ → V → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ))
    (hd : ContinuousOn (Function.uncurry d) (Icc a b ×ˢ univ))
    (hf0 : ∀ s x, x ∉ E → f s x = 0)
    (hd0 : ∀ s ∈ Ioo a b, ∀ x ∉ E, d s x = 0)
    (hder : ∀ s ∈ Ioo a b, ∀ x ∈ E, HasDerivAt (fun r => f r x) (d s x) s) :
    HasDerivAt (fun s => ∫ x, f s x) (∫ x, d t x) t := by
  have hfc (s : ℝ) (hs : s ∈ Icc a b) : Continuous (f s) := by
    rw [← continuousOn_univ]
    exact hf.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ _ => ⟨hs, mem_univ _⟩)
  have hdc (s : ℝ) (hs : s ∈ Icc a b) : Continuous (d s) := by
    rw [← continuousOn_univ]
    exact hd.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ _ => ⟨hs, mem_univ _⟩)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hE).exists_bound_of_continuousOn
    (hd.mono (prod_mono Subset.rfl (subset_univ E)))
  have hm : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (f s) (volume.restrict E) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (hfc s ⟨hs.1.le, hs.2.le⟩).aestronglyMeasurable
  have hb : ∀ᵐ x ∂volume.restrict E, ∀ s ∈ Ioo a b, ‖d s x‖ ≤ M := by
    filter_upwards [ae_restrict_mem hE.measurableSet] with x hx
    exact fun s hs => hM (s, x) ⟨⟨hs.1.le, hs.2.le⟩, hx⟩
  have hh : ∀ᵐ x ∂volume.restrict E, ∀ s ∈ Ioo a b,
      HasDerivAt (fun r => f r x) (d s x) s := by
    filter_upwards [ae_restrict_mem hE.measurableSet] with x hx
    exact fun s hs => hder s hs x hx
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo a b) (bound := fun _ : V => M) (Ioo_mem_nhds ht.1 ht.2) hm
    ((hfc t ⟨ht.1.le, ht.2.le⟩).continuousOn.integrableOn_compact hE)
    (hdc t ⟨ht.1.le, ht.2.le⟩).aestronglyMeasurable hb
    (integrableOn_const hE.measure_ne_top) hh).2
  have he (s : ℝ) : (∫ x in E, f s x) = ∫ x, f s x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hf0 s)
  have he' : (∫ x in E, d t x) = ∫ x, d t x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hd0 t ht)
  simpa only [he, he'] using h

theorem compact_test_time_hasDerivAt
    {a b t : ℝ} (ht : t ∈ Ioo a b) {f : ℝ → V → ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Ioo a b ×ˢ univ))
    {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    HasDerivAt (fun s => ∫ x, φ x * f s x)
      (∫ x, φ x * fderiv ℝ (Function.uncurry f) (t, x) (1, 0)) t := by
  let a' := (a + t) / 2
  let b' := (t + b) / 2
  have ht' : t ∈ Ioo a' b' := by dsimp [a', b']; constructor <;> linarith [ht.1, ht.2]
  have hsub : Icc a' b' ⊆ Ioo a b := by
    intro s hs
    dsimp [a', b'] at hs
    constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
  let d := fun s x => fderiv ℝ (Function.uncurry f) (s, x) (1, 0)
  have hd : ContDiffOn ℝ ∞ (Function.uncurry d) (Ioo a b ×ˢ univ) :=
    (hf.fderiv_of_isOpen (isOpen_Ioo.prod isOpen_univ) (by simp)).clm_apply contDiffOn_const
  have hpc : ContinuousOn (fun p : ℝ × V => φ p.2) (Icc a' b' ×ˢ univ) :=
    (hφ.comp continuous_snd).continuousOn
  apply compact_family_integral_hasDerivAt ht' hc
    (fun s x => φ x * f s x) (fun s x => φ x * d s x)
    (hpc.mul (hf.continuousOn.mono (prod_mono hsub Subset.rfl)))
    (hpc.mul (hd.continuousOn.mono (prod_mono hsub Subset.rfl)))
    (fun _ _ hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
    (fun _ _ _ hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul])
  intro s hs x _hx
  have hs' : s ∈ Ioo a b := hsub ⟨hs.1.le, hs.2.le⟩
  have h := ((hf (s, x) ⟨hs', mem_univ x⟩).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hs', mem_univ x⟩)
      ).differentiableAt (by simp)
  exact (h.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))).const_mul (φ x)

theorem abs_sub_le_of_closed_interval_derivative_bound
    {f d : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (d t) t)
    (hb : ∀ t ∈ Ioo a b, |d t| ≤ C) :
    |f b - f a| ≤ C * (b - a) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope f d hab hf hd
  have he' : f b - f a = d t * (b - a) := (eq_div_iff (sub_ne_zero.mpr hab.ne')).mp he |>.symm
  rw [he', abs_mul, abs_of_pos (sub_pos.mpr hab)]
  exact mul_le_mul_of_nonneg_right (hb t ht) (sub_nonneg.mpr hab.le)

end PoincareConjecture.M35.Uniqueness.Heat

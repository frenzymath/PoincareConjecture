import PoincareConjecture.Definitions.Ch19.AnnulusComparison
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture

theorem m64AnnulusForwardDerivativeBound.frequently_slope_lt
    {f : ℝ → ℝ} {q t R : ℝ}
    (hf : AnnulusForwardDerivativeBound f q t) (hR : q < R) :
    ∃ᶠ z in 𝓝[>] t, slope f t z < R := by
  obtain ⟨delta, hdelta, hbound⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp (hf ((R - q) / 2) (by linarith))
  have hsmall : ∀ᶠ z in 𝓝[>] t, z ∈ Ioo t (t + delta) :=
    Ioo_mem_nhdsGT (lt_add_of_pos_right t hdelta)
  apply (hsmall.mono ?_).frequently
  intro z hz
  have h := hbound (show z - t ∈ Ioo (0 : ℝ) delta by
    constructor <;> linarith [hz.1, hz.2])
  change (f (t + (z - t)) - f t) / (z - t) ≤ q + (R - q) / 2 at h
  rw [show t + (z - t) = z by ring] at h
  rw [slope_def_field]
  linarith

theorem m64AnnulusForwardDerivativeBound.linear_comparison
    {f q : ℝ → ℝ} {s t C : ℝ} (hst : s ≤ t)
    (hf : ContinuousOn f (Icc s t))
    (hforward : ∀ x ∈ Ico s t, AnnulusForwardDerivativeBound f (q x) x)
    (hq : ∀ x ∈ Ico s t, q x ≤ C) :
    f t ≤ f s + C * (t - s) := by
  have hderiv (x : ℝ) : HasDerivAt (fun y => f s + C * (y - s)) C x := by
    simpa using (((hasDerivAt_id x).sub_const s).const_mul C).const_add (f s)
  apply image_le_of_liminf_slope_right_le_deriv_boundary hf
    (B := fun x => f s + C * (x - s)) (B' := fun _ => C)
    (by simp) (by fun_prop) (fun x _ => (hderiv x).hasDerivWithinAt) ?_ ⟨hst, le_rfl⟩
  intro x hx R hR
  exact m64AnnulusForwardDerivativeBound.frequently_slope_lt
    (hforward x hx) ((hq x hx).trans_lt hR)

theorem m64AnnulusForwardDerivativeBound.at_initial
    {f q : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hq : ContinuousWithinAt q (Icc a b) a)
    (hforward : ∀ t ∈ Ioo a b, AnnulusForwardDerivativeBound f (q t) t) :
    AnnulusForwardDerivativeBound f (q a) a := by
  intro eta heta
  have hrate : ∀ᶠ x in 𝓝[Icc a b] a, q x < q a + eta :=
    hq (Iio_mem_nhds (by linarith))
  have hright : ∀ᶠ x in 𝓝[>] a, q x < q a + eta :=
    nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ⟨le_rfl, hab⟩) hrate
  obtain ⟨c, hc, hqc⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hab).mp hright
  have hbound (z : ℝ) (hz : z ∈ Ioo a c) :
      f z ≤ f a + (q a + eta) * (z - a) := by
    have hzab : z < b := hz.2.trans_le hc.2
    have hsub : Ioo a z ⊆ Icc a b := fun x hx =>
      ⟨hx.1.le, hx.2.le.trans hzab.le⟩
    have haclosure : a ∈ closure (Ioo a z) := by
      rw [closure_Ioo hz.1.ne]
      exact ⟨le_rfl, hz.1.le⟩
    apply ContinuousWithinAt.closure_le haclosure continuousWithinAt_const
      (((hf a ⟨le_rfl, hab.le⟩).mono hsub).add
        (continuousWithinAt_const.mul
          (continuousWithinAt_const.sub continuousWithinAt_id)))
    intro s hs
    apply m64AnnulusForwardDerivativeBound.linear_comparison hs.2.le
      (hf.mono (Icc_subset_Icc hs.1.le hzab.le))
    · intro x hx
      exact hforward x ⟨hs.1.trans_le hx.1, hx.2.trans hzab⟩
    · intro x hx
      exact (hqc ⟨hs.1.trans_le hx.1, hx.2.trans hz.2⟩).le
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo 0 (c - a) :=
    Ioo_mem_nhdsGT (sub_pos.mpr hc.1)
  filter_upwards [hsmall] with h hh
  have h := hbound (a + h) (by constructor <;> linarith [hh.1, hh.2])
  apply (div_le_iff₀ hh.1).mpr
  nlinarith

theorem m64AnnulusForwardDerivativeBound.on_Ico_of_on_Ioo
    {f q : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hforward : ∀ t ∈ Ioo a b, AnnulusForwardDerivativeBound f (q t) t) :
    ∀ t ∈ Ico a b, AnnulusForwardDerivativeBound f (q t) t := by
  intro t ht
  rcases ht.1.eq_or_lt with hta | hta
  · subst t
    exact m64AnnulusForwardDerivativeBound.at_initial ht.2 hf
      (hq a ⟨le_rfl, ht.2.le⟩) hforward
  · exact hforward t ⟨hta, ht.2⟩

end PoincareConjecture

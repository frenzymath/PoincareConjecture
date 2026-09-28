
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Transport
import Mathlib.Analysis.Calculus.ContDiff.Deriv










noncomputable section

open Set Filter
open scoped Topology NNReal ContDiff

namespace PoincareConjecture.RicciFlow.Frame

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

private lemma exists_bound {A : ℝ → V →L[ℝ] V} {a b : ℝ}
    (hA : ContinuousOn A (Icc a b)) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K := by
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hA.nnnorm
  exact ⟨K, fun t ht => hK (mem_image_of_mem _ ht)⟩


def compactTransport (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) : ℝ → V →L[ℝ] V :=
  transportCurveOn A hab hA (exists_bound hA).choose_spec

@[simp] theorem compactTransport_left
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) :
    compactTransport A hab hA a = ContinuousLinearMap.id ℝ V :=
  transportCurveOn_left A hab hA _

theorem compactTransport_hasDerivWithinAt
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (compactTransport A hab hA)
      ((A t).comp (compactTransport A hab hA t)) (Icc a b) t :=
  transportCurveOn_hasDerivWithinAt A hab hA _ ht

theorem compactTransport_eqOn_of_le
    (A : ℝ → V →L[ℝ] V) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hA : ContinuousOn A (Icc a b)) (hA' : ContinuousOn A (Icc a c)) :
    EqOn (compactTransport A hab hA)
      (compactTransport A (hab.trans hbc) hA') (Icc a b) := by
  apply transportCurveOn_eqOn A hab hA _ (compactTransport_left A _ _)
  intro t ht
  exact (compactTransport_hasDerivWithinAt A (hab.trans hbc) hA'
    ⟨ht.1, ht.2.trans hbc⟩).mono (Icc_subset_Icc le_rfl hbc)


def transportIco (A : ℝ → V →L[ℝ] V) (a b : ℝ)
    (hA : ContinuousOn A (Ico a b)) (t : ℝ) : V →L[ℝ] V :=
  if ht : t ∈ Ico a b then
    compactTransport A ht.1 (hA.mono (Icc_subset_Ico_right ht.2)) t
  else ContinuousLinearMap.id ℝ V

theorem transportIco_eq_compactTransport
    (A : ℝ → V →L[ℝ] V) {a b c : ℝ}
    (hA : ContinuousOn A (Ico a b)) (hac : a ≤ c) (hcb : c < b) :
    EqOn (transportIco A a b hA)
      (compactTransport A hac (hA.mono (Icc_subset_Ico_right hcb))) (Icc a c) := by
  intro t ht
  have htb : t < b := ht.2.trans_lt hcb
  simp only [transportIco, dif_pos (show t ∈ Ico a b from ⟨ht.1, htb⟩)]
  exact compactTransport_eqOn_of_le A ht.1 ht.2 _ _ ⟨ht.1, le_rfl⟩

@[simp] theorem transportIco_left
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hA : ContinuousOn A (Ico a b)) :
    transportIco A a b hA a = ContinuousLinearMap.id ℝ V := by
  simp only [transportIco, dif_pos (show a ∈ Ico a b from ⟨le_rfl, hab⟩),
    compactTransport_left]

theorem transportIco_hasDerivWithinAt
    (A : ℝ → V →L[ℝ] V) {a b : ℝ}
    (hA : ContinuousOn A (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt (transportIco A a b hA)
      ((A t).comp (transportIco A a b hA t)) (Ico a b) t := by
  obtain ⟨c, htc, hcb⟩ := exists_between ht.2
  have hac : a ≤ c := ht.1.trans htc.le
  have heq := transportIco_eq_compactTransport A hA hac hcb
  have hset : (Icc a c : Set ℝ) =ᶠ[𝓝 t] Ico a b := by
    filter_upwards [isOpen_Iio.mem_nhds htc] with s hs
    exact propext ⟨fun h => ⟨h.1, h.2.trans_lt hcb⟩, fun h => ⟨h.1, hs.le⟩⟩
  have hd := compactTransport_hasDerivWithinAt A hac
    (hA.mono (Icc_subset_Ico_right hcb)) (show t ∈ Icc a c from ⟨ht.1, htc.le⟩)
  rw [heq ⟨ht.1, htc.le⟩]
  apply (hd.congr_set hset).congr_of_eventuallyEq
  · filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds htc),
      self_mem_nhdsWithin] with s hs hs'
    exact heq ⟨hs'.1, hs.le⟩
  · exact heq ⟨ht.1, htc.le⟩

theorem transportIco_continuousOn
    (A : ℝ → V →L[ℝ] V) {a b : ℝ}
    (hA : ContinuousOn A (Ico a b)) :
    ContinuousOn (transportIco A a b hA) (Ico a b) :=
  fun _ ht => (transportIco_hasDerivWithinAt A hA ht).continuousWithinAt

theorem transportIco_bijective
    (A : ℝ → V →L[ℝ] V) {a b : ℝ}
    (hA : ContinuousOn A (Ico a b)) {t : ℝ} (ht : t ∈ Ico a b) :
    Function.Bijective (transportIco A a b hA t) := by
  simp only [transportIco, dif_pos ht, compactTransport]
  exact transportCurveOn_bijective A ht.1 _ _ ⟨ht.1, le_rfl⟩


theorem transportIco_contDiffOn
    (A : ℝ → V →L[ℝ] V) {a b : ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ico a b)) :
    ContDiffOn ℝ ∞ (transportIco A a b hA.continuousOn) (Ico a b) := by
  have hder := fun {t : ℝ} (ht : t ∈ Ico a b) =>
    transportIco_hasDerivWithinAt A hA.continuousOn ht
  have hdiff : DifferentiableOn ℝ
      (transportIco A a b hA.continuousOn) (Ico a b) :=
    fun _ ht => (hder ht).differentiableWithinAt
  have heq : EqOn (derivWithin (transportIco A a b hA.continuousOn) (Ico a b))
      (fun t => (A t).comp (transportIco A a b hA.continuousOn t)) (Ico a b) :=
    fun t ht => (hder ht).derivWithin (uniqueDiffOn_Ico a b t ht)
  rw [contDiffOn_infty]
  intro k
  induction k with
  | zero => exact contDiffOn_zero.mpr (transportIco_continuousOn A hA.continuousOn)
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by simp]
    apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Ico a b)).mpr
    refine ⟨hdiff, by simp, ?_⟩
    refine (hA.of_le (show (k : WithTop ℕ∞) ≤ ∞ from
      WithTop.coe_le_coe.mpr le_top)).clm_comp ih |>.congr ?_
    intro t ht
    exact heq ht


theorem transportIco_pairing
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hA : ContinuousOn A (Ico a b))
    (g r : ℝ → V →L[ℝ] V →L[ℝ] ℝ)
    (hg : ∀ t ∈ Ico a b, HasDerivWithinAt g ((-2 : ℝ) • r t) (Ico a b) t)
    (hleft : ∀ t ∈ Ico a b, ∀ v w, g t (A t v) w = r t v w)
    (hright : ∀ t ∈ Ico a b, ∀ v w, g t v (A t w) = r t v w)
    {t : ℝ} (ht : t ∈ Ico a b) (v w : V) :
    g t (transportIco A a b hA t v) (transportIco A a b hA t w) = g a v w := by
  let Φ := transportIco A a b hA
  let f := fun s => g s (Φ s v) (Φ s w)
  have hzero : ∀ s ∈ Ico a b, HasDerivWithinAt f 0 (Ico a b) s := by
    intro s hs
    have hd := transportIco_hasDerivWithinAt A hA hs
    have hv := hd.clm_apply (hasDerivWithinAt_const s (Ico a b) v)
    have hw := hd.clm_apply (hasDerivWithinAt_const s (Ico a b) w)
    have hp := ((hg s hs).clm_apply hv).clm_apply hw
    apply hp.congr_deriv
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, map_zero, add_zero]
    rw [hleft s hs, hright s hs]
    ring
  obtain ⟨c, htc, hcb⟩ := exists_between ht.2
  have hac : a < c := ht.1.trans_lt htc
  have hsub : Icc a c ⊆ Ico a b := Icc_subset_Ico_right hcb
  have hdiff : DifferentiableOn ℝ f (Icc a c) :=
    fun s hs => ((hzero s (hsub hs)).mono hsub).differentiableWithinAt
  have hderiv : ∀ s ∈ Ico a c, derivWithin f (Icc a c) s = 0 :=
    fun s hs => ((hzero s (hsub ⟨hs.1, hs.2.le⟩)).mono hsub).derivWithin
      (uniqueDiffOn_Icc hac s ⟨hs.1, hs.2.le⟩)
  have hconst := constant_of_derivWithin_zero hdiff hderiv t ⟨ht.1, htc.le⟩
  simpa only [f, Φ, transportIco_left A hab hA, ContinuousLinearMap.id_apply] using hconst

end PoincareConjecture.RicciFlow.Frame

import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem joint_contDiffOn_one_of_partials
    {J : Set ℝ} (hJ : IsOpen J) {u H : ℝ → E → F}
    (hspace : ∀ t ∈ J, Differentiable ℝ (u t))
    (htime : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => u s x) (H t x) t)
    (hH : ContinuousOn (Function.uncurry H) (J ×ˢ univ))
    (hdu : ContinuousOn (fun p : ℝ × E => fderiv ℝ (u p.1) p.2) (J ×ˢ univ)) :
    ContDiffOn ℝ 1 (Function.uncurry u) (J ×ˢ univ) := by
  let timeMap : F →L[ℝ] (ℝ →L[ℝ] F) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ F).toContinuousLinearEquiv.toContinuousLinearMap
  let D (p : ℝ × E) := (timeMap (H p.1 p.2)).coprod (fderiv ℝ (u p.1) p.2)
  have hW : IsOpen (J ×ˢ (univ : Set E)) := hJ.prod isOpen_univ
  have htc : ContinuousOn (fun p : ℝ × E => timeMap (H p.1 p.2)) (J ×ˢ univ) :=
    timeMap.continuous.comp_continuousOn hH
  have hDc : ContinuousOn D (J ×ˢ univ) := by
    have h := (htc.clm_comp (continuousOn_const (c := ContinuousLinearMap.fst ℝ ℝ E))).add
      (hdu.clm_comp (continuousOn_const (c := ContinuousLinearMap.snd ℝ ℝ E)))
    exact h.congr (fun p _ =>
      (ContinuousLinearMap.comp_fst_add_comp_snd _ _).symm)
  have hd {p : ℝ × E} (hp : p ∈ J ×ˢ (univ : Set E)) :
      HasFDerivAt (Function.uncurry u) (D p) p := by
    exact (hasStrictFDerivAt_uncurry_coprod
      (f := u) (f₁ := fun t x => timeMap (H t x))
      (f₂ := fun t x => fderiv ℝ (u t) x)
      (by
        filter_upwards [hW.mem_nhds hp] with q hq
        exact (htime q.1 hq.1 q.2).hasFDerivAt)
      (by
        filter_upwards [hW.mem_nhds hp] with q hq
        exact (hspace q.1 hq.1 q.2).hasFDerivAt)
      (htc.continuousAt (hW.mem_nhds hp))
      (hdu.continuousAt (hW.mem_nhds hp))).hasFDerivAt
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hW).mpr
  refine ⟨fun p hp => (hd hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  apply contDiffOn_zero.mpr
  exact hDc.congr (fun p hp => (hd hp).fderiv)

theorem joint_contDiffOn_one_of_slab_partials
    {u H : ℝ → E → F} {a b : ℝ}
    (hspace : ∀ t ∈ Icc a b, Differentiable ℝ (u t))
    (htime : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => u s x) (H t x) t)
    (hH : Continuous (fun p : Icc a b × E => H p.1.1 p.2))
    (hdu : Continuous (fun p : Icc a b × E => fderiv ℝ (u p.1.1) p.2)) :
    ContDiffOn ℝ 1 (Function.uncurry u) (Ioo a b ×ˢ univ) := by
  apply joint_contDiffOn_one_of_partials isOpen_Ioo
    (fun t ht => hspace t ⟨ht.1.le, ht.2.le⟩) htime
  · apply continuousOn_iff_continuous_domRestrict.mpr
    exact hH.comp (f := fun p : Ioo a b ×ˢ (univ : Set E) =>
      ((⟨p.1.1, p.2.1.1.le, p.2.1.2.le⟩ : Icc a b), p.1.2)) (by fun_prop)
  · apply continuousOn_iff_continuous_domRestrict.mpr
    exact hdu.comp (f := fun p : Ioo a b ×ˢ (univ : Set E) =>
      ((⟨p.1.1, p.2.1.1.le, p.2.1.2.le⟩ : Icc a b), p.1.2)) (by fun_prop)

end PoincareConjecture.M35.RadialGauge

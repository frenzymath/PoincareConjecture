import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic

open Set Filter Asymptotics
open scoped Topology Convex

namespace Poincare

private theorem isLittleO_sub_sub_fderiv
    {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E} {v w : α → E} {l : Filter α}
    (hv : Tendsto v l (𝓝 u)) (hw : Tendsto w l (𝓝 u))
    (s : Set E) (seg : ∀ᶠ q in l, [w q -[ℝ] v q] ⊆ s)
    {f : α → E → F} {f' : α → E → E →L[ℝ] F}
    (hf : ∀ᶠ p in l ×ˢ 𝓝[s] u,
      HasFDerivWithinAt (f p.1) (f' p.1 p.2) s p.2)
    {φ : E →L[ℝ] F} (hc : Tendsto (Function.uncurry f') (l ×ˢ 𝓝[s] u) (𝓝 φ)) :
    (fun q => f q (v q) - f q (w q) - φ (v q - w q)) =o[l]
      (fun q => v q - w q) := by
  rw [isLittleO_iff]
  intro ε hε
  have hd : ∀ᶠ q in l, ∀ z ∈ [w q -[ℝ] v q],
      HasFDerivWithinAt (f q) (f' q z) s z :=
    hf.segment_of_prod_nhdsWithin hw hv seg
  have hb : ∀ᶠ q in l, ∀ z ∈ [w q -[ℝ] v q], ‖f' q z - φ‖ < ε := by
    simp_rw [Metric.tendsto_nhds, dist_eq_norm_sub] at hc
    exact (hc ε hε).segment_of_prod_nhdsWithin hw hv seg
  filter_upwards [seg, hd, hb] with q hseg hd hb
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (hd z hz).mono hseg) (fun z hz => (hb z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

variable {P Q V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem hasFDerivWithinAt_prod_of_continuous_partial
    {f : P × Q → V} {U : Set P} {T : Set Q} (hT : Convex ℝ T)
    {p : P × Q} (hp : p ∈ U ×ˢ T) {Dx : P →L[ℝ] V}
    {Dt : P × Q → Q →L[ℝ] V}
    (hx : HasFDerivAt (fun x => f (x, p.2)) Dx p.1)
    (ht : ∀ q ∈ U ×ˢ T,
      HasFDerivWithinAt (fun t => f (q.1, t)) (Dt q) T q.2)
    (hDt : ContinuousWithinAt Dt (U ×ˢ T) p) :
    HasFDerivWithinAt f (Dx.coprod (Dt p)) (U ×ˢ T) p := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  have hfst : Tendsto (fun q : P × Q => q.1) (𝓝[U ×ˢ T] p) (𝓝 p.1) :=
    continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hsnd : Tendsto (fun q : P × Q => q.2) (𝓝[U ×ˢ T] p) (𝓝 p.2) :=
    continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmap : Tendsto (fun q : (P × Q) × Q => (q.1.1, q.2))
      ((𝓝[U ×ˢ T] p) ×ˢ 𝓝[T] p.2) (𝓝[U ×ˢ T] p) := by
    rw [nhdsWithin_prod_eq] at *
    exact (tendsto_fst.comp tendsto_fst).prodMk tendsto_snd
  have htime :
      (fun q => f (q.1, q.2) - f (q.1, p.2) - Dt p (q.2 - p.2))
        =o[𝓝[U ×ˢ T] p] (fun q => q.2 - p.2) := by
    apply isLittleO_sub_sub_fderiv hsnd tendsto_const_nhds T
      (f := fun q t => f (q.1, t)) (f' := fun q t => Dt (q.1, t))
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact hT.segment_subset hp.2 hq.2
    · exact hmap.eventually (eventually_mem_nhdsWithin.mono ht)
    · exact (show Tendsto Dt (𝓝[U ×ˢ T] p) (𝓝 (Dt p)) from hDt).comp hmap
  have hspace :
      (fun q : P × Q => f (q.1, p.2) - f p - Dx (q.1 - p.1))
        =o[𝓝[U ×ˢ T] p] (fun q => q.1 - p.1) := by
    simpa [Function.comp_def] using (hasFDerivAt_iff_isLittleO.mp hx).comp_tendsto hfst
  have hspace' :
      (fun q : P × Q => f (q.1, p.2) - f p - Dx (q.1 - p.1))
        =o[𝓝[U ×ˢ T] p] (fun q => q - p) :=
    hspace.trans_isBigO (isBigO_of_le _ (fun q => norm_fst_le (q - p)))
  have htime' :
      (fun q : P × Q => f (q.1, q.2) - f (q.1, p.2) - Dt p (q.2 - p.2))
        =o[𝓝[U ×ˢ T] p] (fun q => q - p) :=
    htime.trans_isBigO (isBigO_of_le _ (fun q => norm_snd_le (q - p)))
  simpa [ContinuousLinearMap.coprod_apply, Prod.fst_sub, Prod.snd_sub,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hspace'.add htime'

theorem hasFDerivWithinAt_prod_Ico_of_continuous_partial
    {f : P × ℝ → V} {U : Set P} {a b : ℝ}
    {p : P × ℝ} (hp : p ∈ U ×ˢ Ico a b) {Dx : P →L[ℝ] V}
    {Dt : P × ℝ → V}
    (hx : HasFDerivAt (fun x => f (x, p.2)) Dx p.1)
    (ht : ∀ q ∈ U ×ˢ Ico a b,
      HasDerivWithinAt (fun t => f (q.1, t)) (Dt q) (Ico a b) q.2)
    (hDt : ContinuousWithinAt Dt (U ×ˢ Ico a b) p) :
    HasFDerivWithinAt f
      (Dx.coprod (ContinuousLinearMap.toSpanSingleton ℝ (Dt p))) (U ×ˢ Ico a b) p := by
  apply hasFDerivWithinAt_prod_of_continuous_partial (convex_Ico a b) hp hx
    (fun q hq => (ht q hq).hasFDerivWithinAt)
  exact ContinuousLinearMap.toSpanSingletonCLE.continuous.continuousAt.comp_continuousWithinAt hDt

end Poincare

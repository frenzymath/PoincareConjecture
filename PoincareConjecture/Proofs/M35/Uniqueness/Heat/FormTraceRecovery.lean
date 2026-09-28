import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SmoothFormRecovery
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.WeakValuePath









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem tested_value_derivative_adjoint (I : V →L[ℝ] H)
    (P : ℝ → V →L[ℝ] V) (L : ℝ → V →L[ℝ] H) {B : ℝ}
    {v : ℝ → V} {U : ℝ → H}
    (hU : ∀ t ∈ Ioo 0 B, ContDiffAt ℝ ∞ U t)
    (hweak : ∀ᵐ t ∂timeMeasure B, ∀ w : V,
      HasDerivWithinAt (fun s => inner ℝ (I w) (U s))
        (inner ℝ (I w) (L t (v t)) - inner ℝ w (P t (v t))) (Icc 0 B) t) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 B),
      I.adjoint (deriv U t) = I.adjoint (L t (v t)) - P t (v t) := by
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hweak,
    ae_restrict_mem measurableSet_Ioo] with t hw ht
  apply ext_inner_left ℝ
  intro w
  rw [inner_sub_right, I.adjoint_inner_right, I.adjoint_inner_right]
  have hdU := (hU t ht).differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hd := (innerSL ℝ (I w)).hasFDerivAt.comp_hasDerivAt t hdU.hasDerivAt
  exact hd.unique ((hw w).hasDerivAt (Icc_mem_nhds ht.1 ht.2))

theorem recover_smooth_form_trace (I : V →L[ℝ] H)
    (P : ℝ → V →L[ℝ] V) (L : ℝ → V →L[ℝ] H) {B c C : ℝ}
    (hc : 0 < c) (hLb : ∀ t ∈ Ioo 0 B, ‖L t‖ ≤ C)
    (hP : ∀ t ∈ Ioo 0 B, ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ u (P t u) + ‖I u‖ ^ 2)
    (hPc : ContDiffOn ℝ ∞ P (Ioo 0 B)) (hLc : ContDiffOn ℝ ∞ L (Ioo 0 B))
    {v : ℝ → V} {U : ℝ → H}
    (hU : ∀ t ∈ Ioo 0 B, ContDiffAt ℝ ∞ U t)
    (hgraph : ∀ᵐ t ∂timeMeasure B, I (v t) = U t)
    (hweak : ∀ᵐ t ∂timeMeasure B, ∀ w : V,
      HasDerivWithinAt (fun s => inner ℝ (I w) (U s))
        (inner ℝ (I w) (L t (v t)) - inner ℝ w (P t (v t))) (Icc 0 B) t) :
    (∀ t ∈ Ioo 0 B, ContDiffAt ℝ ∞ (ellipticFormRecovery I P L c C U) t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 B), ellipticFormRecovery I P L c C U t = v t) ∧
      (∀ t ∈ Ioo 0 B, I (ellipticFormRecovery I P L c C U t) = U t) ∧
      (∀ t ∈ Ioo 0 B,
        I.adjoint (deriv U t) = I.adjoint (L t (ellipticFormRecovery I P L c C U t)) -
          P t (ellipticFormRecovery I P L c C U t)) := by
  have hvc : ∀ t ∈ Ioo 0 B, ContDiffAt ℝ ∞ (ellipticFormRecovery I P L c C U) t := by
    intro t ht
    exact contDiffAt_ellipticFormRecovery I P L hc (hLb t ht) (hP t ht)
      (hPc.contDiffAt (isOpen_Ioo.mem_nhds ht))
      (hLc.contDiffAt (isOpen_Ioo.mem_nhds ht)) (hU t ht)
  have hae : ∀ᵐ t ∂volume.restrict (Ioo 0 B), ellipticFormRecovery I P L c C U t = v t := by
    filter_upwards [tested_value_derivative_adjoint I P L hU hweak,
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hgraph,
      ae_restrict_mem measurableSet_Ioo] with t he hg ht
    exact ellipticFormRecovery_eq I P L hc (hLb t ht) (hP t ht) hg he
  have hga : ∀ᵐ t ∂volume.restrict (Ioo 0 B), I (ellipticFormRecovery I P L c C U t) = U t := by
    filter_upwards [hae, ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hgraph]
      with t he hg
    rw [he, hg]
  have hgc : ∀ t ∈ Ioo 0 B, I (ellipticFormRecovery I P L c C U t) = U t :=
    Measure.eqOn_open_of_ae_eq hga isOpen_Ioo
      (I.continuous.comp_continuousOn (fun t ht => (hvc t ht).continuousAt.continuousWithinAt))
      (fun t ht => (hU t ht).continuousAt.continuousWithinAt)
  exact ⟨hvc, hae, hgc, fun t ht =>
    ellipticFormRecovery_equation I P L hc (hLb t ht) (hP t ht) (hgc t ht)⟩

theorem exists_smooth_form_trace (I : V →L[ℝ] H)
    (P : ℝ → V →L[ℝ] V) (L : ℝ → V →L[ℝ] H) {B c C : ℝ}
    (hc : 0 < c) (hLb : ∀ t ∈ Ioo 0 B, ‖L t‖ ≤ C)
    (hP : ∀ t ∈ Ioo 0 B, ∀ u, c * ‖u‖ ^ 2 ≤ inner ℝ u (P t u) + ‖I u‖ ^ 2)
    (hPc : ContDiffOn ℝ ∞ P (Ioo 0 B)) (hLc : ContDiffOn ℝ ∞ L (Ioo 0 B))
    {v : ℝ → V} {U : ℝ → H}
    (hU : ∀ t ∈ Ioo 0 B, ContDiffAt ℝ ∞ U t)
    (hgraph : ∀ᵐ t ∂timeMeasure B, I (v t) = U t)
    (hweak : ∀ᵐ t ∂timeMeasure B, ∀ w : V,
      HasDerivWithinAt (fun s => inner ℝ (I w) (U s))
        (inner ℝ (I w) (L t (v t)) - inner ℝ w (P t (v t))) (Icc 0 B) t) :
    ∃ w : ℝ → V, (∀ t ∈ Ioo 0 B, ContDiffAt ℝ ∞ w t) ∧
      (∀ᵐ t ∂volume.restrict (Ioo 0 B), w t = v t) ∧
      (∀ t ∈ Ioo 0 B, I (w t) = U t) ∧
      (∀ t ∈ Ioo 0 B, ∀ z : V, inner ℝ (I z) (deriv U t) =
        inner ℝ (I z) (L t (w t)) - inner ℝ z (P t (w t))) := by
  obtain ⟨hws, hwa, hwg, hwe⟩ := recover_smooth_form_trace I P L hc hLb hP hPc hLc hU hgraph hweak
  refine ⟨ellipticFormRecovery I P L c C U, hws, hwa, hwg, ?_⟩
  intro t ht z
  have hp := congrArg (fun q => inner ℝ z q) (hwe t ht)
  simpa only [inner_sub_right, ContinuousLinearMap.adjoint_inner_right] using hp

end PoincareConjecture.M35.Uniqueness.Heat

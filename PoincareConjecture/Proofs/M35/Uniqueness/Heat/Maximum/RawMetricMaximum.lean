import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.ActualTimeChain
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.EntropyZero
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawAbsoluteFormTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open ValueInitial

variable {n m : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Z" => EuclideanSpace ℝ (Fin m)

def dirichletValueField (K : Set V) :
    PiLp 2 (fun _ : Fin m => dirichletValue K) →L[ℝ] Lp Z 2 (volume : Measure V) :=
  scalarFieldsLp.comp (finiteHilbertMap (dirichletValue K).subtypeL)

theorem dirichletValueField_form (K : Set V)
    (w : PiLp 2 (fun _ : Fin m => dirichletForm K)) :
    dirichletValueField K (finiteHilbertMap (dirichletInclusion K) w) =
      dirichletFieldValue K w := rfl

theorem raw_compact_vector_heat_metric_maximum {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {K : Set V} (hK : IsCompact K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hη0 : ∀ x, 0 ≤ η x) (hηK : ∀ x ∈ K, η x = 1)
    (hR : ∀ t ∈ Icc a b, ∀ x, 0 ≤ (F.connection t).scalarCurvature x)
    {u₀ : PiLp 2 (fun _ : Fin n => dirichletValue K)}
    {v : ℝ → PiLp 2 (fun _ : Fin n => dirichletForm K)}
    {U : ℝ → PiLp 2 (fun _ : Fin n => dirichletValue K)}
    (hsol : PrincipalValueHeat K
      (fun r => rawCutoffPrincipalCoefficient (F.metric r) η hη)
      (fun r => rawLowerFormOperator (F.connection r) hK.isClosed η hη) a (b - a) u₀ v U)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hinit : ∀ᵐ x ∂volume, (F.metric a).inner x
      (dirichletValueField K u₀ x) (dirichletValueField K u₀ x) ≤ Q) :
    ∀ t ∈ Icc a b, ∀ᵐ x ∂volume, x ∈ K → (F.metric t).inner x
      (dirichletValueField K (U (t - a)) x) (dirichletValueField K (U (t - a)) x) ≤ Q := by
  obtain ⟨W, hW, hgraph, heq⟩ :=
    exists_raw_compact_absolute_form_trace F hab hJ hK η hη hηK hsol
  let Y (s : ℝ) := dirichletValueField K (U (s - a))
  have hY : ContinuousOn Y (Icc a b) := by
    apply (dirichletValueField K).continuous.comp_continuousOn
    apply hsol.2.2.1.comp (continuous_id.sub continuous_const).continuousOn
    intro s hs
    change s - a ∈ Icc 0 (b - a)
    constructor <;> linarith only [hs.1, hs.2]
  have hY0 : Y a = dirichletValueField K u₀ := by
    simp only [Y, sub_self, hsol.2.1]
  have hfield (s : ℝ) (hs : s ∈ Ioo a b) : dirichletFieldValue K (W s) = Y s :=
    (dirichletValueField_form K (W s)).symm.trans (congrArg (dirichletValueField K) (hgraph s hs))
  have hdec : ∀ t ∈ Ioo a b, ∃ d : ℝ, d ≤ 0 ∧ HasDerivAt
      (fun s => fieldIntegral (metricEntropyPotential (F.metric s) η Q) (Y s)) d t := by
    intro t ht
    obtain ⟨d, hd, hder⟩ := raw_form_entropy_hasDerivAt_nonpos F hJ ht hK η hη hηK hQ
      (hR t ⟨ht.1.le, ht.2.le⟩) W ((hW t ht).differentiableAt (by simp)) (heq t ht)
    refine ⟨d, hd, hder.congr_of_eventuallyEq ?_⟩
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact congrArg (fieldIntegral (metricEntropyPotential (F.metric s) η Q)) (hfield s hs).symm
  have hzero := metricEntropy_trace_eq_zero F hab.le hJ η.smooth' hη hη0 hQ Y hY
    (by simpa only [hY0] using hinit) hdec
  intro t ht
  exact metric_norm_bound_of_entropy_zero (F.metric t) η.smooth' hη hη0 hηK hQ (Y t)
    (hzero t ht)

end PoincareConjecture.M35.Uniqueness.Heat

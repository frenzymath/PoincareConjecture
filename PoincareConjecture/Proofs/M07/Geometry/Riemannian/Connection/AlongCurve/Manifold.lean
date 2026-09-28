import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Transport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Manifold
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.ConnectionAlongCurve

open CoordinateExponential ConnectionVariation

theorem contDiffAt_operator_of_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    {P : ℝ → E →L[ℝ] F} {t : ℝ}
    (h : ∀ v, ContDiffAt ℝ ∞ (fun s => P s v) t) : ContDiffAt ℝ ∞ P t := by
  let d := Module.finrank ℝ E
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[ℝ] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  have he : P = fun s => e₂.symm (e₂ (P s)) := by
    funext s
    exact (e₂.symm_apply_apply _).symm
  rw [he]
  exact e₂.symm.contDiff.contDiffAt.comp t (contDiffAt_pi.mpr fun i => h _)

private theorem hasDerivAt_operator_of_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P : ℝ → E →L[ℝ] F} {P' : E →L[ℝ] F} {t : ℝ}
    (hP : DifferentiableAt ℝ P t)
    (h : ∀ v, HasDerivAt (fun s => P s v) (P' v) t) : HasDerivAt P P' t := by
  have heq : deriv P t = P' := by
    ext v
    have hd := hP.hasDerivAt.clm_apply (hasDerivAt_const t v)
    simpa only [map_zero, add_zero] using hd.unique (h v)
  exact heq ▸ hP.hasDerivAt

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


def chartField (q : ℝ → M) (a : M)
    (V : (t : ℝ) → TangentSpace (𝓡 n) (q t)) : ℝ → EuclideanSpace ℝ (Fin n) :=
  fun t => mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q t) (V t)

theorem contDiffAt_chart_curve {q : ℝ → M} {a : M} {t : ℝ}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (ha : q t ∈ (extChartAt (𝓡 n) a).source) :
    ContDiffAt ℝ ∞ ((extChartAt (𝓡 n) a) ∘ q) t := by
  apply contMDiffAt_iff_contDiffAt.mp
  exact (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using ha)).comp t hq

theorem contDiffAt_chartField_change {q : ℝ → M}
    {V : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {a b : M} {t : ℝ}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (ha : q t ∈ (extChartAt (𝓡 n) a).source)
    (hb : q t ∈ (extChartAt (𝓡 n) b).source)
    (hV : ContDiffAt ℝ ∞ (chartField q a V) t) :
    ContDiffAt ℝ ∞ (chartField q b V) t := by
  let ca := extChartAt (𝓡 n) a
  let cb := extChartAt (𝓡 n) b
  let f := cb ∘ ca.symm
  have hf : ContDiffAt ℝ ∞ f (ca (q t)) := by
    apply contMDiffAt_iff_contDiffAt.mp
    apply (contMDiffAt_extChartAt' (by
      simpa only [ca.left_inv ha, extChartAt_source] using hb)).comp
    exact (contMDiffOn_extChartAt_symm a).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) a).mem_nhds (ca.map_source ha))
  have hrep : chartField q b V =ᶠ[𝓝 t]
      (fun s => fderiv ℝ f (ca (q s)) (chartField q a V s)) := by
    filter_upwards [hq.continuousAt.preimage_mem_nhds
      (inter_mem ((isOpen_extChartAt_source a).mem_nhds ha)
        ((isOpen_extChartAt_source b).mem_nhds hb))] with s hs
    exact (chart_transition_tangent a b hs.1 hs.2 (V s)).symm
  have hs := ((hf.fderiv_right (m := ∞) (by simp)).comp t
    (contDiffAt_chart_curve hq ha)).clm_apply hV
  exact hs.congr_of_eventuallyEq hrep



theorem contDiffAt_chartField_covDeriv (g : RiemannianMetric n M)
    {q : ℝ → M} {V : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {I : Set ℝ}
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hV : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField q (q t) V) t)
    {t : ℝ} (ht : t ∈ I) {a : M} (ha : q t ∈ (extChartAt (𝓡 n) a).source) :
    ContDiffAt ℝ ∞ (chartField q a (manifoldCovDerivAlong g q V 1)) t := by
  have hqt := hq.contMDiffAt (hI.mem_nhds ht)
  have hnear := inter_mem (hI.mem_nhds ht) (hqt.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source a).mem_nhds ha))
  have heq : chartField q a (manifoldCovDerivAlong g q V 1) =ᶠ[𝓝 t]
      covDerivAlong (christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm))
        ((extChartAt (𝓡 n) a) ∘ q) (chartField q a V) 1 := by
    filter_upwards [hnear] with s hs
    have hqs := hq.contMDiffAt (hI.mem_nhds hs.1)
    have hVs := contDiffAt_chartField_change hqs (mem_extChartAt_source _) hs.2 (hV s hs.1)
    exact manifoldCovDerivAlong_in_chart g a hs.2 hqs.continuousAt
      ((contDiffAt_chart_curve hqs hs.2).differentiableAt (by simp))
      (hVs.differentiableAt (by simp)) 1
  have hB := (g.contDiffOn_chartCoefficients a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds ((extChartAt (𝓡 n) a).map_source ha))
  have hΓ := contDiffAt_christoffelBilinear hB
    (g.isInvertible_chartCoefficients a ((extChartAt (𝓡 n) a).map_source ha))
  have hd := contDiffAt_covDerivAlong (u := (extChartAt (𝓡 n) a) ∘ q) (p := t)
    hΓ (contDiffAt_chart_curve hqt ha)
    (contDiffAt_chartField_change hqt (mem_extChartAt_source _) ha (hV t ht)) (1 : ℝ)
  exact hd.congr_of_eventuallyEq heq



theorem hasDerivAt_chartField (g : RiemannianMetric n M)
    {q : ℝ → M} {V : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {t : ℝ} {a : M}
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (ha : q t ∈ (extChartAt (𝓡 n) a).source)
    (hV : DifferentiableAt ℝ (chartField q a V) t) :
    HasDerivAt (chartField q a V)
      (chartField q a (manifoldCovDerivAlong g q V 1) t +
        parallelCoefficient (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
          ((extChartAt (𝓡 n) a) ∘ q) t (chartField q a V t)) t := by
  have heq := manifoldCovDerivAlong_in_chart g a ha hq.continuousAt
    ((contDiffAt_chart_curve hq ha).differentiableAt (by simp)) hV (1 : ℝ)
  have hd : chartField q a (manifoldCovDerivAlong g q V 1) t +
      parallelCoefficient (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
        ((extChartAt (𝓡 n) a) ∘ q) t (chartField q a V t) = deriv (chartField q a V) t := by
    change mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q t)
      (manifoldCovDerivAlong g q V 1 t) + _ = _
    rw [heq]
    change deriv (chartField q a V) t + _ + _ = _
    simp only [parallelCoefficient, neg_apply, chartField]
    exact add_neg_cancel_right _ _
  rw [hd]
  exact hV.hasDerivAt

private def ParallelAt (g : RiemannianMetric n M) (q : ℝ → M)
    (V : (t : ℝ) → TangentSpace (𝓡 n) (q t)) (t : ℝ) : Prop :=
  ∃ a : M, q t ∈ (extChartAt (𝓡 n) a).source ∧
    ContDiffAt ℝ ∞ (chartField q a V) t ∧
    HasDerivAt (chartField q a V)
      (parallelCoefficient (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
        ((extChartAt (𝓡 n) a) ∘ q) t (chartField q a V t)) t

private theorem ParallelAt.covDeriv_eq_zero {g : RiemannianMetric n M}
    {q : ℝ → M} {V : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {t : ℝ}
    (h : ParallelAt g q V t) (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t) :
    manifoldCovDerivAlong g q V 1 t = 0 := by
  obtain ⟨a, ha, hV, hd⟩ := h
  apply (isInvertible_mfderiv_extChartAt ha).injective
  rw [map_zero, manifoldCovDerivAlong_in_chart g a ha hq.continuousAt
    ((contDiffAt_chart_curve hq ha).differentiableAt (by simp))
    (hV.differentiableAt (by simp))]
  change deriv (chartField q a V) t + _ = 0
  rw [hd.deriv]
  simp [parallelCoefficient, chartField]

private theorem ParallelAt.in_chart {g : RiemannianMetric n M}
    {q : ℝ → M} {V : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {t : ℝ}
    (h : ParallelAt g q V t) (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    {a : M} (ha : q t ∈ (extChartAt (𝓡 n) a).source) :
    ContDiffAt ℝ ∞ (chartField q a V) t ∧
    HasDerivAt (chartField q a V)
      (parallelCoefficient (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
        ((extChartAt (𝓡 n) a) ∘ q) t (chartField q a V t)) t := by
  have hz := h.covDeriv_eq_zero hq
  obtain ⟨b, hb, hV, _⟩ := h
  have hVa := contDiffAt_chartField_change hq hb ha hV
  refine ⟨hVa, ?_⟩
  have heq := manifoldCovDerivAlong_in_chart g a ha hq.continuousAt
    ((contDiffAt_chart_curve hq ha).differentiableAt (by simp))
    (hVa.differentiableAt (by simp)) (1 : ℝ)
  rw [hz, map_zero] at heq
  have hd : deriv (chartField q a V) t =
      parallelCoefficient (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
        ((extChartAt (𝓡 n) a) ∘ q) t (chartField q a V t) := by
    change 0 = deriv (chartField q a V) t + _ at heq
    simpa [parallelCoefficient, chartField] using eq_neg_of_add_eq_zero_left heq.symm
  exact hd ▸ (hVa.differentiableAt (by simp)).hasDerivAt

private theorem ParallelAt.congr {g : RiemannianMetric n M}
    {q : ℝ → M} {V W : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (h : ParallelAt g q V t) (heq : V =ᶠ[𝓝 t] W) : ParallelAt g q W t := by
  obtain ⟨a, ha, hV, hd⟩ := h
  have hrep : chartField q a V =ᶠ[𝓝 t] chartField q a W :=
    heq.mono fun s hs => congrArg (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q s)) hs
  refine ⟨a, ha, hV.congr_of_eventuallyEq hrep.symm, ?_⟩
  rw [← hrep.self_of_nhds]
  exact hd.congr_of_eventuallyEq hrep.symm

set_option maxHeartbeats 2000000 in
private theorem exists_parallel_in_chart (g : RiemannianMetric n M)
    {q : ℝ → M} {I : Set ℝ} (hI : IsOpen I)
    (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    {a : M} {l r : ℝ} (hlr : l < r) (hsub : Icc l r ⊆ I)
    (hsrc : ∀ t ∈ Icc l r, q t ∈ (extChartAt (𝓡 n) a).source)
    {s : ℝ} (hs : s ∈ Ioo l r) (v : TangentSpace (𝓡 n) (q s)) :
    ∃ V : ℝ → EuclideanSpace ℝ (Fin n), V s = v ∧
      ∀ t ∈ Ioo l r, ParallelAt g q V t := by
  let c := extChartAt (𝓡 n) a
  let B := g.pullbackCoefficients c.symm
  let J := I ∩ q ⁻¹' c.source
  have hJo : IsOpen J :=
    hq.continuousOn.isOpen_inter_preimage hI (isOpen_extChartAt_source a)
  have hJsub : Icc l r ⊆ J := fun t ht => ⟨hsub ht, hsrc t ht⟩
  have hqc : ContDiffOn ℝ ∞ (c ∘ q) J := by
    intro t ht
    exact (contDiffAt_chart_curve (hq.contMDiffAt (hI.mem_nhds ht.1)) ht.2).contDiffWithinAt
  obtain ⟨P, _, hPs, hPi, hP, _⟩ := exists_parallel_transport (B := B) (q := c ∘ q) hlr
    (isOpen_extChartAt_target a) (g.contDiffOn_chartCoefficients a)
    (fun _ ht => g.isInvertible_chartCoefficients a ht)
    (fun _ _ _ _ => g.symm _ _ _) hJo hqc (fun _ ht => c.map_source ht.2) hJsub
  let z := (P s).inverse (mfderiv (𝓡 n) (𝓡 n) c (q s) v)
  let V : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun t => (mfderiv (𝓡 n) (𝓡 n) c (q t)).inverse (P t z)
  have hread {t : ℝ} (ht : t ∈ Ioo l r) : chartField q a V t = P t z :=
    (isInvertible_mfderiv_extChartAt (hsrc t ⟨ht.1.le, ht.2.le⟩)).self_apply_inverse _
  refine ⟨V, ?_, ?_⟩
  · dsimp only [V, z]
    rw [(hPi s ⟨hs.1.le, hs.2.le⟩).self_apply_inverse,
      (isInvertible_mfderiv_extChartAt (hsrc s ⟨hs.1.le, hs.2.le⟩)).inverse_apply_self]
  · intro t ht
    have hPt := hPs.contDiffAt (Icc_mem_nhds ht.1 ht.2)
    have hrep : chartField q a V =ᶠ[𝓝 t] (fun u => P u z) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
      exact hread hu
    refine ⟨a, hsrc t ⟨ht.1.le, ht.2.le⟩,
      (hPt.clm_apply contDiffAt_const).congr_of_eventuallyEq hrep, ?_⟩
    rw [hread ht]
    have hd := ((hP t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).clm_apply (hasDerivAt_const t z)
    simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero]
      using hd.congr_of_eventuallyEq hrep

theorem chartField_inner (g : RiemannianMetric n M) {q : ℝ → M}
    (V W : (t : ℝ) → TangentSpace (𝓡 n) (q t)) {a : M} {t : ℝ}
    (ha : q t ∈ (extChartAt (𝓡 n) a).source) :
    g.pullbackCoefficients (extChartAt (𝓡 n) a).symm (extChartAt (𝓡 n) a (q t))
      (chartField q a V t) (chartField q a W t) = g.inner (q t) (V t) (W t) := by
  have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓡 n) ha
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hi
  have hv : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm
      (extChartAt (𝓡 n) a (q t)) (chartField q a V t) = V t :=
    congrArg (fun L => L (V t)) hi
  have hw : mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm
      (extChartAt (𝓡 n) a (q t)) (chartField q a W t) = W t :=
    congrArg (fun L => L (W t)) hi
  change g.inner _ _ _ = _
  erw [hv, hw]
  exact congrArg (fun z => g.inner z (V t) (W t)) ((extChartAt (𝓡 n) a).left_inv ha)

private theorem ParallelAt.inner_deriv {g : RiemannianMetric n M} {q : ℝ → M}
    {V W : (t : ℝ) → TangentSpace (𝓡 n) (q t)} {t : ℝ}
    (hV : ParallelAt g q V t) (hW : ParallelAt g q W t)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t) :
    HasDerivAt (fun s => g.inner (q s) (V s) (W s)) 0 t := by
  let a := q t
  have ha : q t ∈ (extChartAt (𝓡 n) a).source := mem_extChartAt_source _
  have hnear := hq.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source a).mem_nhds ha)
  have hVa := (hV.in_chart hq ha).2
  have hWa := (hW.in_chart hq ha).2
  have hB := (g.contDiffOn_chartCoefficients a).contDiffAt
    ((isOpen_extChartAt_target a).mem_nhds ((extChartAt (𝓡 n) a).map_source ha))
  have hd := hasDerivWithinAt_metric_parallel (S := univ)
    (hB.differentiableAt (by simp))
    (g.isInvertible_chartCoefficients a ((extChartAt (𝓡 n) a).map_source ha))
    (Eventually.of_forall fun _ _ _ => g.symm _ _ _)
    ((contDiffAt_chart_curve hq ha).differentiableAt (by simp))
    (by simpa only [parallelCoefficient, neg_apply, christoffelBilinear_apply]
      using hVa.hasDerivWithinAt (s := univ))
    (by simpa only [parallelCoefficient, neg_apply, christoffelBilinear_apply]
      using hWa.hasDerivWithinAt (s := univ))
  apply hd.hasDerivAt (by simp) |>.congr_of_eventuallyEq
  filter_upwards [hnear] with s hs
  exact (chartField_inner g V W hs).symm

private theorem ParallelAt.sub {g : RiemannianMetric n M} {q : ℝ → M}
    {V W : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hV : ParallelAt g q V t) (hW : ParallelAt g q W t)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t) :
    ParallelAt g q (V - W) t := by
  let a := q t
  have ha : q t ∈ (extChartAt (𝓡 n) a).source := mem_extChartAt_source _
  have hVa := hV.in_chart hq ha
  have hWa := hW.in_chart hq ha
  have hrep : chartField q a (V - W) = chartField q a V - chartField q a W := by
    funext s
    exact map_sub (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q s)) (V s) (W s)
  refine ⟨a, ha, ?_, ?_⟩
  · rw [hrep]
    exact hVa.1.sub hWa.1
  · rw [hrep, Pi.sub_apply, map_sub]
    exact hVa.2.sub hWa.2

private theorem parallel_pairing_eq {g : RiemannianMetric n M} {q : ℝ → M}
    {V W : ℝ → EuclideanSpace ℝ (Fin n)} {a b : ℝ} (hab : a < b)
    (hq : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hV : ∀ t ∈ Icc a b, ParallelAt g q V t)
    (hW : ∀ t ∈ Icc a b, ParallelAt g q W t) {t : ℝ} (ht : t ∈ Icc a b) :
    g.inner (q t) (V t) (W t) = g.inner (q a) (V a) (W a) := by
  have hd := fun s hs => ((hV s hs).inner_deriv (hW s hs) (hq s hs)).hasDerivWithinAt
    (s := Icc a b)
  exact constant_of_derivWithin_zero (fun s hs => (hd s hs).differentiableWithinAt)
    (fun s hs => (hd s ⟨hs.1, hs.2.le⟩).derivWithin
      (uniqueDiffOn_Icc hab s ⟨hs.1, hs.2.le⟩)) t ht

private theorem parallel_unique {g : RiemannianMetric n M} {q : ℝ → M}
    {V W : ℝ → EuclideanSpace ℝ (Fin n)} {a b s : ℝ}
    (hq : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hV : ∀ t ∈ Icc a b, ParallelAt g q V t)
    (hW : ∀ t ∈ Icc a b, ParallelAt g q W t)
    (hs : s ∈ Icc a b) (heq : V s = W s) : EqOn V W (Icc a b) := by
  intro t ht
  rcases lt_or_eq_of_le (hs.1.trans hs.2) with hab | rfl
  · have hd := fun u hu => (hV u hu).sub (hW u hu) (hq u hu)
    have hp := (parallel_pairing_eq hab hq hd hd ht).trans
      (parallel_pairing_eq hab hq hd hd hs).symm
    simp only [Pi.sub_apply, heq, sub_self, map_zero] at hp
    by_contra hne
    exact (ne_of_gt (g.pos (q t) (V t - W t) (sub_ne_zero.mpr hne))) hp
  · have ht' : t = a := le_antisymm ht.2 ht.1
    have hs' : s = a := le_antisymm hs.2 hs.1
    simpa only [ht', hs'] using heq

private theorem ParallelAt.const_smul {g : RiemannianMetric n M} {q : ℝ → M}
    {V : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hV : ParallelAt g q V t) (r : ℝ) : ParallelAt g q (fun s => r • V s) t := by
  obtain ⟨a, ha, hs, hd⟩ := hV
  have hrep : chartField q a (fun s => r • V s) = fun s => r • chartField q a V s := by
    funext s
    exact map_smul (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (q s)) r (V s)
  refine ⟨a, ha, ?_, ?_⟩
  · rw [hrep]
    exact hs.const_smul r
  · rw [hrep, map_smul]
    exact hd.const_smul r

private theorem ParallelAt.zero (g : RiemannianMetric n M) {q : ℝ → M} {t : ℝ} :
    ParallelAt g q (fun _ => 0) t := by
  have hrep : chartField (n := n) q (q t) (fun _ => 0) = fun _ => 0 := by
    funext s
    exact map_zero _
  refine ⟨q t, mem_extChartAt_source _, ?_, ?_⟩
  · rw [hrep]
    exact contDiffAt_const
  · rw [hrep, map_zero]
    exact hasDerivAt_const t _

private theorem ParallelAt.add {g : RiemannianMetric n M} {q : ℝ → M}
    {V W : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hV : ParallelAt g q V t) (hW : ParallelAt g q W t)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t) : ParallelAt g q (V + W) t := by
  have heq : V - (fun s => (-1 : ℝ) • W s) = V + W := by
    funext s
    simp
  rw [← heq]
  exact hV.sub (hW.const_smul (-1)) hq

private theorem ParallelAt.sum {ι : Type*} {g : RiemannianMetric n M} {q : ℝ → M}
    {V : ι → ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ} (S : Finset ι)
    (hV : ∀ i ∈ S, ParallelAt g q (V i) t)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t) :
    ParallelAt g q (∑ i ∈ S, V i) t := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact ParallelAt.zero g (q := q) (t := t)
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hV i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hV j (Finset.mem_insert_of_mem hj))) hq

set_option maxHeartbeats 2000000 in
private theorem exists_parallel_on_Icc (g : RiemannianMetric n M)
    {q : ℝ → M} {I : Set ℝ} {a b : ℝ} (hab : a < b)
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hsub : Icc a b ⊆ I) (v : TangentSpace (𝓡 n) (q a)) :
    ∃ V : ℝ → EuclideanSpace ℝ (Fin n), V a = v ∧
      ∀ t ∈ Icc a b, ParallelAt g q V t := by
  classical
  have hqt := fun t ht => hq.contMDiffAt (hI.mem_nhds (hsub (show t ∈ Icc a b from ht)))
  have hchart : ∀ t ∈ Icc a b, ∃ ε > (0 : ℝ),
      Icc (t - ε) (t + ε) ⊆ I ∧
      ∀ s ∈ Icc (t - ε) (t + ε), q s ∈ (extChartAt (𝓡 n) (q t)).source := by
    intro t ht
    have hn := inter_mem (hI.mem_nhds (hsub ht))
      ((hqt t ht).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := 𝓡 n) (q t)).mem_nhds
          (mem_extChartAt_source (I := 𝓡 n) _)))
    obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hn
    have hm : Icc (t - ε / 2) (t + ε / 2) ⊆ Metric.ball t ε := by
      intro s hs
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    exact ⟨ε / 2, by positivity, fun s hs => (he (hm hs)).1,
      fun s hs => (he (hm hs)).2⟩
  let S : Set ℝ := {r | r ∈ Ioc a b ∧ ∃ V : ℝ → EuclideanSpace ℝ (Fin n),
    V a = v ∧ ∀ t ∈ Icc a r, ParallelAt g q V t}
  obtain ⟨ε₀, hε₀, hI₀, hsrc₀⟩ := hchart a ⟨le_rfl, hab.le⟩
  obtain ⟨V₀, hV₀a, hV₀⟩ := exists_parallel_in_chart g hI hq
    (by linarith : a - ε₀ < a + ε₀) hI₀ hsrc₀ (s := a) ⟨by linarith, by linarith⟩ v
  have hstart : min b (a + ε₀ / 2) ∈ S := by
    refine ⟨⟨lt_min hab (by linarith), min_le_left _ _⟩, V₀, hV₀a, ?_⟩
    intro t ht
    apply hV₀ t
    constructor
    · linarith [ht.1]
    · have := min_le_right b (a + ε₀ / 2)
      linarith [ht.2]
  have hSne : S.Nonempty := ⟨_, hstart⟩
  have hSbdd : BddAbove S := ⟨b, fun _ hr => hr.1.2⟩
  let c := sSup S
  have hac : a < c := (lt_min hab (by linarith : a < a + ε₀ / 2)).trans_le
    (le_csSup hSbdd hstart)
  have hcb : c ≤ b := csSup_le hSne fun _ hr => hr.1.2
  obtain ⟨ε, hε, hIc, hsrcc⟩ := hchart c ⟨hac.le, hcb⟩
  obtain ⟨d, hdS, hld⟩ := exists_lt_of_lt_csSup hSne
    (show max a (c - ε / 2) < sSup S from max_lt hac (by dsimp [c]; linarith))
  have hdc : d ≤ c := le_csSup hSbdd hdS
  obtain ⟨hdab, V, hVa, hV⟩ := hdS
  obtain ⟨W, hWd, hW⟩ := exists_parallel_in_chart g hI hq
    (by linarith : c - ε < c + ε) hIc hsrcc (s := d)
      ⟨by linarith [le_max_right a (c - ε / 2)], by linarith⟩ (V d)
  let l := max a (c - ε / 2)
  have hal : a ≤ l := le_max_left _ _
  have heq : EqOn V W (Icc l d) := by
    apply parallel_unique (s := d)
      (fun t ht => hqt t ⟨hal.trans ht.1, ht.2.trans hdab.2⟩)
      (fun t ht => hV t ⟨hal.trans ht.1, ht.2⟩)
      (fun t ht => hW t ⟨by dsimp [l] at ht; linarith [le_max_right a (c - ε / 2), ht.1],
        by linarith [ht.2]⟩) ⟨hld.le, le_rfl⟩ hWd.symm
  let U : ℝ → EuclideanSpace ℝ (Fin n) := fun t => if t ≤ d then V t else W t
  let r := min b (c + ε / 2)
  have hcr : c ≤ r := le_min hcb (by linarith)
  have hrS : r ∈ S := by
    refine ⟨⟨hac.trans_le hcr, min_le_left _ _⟩, U, ?_, ?_⟩
    · simp only [U, if_pos hdab.1.le, hVa]
    · intro t ht
      by_cases htd : t < d
      · apply (hV t ⟨ht.1, htd.le⟩).congr
        filter_upwards [isOpen_Iio.mem_nhds htd] with s hs
        simp only [U, if_pos (show s < d from hs).le]
      · have hdt : d ≤ t := le_of_not_gt htd
        apply (hW t ⟨by linarith [le_max_right a (c - ε / 2)],
          by have := min_le_right b (c + ε / 2); linarith [ht.2]⟩).congr
        filter_upwards [isOpen_Ioi.mem_nhds (hld.trans_le hdt)] with s hs
        dsimp only [U]
        split_ifs with hsd
        · exact (heq ⟨hs.le, hsd⟩).symm
        · rfl
  have hrc : r ≤ c := le_csSup hSbdd hrS
  have hbc : b ≤ c := by
    by_contra h
    have : c < r := lt_min (lt_of_not_ge h) (by linarith)
    exact (not_lt_of_ge hrc) this
  have hrb : r = b := le_antisymm (min_le_left _ _) (hbc.trans hcr)
  rw [hrb] at hrS
  exact hrS.2

private theorem exists_parallel_operators (g : RiemannianMetric n M)
    {q : ℝ → M} {I : Set ℝ} {a b : ℝ} (hab : a < b)
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hsub : Icc a b ⊆ I) :
    ∃ P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      P a = ContinuousLinearMap.id ℝ _ ∧
      (∀ t ∈ Icc a b, (P t).IsInvertible) ∧
      (∀ t ∈ Icc a b, ∀ u, ParallelAt g q (fun s => P s u) t) ∧
      ∀ t ∈ Icc a b, ∀ u v, g.inner (q t) (P t u) (P t v) = g.inner (q a) u v := by
  classical
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  choose V hVa hV using fun i => exists_parallel_on_Icc g hab hI hq hsub (e i)
  let P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun t => (e.constr ℝ (fun i => V i t)).toContinuousLinearMap
  have hPa : P a = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.coe_injective
    change e.constr ℝ (fun i => V i a) = LinearMap.id
    simp only [hVa]
    exact e.constr_self ℝ LinearMap.id
  have hp : ∀ t ∈ Icc a b, ∀ u, ParallelAt g q (fun s => P s u) t := by
    intro t ht u
    have heq : (fun s => P s u) = ∑ i : Fin n, fun s => e.repr u i • V i s := by
      funext s
      simp [P, Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply,
        Finset.sum_apply]
    rw [heq]
    exact ParallelAt.sum Finset.univ (fun i _ => (hV i t ht).const_smul _)
      (hq.contMDiffAt (hI.mem_nhds (hsub ht)))
  have hpair : ∀ t ∈ Icc a b, ∀ u v,
      g.inner (q t) (P t u) (P t v) = g.inner (q a) u v := by
    intro t ht u v
    simpa only [hPa, ContinuousLinearMap.id_apply] using
      parallel_pairing_eq hab (fun s hs => hq.contMDiffAt (hI.mem_nhds (hsub hs)))
        (fun s hs => hp s hs u) (fun s hs => hp s hs v) ht
  refine ⟨P, hPa, ?_, hp, hpair⟩
  intro t ht
  have hinj : Function.Injective (P t) := by
    intro u v huv
    have h := hpair t ht (u - v) (u - v)
    rw [map_sub, huv, sub_self, map_zero] at h
    by_contra hne
    exact (ne_of_gt (g.pos _ _ (sub_ne_zero.mpr hne))) h.symm
  let f := LinearEquiv.ofBijective (P t).toLinearMap
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (P t).toLinearMap)).mp hinj⟩
  exact ⟨f.toContinuousLinearEquiv, rfl⟩



theorem exists_manifold_parallel_transport
    (g : RiemannianMetric n M)
    {q : ℝ → M} {I : Set ℝ} {a b : ℝ} (hab : a < b)
    (hI : IsOpen I) (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I)
    (hsub : Icc a b ⊆ I) :
    ∃ P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      P a = ContinuousLinearMap.id ℝ _ ∧
      (∀ t ∈ Icc a b, (P t).IsInvertible) ∧
      (∀ t ∈ Icc a b, ∀ u,
        ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t ∧
        ConnectionVariation.manifoldCovDerivAlong g q (fun s => P s u) 1 t = 0) ∧
      ∀ t ∈ Icc a b, ∀ u v,
        g.inner (q t) (P t u) (P t v) = g.inner (q a) u v := by
  obtain ⟨P, hPa, hPi, hP, hpair⟩ := exists_parallel_operators g hab hI hq hsub
  refine ⟨P, hPa, hPi, ?_, hpair⟩
  intro t ht u
  have hqt := hq.contMDiffAt (hI.mem_nhds (hsub ht))
  exact ⟨((hP t ht u).in_chart hqt (mem_extChartAt_source _)).1,
    (hP t ht u).covDeriv_eq_zero hqt⟩



theorem inverse_manifold_parallel_hasDerivAt (g : RiemannianMetric n M)
    {q : ℝ → M} {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hPi : ∀ s ∈ Icc a b, (P s).IsInvertible)
    (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hP : ∀ u, ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t ∧
      manifoldCovDerivAlong g q (fun s => P s u) 1 t = 0)
    {J : (s : ℝ) → TangentSpace (𝓡 n) (q s)}
    (hJ : DifferentiableAt ℝ (chartField q (q t) J) t) :
    HasDerivAt (fun s => (P s).inverse (J s))
      ((P t).inverse (manifoldCovDerivAlong g q J 1 t)) t := by
  let L : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun s => mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) (q t)) (q s)
  let Q : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun s => (L s).comp (P s)
  let A := parallelCoefficient (g.pullbackCoefficients (extChartAt (𝓡 n) (q t)).symm)
    ((extChartAt (𝓡 n) (q t)) ∘ q) t
  have hL : (L t).IsInvertible := isInvertible_mfderiv_extChartAt (mem_extChartAt_source _)
  have hQ : ContDiffAt ℝ ∞ Q t := contDiffAt_operator_of_apply fun u => (hP u).1
  have hQd : HasDerivAt Q (A.comp (Q t)) t := by
    apply hasDerivAt_operator_of_apply (hQ.differentiableAt (by simp))
    intro u
    have hd := hasDerivAt_chartField g hq (mem_extChartAt_source _)
      ((hP u).1.differentiableAt (by simp))
    change HasDerivAt (fun s => L s (P s u))
      (L t (manifoldCovDerivAlong g q (fun s => P s u) 1 t) + A (L t (P t u))) t at hd
    rw [(hP u).2, map_zero, zero_add] at hd
    exact hd
  let Y := fun s => (P s).inverse (J s)
  have hrep : Y =ᶠ[𝓝 t] fun s => (Q s).inverse (chartField q (q t) J s) := by
    filter_upwards [hq.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) (q t)).mem_nhds (mem_extChartAt_source _))]
      with s hs
    have hLs : (L s).IsInvertible := isInvertible_mfderiv_extChartAt hs
    change (P s).inverse (J s) = ((L s).comp (P s)).inverse (L s (J s))
    rw [hLs.inverse_comp_apply_of_left, hLs.inverse_apply_self]
  have hY : DifferentiableAt ℝ Y t := by
    have hi := ((hL.comp (hPi t ht)).contDiffAt_map_inverse (n := ∞)).comp t hQ
    exact ((hi.differentiableAt (by simp)).clm_apply hJ).congr_of_eventuallyEq hrep
  have hprod := hQd.clm_apply hY.hasDerivAt
  have heq : EqOn (fun s => Q s (Y s)) (chartField q (q t) J) (Icc a b) := by
    intro s hs
    change L s (P s ((P s).inverse (J s))) = L s (J s)
    rw [(hPi s hs).self_apply_inverse]
  have hd := hprod.hasDerivWithinAt.congr (fun s hs => (heq hs).symm) (heq ht).symm
  have hJd := hasDerivAt_chartField g hq (mem_extChartAt_source _) hJ
  have hval := (hd.derivWithin (uniqueDiffOn_Icc hab t ht)).symm.trans
    (hJd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht))
  have hval' : Q t (deriv Y t) = chartField q (q t) (manifoldCovDerivAlong g q J 1) t := by
    change A (Q t (Y t)) + Q t (deriv Y t) =
      L t (manifoldCovDerivAlong g q J 1 t) + A (L t (J t)) at hval
    have heqt : Q t (Y t) = L t (J t) := heq ht
    rw [heqt] at hval
    exact add_left_cancel (hval.trans (add_comm _ _))
  have hder : deriv Y t = (P t).inverse (manifoldCovDerivAlong g q J 1 t) := by
    apply (hPi t ht).injective
    rw [(hPi t ht).self_apply_inverse]
    exact hL.injective hval'
  exact hder ▸ hY.hasDerivAt

end PoincareConjecture.ConnectionAlongCurve

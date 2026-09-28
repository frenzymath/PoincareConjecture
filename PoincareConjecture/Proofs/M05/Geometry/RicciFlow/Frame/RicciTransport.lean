
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.Transport
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Connection.MetricDuality
import Mathlib.Analysis.Calculus.ContDiff.Operations










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology NNReal BigOperators

universe u

namespace PoincareConjecture.RicciFlow.Frame

private lemma differentiableWithinAt_clm_of_apply
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
    {f : ℝ → E →L[ℝ] G} {S : Set ℝ} {t : ℝ}
    (hf : ∀ v, DifferentiableWithinAt ℝ (fun s => f s v) S t) :
    DifferentiableWithinAt ℝ f S t := by
  let d := Module.finrank ℝ E
  let e₁ : E ≃L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e₂ := (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.differentiableAt.comp_differentiableWithinAt t
    (differentiableWithinAt_pi.mpr fun i => hf _)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}


noncomputable def ricciForm (F : RicciFlow n M (Ico a b)) (x : M) (t : ℝ) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  (- (1 / 2 : ℝ)) • derivWithin (fun s => (F.metric s).inner x) (Ico a b) t

theorem ricciForm_apply (F : RicciFlow n M (Ico a b))
    (x : M) {t : ℝ} (ht : t ∈ Ico a b) (v w : TangentSpace (𝓡 n) x) :
    ricciForm F x t v w = (F.connection t).ricci x v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have hd : DifferentiableWithinAt ℝ (fun s => (F.metric s).inner x) (Ico a b) t :=
    differentiableWithinAt_clm_of_apply fun u =>
      differentiableWithinAt_clm_of_apply fun z => (F.equation t ht x u z).differentiableWithinAt
  have he := ((hd.hasDerivWithinAt.clm_apply (hasDerivWithinAt_const t (Ico a b) v)).clm_apply
    (hasDerivWithinAt_const t (Ico a b) w)).derivWithin (uniqueDiffOn_Ico a b t ht)
  rw [(F.equation t ht x v w).derivWithin (uniqueDiffOn_Ico a b t ht)] at he
  simp only [map_zero, add_zero] at he
  simp only [ricciForm, smul_apply, smul_eq_mul]
  rw [← he]
  ring


noncomputable def ricciEndomorphism (F : RicciFlow n M (Ico a b)) (x : M) (t : ℝ) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  ((F.metric t).inner x).inverse.comp (ricciForm F x t)

theorem inner_ricciEndomorphism (F : RicciFlow n M (Ico a b))
    (x : M) {t : ℝ} (ht : t ∈ Ico a b) (v w : TangentSpace (𝓡 n) x) :
    (F.metric t).inner x (ricciEndomorphism F x t v) w =
      (F.connection t).ricci x v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  change (F.metric t).inner x (((F.metric t).inner x).inverse (ricciForm F x t v)) w = _
  rw [((F.metric t).inner_isInvertible x).self_apply_inverse]
  exact ricciForm_apply F x ht v w


theorem ricciEndomorphism_eq_sum (F : RicciFlow n M (Ico a b)) (x : M)
    {t : ℝ} (ht : t ∈ Ico a b) (v : TangentSpace (𝓡 n) x) :
    ricciEndomorphism F x t v =
      ∑ i, (F.connection t).ricci x v ((F.metric t).orthonormalBasis x i) •
        (F.metric t).orthonormalBasis x i := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let e := (F.metric t).orthonormalBasis x
  have h := e.sum_repr (ricciEndomorphism F x t v)
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
  exact inner_ricciEndomorphism F x ht v (e i)


theorem continuousOn_ricciEndomorphism (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M (Ico a b)) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    ContinuousOn (ricciEndomorphism F x) (Ico a b) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have hg : ContinuousOn (fun s => (F.metric s).inner x) (Ico a b) := by
    apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    exact fun w t ht => (F.equation t ht x v w).continuousWithinAt
  have hr : ContinuousOn (ricciForm F x) (Ico a b) := by
    apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    intro w
    apply ContinuousOn.congr (fun t ht =>
      (hC.ricci_evolution n M (Ico a b) F t ht x v w).continuousWithinAt)
    exact fun t ht => ricciForm_apply F x ht v w
  intro t ht
  exact ((((F.metric t).inner_isInvertible x).contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt
    (f := fun s => (F.metric s).inner x) (hg t ht)).clm_comp (hr t ht)



private theorem exists_ricciTransport_map (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M (Ico a b)) {T : ℝ} (haT : a < T) (hTb : T < b) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    ∃ U : ℝ → TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      U a = ContinuousLinearMap.id ℝ _ ∧
      (∀ t ∈ Icc a T, HasDerivWithinAt U
        ((ricciEndomorphism F x t).comp (U t)) (Icc a T) t) ∧
      (∀ t ∈ Icc a T, ∀ v w,
        (F.metric t).inner x (U t v) (U t w) = (F.metric a).inner x v w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let A := ricciEndomorphism F x
  have hsub : Icc a T ⊆ Ico a b := fun t ht => ⟨ht.1, ht.2.trans_lt hTb⟩
  have hAc : ContinuousOn A (Icc a T) :=
    (continuousOn_ricciEndomorphism hC F x).mono hsub
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hAc
  let K' : ℝ≥0 := ⟨max K 0, le_max_right _ _⟩
  have hK' : ∀ t ∈ Icc a T, ‖A t‖₊ ≤ K' := by
    intro t ht
    exact_mod_cast (hK t ht).trans (le_max_left K 0)
  let U := transportCurveOn A haT.le hAc hK'
  have hUa : U a = ContinuousLinearMap.id ℝ _ := by
    ext v
    rw [transportCurveOn_apply_of_mem A haT.le hAc hK' ⟨le_rfl, haT.le⟩]
    exact Poincare.ODE.Linear.solOf_left haT.le hAc hK' v
  have hUd : ∀ t ∈ Icc a T,
      HasDerivWithinAt U ((A t).comp (U t)) (Icc a T) t :=
    fun t ht => transportCurveOn_hasDerivWithinAt A haT.le hAc hK' ht
  refine ⟨U, hUa, hUd, ?_⟩
  intro t ht v w
  let f : ℝ → ℝ := fun s => (F.metric s).inner x (U s v) (U s w)
  have hd : ∀ s ∈ Icc a T, HasDerivWithinAt f 0 (Icc a T) s := by
    intro s hs
    have hmetric : DifferentiableWithinAt ℝ (fun r => (F.metric r).inner x)
        (Ico a b) s := differentiableWithinAt_clm_of_apply fun u =>
      differentiableWithinAt_clm_of_apply fun z =>
        (F.equation s (hsub hs) x u z).differentiableWithinAt
    have hg : HasDerivWithinAt (fun r => (F.metric r).inner x)
        ((-2 : ℝ) • ricciForm F x s) (Icc a T) s := by
      apply (hmetric.hasDerivWithinAt.mono hsub).congr_deriv
      norm_num [ricciForm, smul_smul]
    have hv := (hUd s hs).clm_apply (hasDerivWithinAt_const s (Icc a T) v)
    have hw := (hUd s hs).clm_apply (hasDerivWithinAt_const s (Icc a T) w)
    have hh := (hg.clm_apply hv).clm_apply hw
    apply hh.congr_deriv
    simp only [smul_apply, add_apply, map_zero, add_zero, ContinuousLinearMap.comp_apply,
      smul_eq_mul]
    rw [ricciForm_apply F x (hsub hs), inner_ricciEndomorphism F x (hsub hs)]
    rw [(F.metric s).symm x (U s v) (A s (U s w)),
      inner_ricciEndomorphism F x (hsub hs)]
    have hsymm := ((hC.tensor_calculus n M (F.metric s) (F.connection s)).2.2.2.1
      x (U s v) (U s w) (U s v) (U s w)).2.2.2
    linarith
  have hc := constant_of_derivWithin_zero
    (fun s hs => (hd s hs).differentiableWithinAt)
    (fun s hs => (hd s ⟨hs.1, hs.2.le⟩).derivWithin
      (uniqueDiffOn_Icc haT s ⟨hs.1, hs.2.le⟩)) t ht
  simpa only [f, hUa, ContinuousLinearMap.id_apply] using hc



theorem exists_ricciTransport (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M (Ico a b)) {T : ℝ} (haT : a < T) (hTb : T < b) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    ∃ U : ℝ → TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      U a = ContinuousLinearMap.id ℝ _ ∧
      (∀ t ∈ Icc a T, HasDerivWithinAt U
        ((ricciEndomorphism F x t).comp (U t)) (Icc a T) t) ∧
      (∀ t ∈ Icc a T, ∀ v w,
        (F.metric t).inner x (U t v) (U t w) = (F.metric a).inner x v w) ∧
      (∀ t ∈ Icc a T, (U t).IsInvertible) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  obtain ⟨U, hUa, hUd, hpair⟩ := exists_ricciTransport_map hC F haT hTb x
  refine ⟨U, hUa, hUd, hpair, ?_⟩
  intro t ht
  have hi : Function.Injective (U t) := by
    apply (U t).toLinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro v hv
    change U t v = 0 at hv
    have hh := hpair t ht v v
    rw [hv] at hh
    by_contra hn
    have hp := (F.metric a).pos x v hn
    simp only [map_zero] at hh
    linarith
  let e := (LinearEquiv.ofBijective (U t).toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  exact ContinuousLinearMap.isInvertible_equiv (f := e)

end PoincareConjecture.RicciFlow.Frame

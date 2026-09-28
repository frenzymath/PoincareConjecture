import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Frame.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Frame.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.MetricDuality












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareConjecture.RicciFlow.Splitting

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

noncomputable def ricciForm (F : RicciFlow n M (Icc a b)) (x : M) (t : ℝ) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  (-(1 / 2 : ℝ)) • derivWithin (fun s => (F.metric s).inner x) (Icc a b) t

private theorem metric_hasDerivWithinAt (F : RicciFlow n M (Icc a b))
    (x : M) {t : ℝ} (ht : t ∈ Icc a b) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric b).toRiemannianMetric⟩
    HasDerivWithinAt (fun s => (F.metric s).inner x)
      ((-2 : ℝ) • ricciForm F x t) (Icc a b) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have hd : DifferentiableWithinAt ℝ (fun s => (F.metric s).inner x) (Icc a b) t :=
    differentiableWithinAt_clm_of_apply fun v =>
      differentiableWithinAt_clm_of_apply fun w => (F.equation t ht x v w).differentiableWithinAt
  simpa only [ricciForm, smul_smul, show (-2 : ℝ) * -(1 / 2) = 1 by norm_num,
    one_smul] using hd.hasDerivWithinAt

theorem ricciForm_apply (hab : a < b) (F : RicciFlow n M (Icc a b))
    (x : M) {t : ℝ} (ht : t ∈ Icc a b) (v w : TangentSpace (𝓡 n) x) :
    ricciForm F x t v w = (F.connection t).ricci x v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  have hd := ((metric_hasDerivWithinAt F x ht).clm_apply
    (hasDerivWithinAt_const t (Icc a b) v)).clm_apply
      (hasDerivWithinAt_const t (Icc a b) w)
  have heq := (uniqueDiffOn_Icc hab t ht).eq_deriv (Icc a b) hd (F.equation t ht x v w)
  simp only [smul_apply, map_zero, smul_eq_mul, add_zero] at heq
  linarith

noncomputable def ricciEndomorphism
    (F : RicciFlow n M (Icc a b)) (x : M) (t : ℝ) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  ((F.metric t).inner x).inverse.comp (ricciForm F x t)

theorem inner_ricciEndomorphism (hab : a < b)
    (F : RicciFlow n M (Icc a b)) (x : M) {t : ℝ} (ht : t ∈ Icc a b)
    (v w : TangentSpace (𝓡 n) x) :
    (F.metric t).inner x (ricciEndomorphism F x t v) w =
      (F.connection t).ricci x v w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  change (F.metric t).inner x (((F.metric t).inner x).inverse (ricciForm F x t v)) w = _
  rw [((F.metric t).inner_isInvertible x).self_apply_inverse]
  exact ricciForm_apply hab F x ht v w

theorem ricciEndomorphism_eq_ricciSharp (hab : a < b)
    (F : RicciFlow n M (Icc a b)) (x : M) {t : ℝ} (ht : t ∈ Icc a b)
    (v : TangentSpace (𝓡 n) x) :
    ricciEndomorphism F x t v = ricciSharp (F.connection t) x v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let e := (F.metric t).orthonormalBasis x
  change ricciEndomorphism F x t v = ∑ i, (F.connection t).ricci x v (e i) • e i
  conv_lhs => rw [← e.sum_repr (ricciEndomorphism F x t v)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
  exact inner_ricciEndomorphism hab F x ht v (e i)

private theorem continuousOn_ricciEndomorphism (hC : RicciFlowCurvatureTheory.{u})
    (hab : a < b) (F : RicciFlow n M (Icc a b)) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric b).toRiemannianMetric⟩
    ContinuousOn (ricciEndomorphism F x) (Icc a b) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have hg : ContinuousOn (fun s => (F.metric s).inner x) (Icc a b) := by
    apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    exact fun w t ht => (F.equation t ht x v w).continuousWithinAt
  have hr : ContinuousOn (ricciForm F x) (Icc a b) := by
    apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    intro w
    apply ContinuousOn.congr (fun t ht =>
      (hC.ricci_evolution n M (Icc a b) F t ht x v w).continuousWithinAt)
    exact fun t ht => ricciForm_apply hab F x ht v w
  intro t ht
  exact ((((F.metric t).inner_isInvertible x).contDiffAt_map_inverse
    (n := ∞)).continuousAt.comp_continuousWithinAt
      (f := fun s => (F.metric s).inner x) (hg t ht)).clm_comp (hr t ht)



theorem exists_terminal_ricci_transport
    (hC : RicciFlowCurvatureTheory.{u}) (hab : a < b)
    (F : RicciFlow n M (Icc a b)) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric b).toRiemannianMetric⟩
    ∃ U : ℝ → TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      U b = ContinuousLinearMap.id ℝ _ ∧
      (∀ t ∈ Icc a b, ∀ v,
        HasDerivWithinAt (fun s => U s v)
          (ricciSharp (F.connection t) x (U t v)) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ∀ v w,
        (F.metric t).inner x (U t v) (U t w) = (F.metric b).inner x v w) ∧
      (∀ t ∈ Icc a b, (U t).IsInvertible) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let A := ricciEndomorphism F x
  have hAc : ContinuousOn A (Icc a b) := continuousOn_ricciEndomorphism hC hab F x
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hAc
  let K' : ℝ≥0 := ⟨max K 0, le_max_right _ _⟩
  have hK' : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K' := by
    intro t ht
    exact_mod_cast (hK t ht).trans (le_max_left K 0)
  let V := Frame.transportCurveOn A hab.le hAc hK'
  have hVa : V a = ContinuousLinearMap.id ℝ _ := Frame.transportCurveOn_left A _ _ _
  have hVd : ∀ t ∈ Icc a b,
      HasDerivWithinAt V ((A t).comp (V t)) (Icc a b) t :=
    fun t ht => Frame.transportCurveOn_hasDerivWithinAt A hab.le hAc hK' ht
  have hpair : ∀ t ∈ Icc a b, ∀ v w,
      (F.metric t).inner x (V t v) (V t w) = (F.metric a).inner x v w := by
    intro t ht v w
    let q : ℝ → ℝ := fun s => (F.metric s).inner x (V s v) (V s w)
    have hd : ∀ s ∈ Icc a b, HasDerivWithinAt q 0 (Icc a b) s := by
      intro s hs
      have hv := (hVd s hs).clm_apply (hasDerivWithinAt_const s (Icc a b) v)
      have hw := (hVd s hs).clm_apply (hasDerivWithinAt_const s (Icc a b) w)
      have hh := ((metric_hasDerivWithinAt F x hs).clm_apply hv).clm_apply hw
      apply hh.congr_deriv
      simp only [smul_apply, add_apply, map_zero, add_zero, ContinuousLinearMap.comp_apply,
        smul_eq_mul]
      rw [ricciForm_apply hab F x hs, inner_ricciEndomorphism hab F x hs]
      rw [(F.metric s).symm x (V s v) (A s (V s w)),
        inner_ricciEndomorphism hab F x hs]
      have hsymm := ((hC.tensor_calculus n M (F.metric s) (F.connection s)).2.2.2.1
        x (V s v) (V s w) (V s v) (V s w)).2.2.2
      linarith
    have hc := constant_of_derivWithin_zero
      (fun s hs => (hd s hs).differentiableWithinAt)
      (fun s hs => (hd s ⟨hs.1, hs.2.le⟩).derivWithin
        (uniqueDiffOn_Icc hab s ⟨hs.1, hs.2.le⟩)) t ht
    simpa only [q, hVa, ContinuousLinearMap.id_apply] using hc
  have hinv : ∀ t ∈ Icc a b, (V t).IsInvertible := by
    intro t ht
    let e := (LinearEquiv.ofBijective (V t).toLinearMap
      (Frame.transportCurveOn_bijective A hab.le hAc hK' ht)).toContinuousLinearEquiv
    exact ContinuousLinearMap.isInvertible_equiv (f := e)
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  let U := fun t => (V t).comp (V b).inverse
  have hUb : U b = ContinuousLinearMap.id ℝ _ := by
    ext v
    exact (hinv b hb).self_apply_inverse v
  refine ⟨U, hUb, ?_, ?_, ?_⟩
  · intro t ht v
    have hd := (hVd t ht).clm_apply
      (hasDerivWithinAt_const t (Icc a b) ((V b).inverse v))
    simpa only [U, A, ContinuousLinearMap.comp_apply, map_zero, add_zero,
      ricciEndomorphism_eq_ricciSharp hab F x ht] using hd
  · intro t ht v w
    have ht' := hpair t ht ((V b).inverse v) ((V b).inverse w)
    have hb' := hpair b hb ((V b).inverse v) ((V b).inverse w)
    rw [(hinv b hb).self_apply_inverse, (hinv b hb).self_apply_inverse] at hb'
    exact ht'.trans hb'.symm
  · intro t ht
    exact (hinv t ht).comp (hinv b hb).inverse

end PoincareConjecture.RicciFlow.Splitting

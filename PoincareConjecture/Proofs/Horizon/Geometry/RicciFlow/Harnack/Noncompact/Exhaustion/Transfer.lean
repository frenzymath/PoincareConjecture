import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Variation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.BoundaryRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}




lemma abs_inner_deriv_connection_le
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (K : ℝ) (x : M)
    (hRic : ∀ u v w : TangentSpace (𝓡 n) x,
      |(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
        x ![u, v, w]| ≤ K * (F.metric t).tangentNorm x u *
          (F.metric t).tangentNorm x v * (F.metric t).tangentNorm x w)
    (u v w : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    |(F.metric t).inner x
      ((deriv (fun s => (F.connection s).connection
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) t) u) w| ≤
      3 * K * (F.metric t).tangentNorm x u * (F.metric t).tangentNorm x v *
        (F.metric t).tangentNorm x w := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  rw [F.inner_deriv_connection_extend_of_equation ht]
  obtain ⟨h₁, h₁'⟩ := abs_le.mp (hRic u v w)
  obtain ⟨h₂, h₂'⟩ := abs_le.mp (hRic v u w)
  obtain ⟨h₃, h₃'⟩ := abs_le.mp (hRic w u v)
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩


lemma tangentNorm_deriv_connection_le
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (K : ℝ) (x : M)
    (hRic : ∀ u v w : TangentSpace (𝓡 n) x,
      |(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
        x ![u, v, w]| ≤ K * (F.metric t).tangentNorm x u *
          (F.metric t).tangentNorm x v * (F.metric t).tangentNorm x w)
    (u v : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    (F.metric t).tangentNorm x
      ((deriv (fun s => (F.connection s).connection
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) t) u) ≤
      3 * K * (F.metric t).tangentNorm x u * (F.metric t).tangentNorm x v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let a := (deriv (fun s => (F.connection s).connection
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) t) u
  have h := F.abs_inner_deriv_connection_le ht K x hRic u v a
  have hn : (F.metric t).tangentNorm x a = ‖a‖ := by
    change Real.sqrt (inner ℝ a a) = ‖a‖
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  change |inner ℝ a a| ≤ _ at h
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _), hn] at h
  rw [hn]
  by_cases ha : a = 0
  · subst a
    have hzero := hRic u v v
    have hnonneg := (abs_nonneg _).trans hzero
    by_cases hv : (F.metric t).tangentNorm x v = 0
    · simp [hv, ha]
    · have hvpos : 0 < (F.metric t).tangentNorm x v :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hv)
      have hKuv : 0 ≤ K * (F.metric t).tangentNorm x u *
          (F.metric t).tangentNorm x v :=
        nonneg_of_mul_nonneg_left hnonneg hvpos
      nlinarith
  · have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    nlinarith


lemma hasDerivAt_hessian
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (f : M → ℝ) (x : M) (u v : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    HasDerivAt (fun s => (F.connection s).hessian f x u v)
      (-mvfderiv (𝓡 n) f x
        ((deriv (fun s => (F.connection s).connection
          (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) t) u)) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  have h := ((F.contDiffAt_connection ht
    (FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)).differentiableAt
      (by simp) |>.hasDerivAt).clm_apply (hasDerivAt_const t u)
  have h' := (mvfderiv (𝓡 n) f x).hasFDerivAt.comp_hasDerivAt t h
  have h'' := (hasDerivAt_const t
    (mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v y)) x u)).sub h'
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self, zero_sub, map_zero, add_zero, Function.comp_def] at h'' ⊢
  convert h'' using 1 <;> rfl



lemma abs_deriv_hessian_le
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (f : M → ℝ) (K G : ℝ) (hG : 0 ≤ G) (x : M)
    (hRic : ∀ u v w : TangentSpace (𝓡 n) x,
      |(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
        x ![u, v, w]| ≤ K * (F.metric t).tangentNorm x u *
          (F.metric t).tangentNorm x v * (F.metric t).tangentNorm x w)
    (hf : ∀ v : TangentSpace (𝓡 n) x,
      |mvfderiv (𝓡 n) f x v| ≤ G * (F.metric t).tangentNorm x v)
    (v : TangentSpace (𝓡 n) x) :
    |deriv (fun s => (F.connection s).hessian f x v v) t| ≤
      3 * G * K * (F.metric t).inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  rw [(F.hasDerivAt_hessian ht f x v v).deriv, abs_neg]
  refine (hf _).trans ((mul_le_mul_of_nonneg_left
    (F.tangentNorm_deriv_connection_le ht K x hRic v v) hG).trans_eq ?_)
  have hv : (F.metric t).tangentNorm x v ^ 2 = (F.metric t).inner x v v := by
    change (Real.sqrt (inner ℝ v v)) ^ 2 = inner ℝ v v
    exact Real.sq_sqrt (real_inner_self_nonneg)
  rw [← hv]
  ring



lemma abs_hessian_sub_le
    (F : RicciFlow n M J) {I : Set ℝ} (hI : Convex ℝ I)
    (hIJ : I ⊆ J)
    (f : M → ℝ) (K A G T : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hG : 0 ≤ G)
    (x : M) {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I)
    (hT : ∀ t ∈ I, |t - a| ≤ T)
    (hRic : ∀ t ∈ I, ∀ v : TangentSpace (𝓡 n) x,
      |(F.connection t).ricci x v v| ≤ K * (F.metric t).inner x v v)
    (hRicDeriv : ∀ t ∈ I, ∀ u v w : TangentSpace (𝓡 n) x,
      |(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
        x ![u, v, w]| ≤ A * (F.metric t).tangentNorm x u *
          (F.metric t).tangentNorm x v * (F.metric t).tangentNorm x w)
    (hf : ∀ v : TangentSpace (𝓡 n) x,
      |mvfderiv (𝓡 n) f x v| ≤ G * (F.metric a).tangentNorm x v)
    (v : TangentSpace (𝓡 n) x) :
    |(F.connection b).hessian f x v v - (F.connection a).hessian f x v v| ≤
      (3 * G * A * Real.exp (K * T) ^ 3 * (F.metric a).inner x v v) * |b - a| := by
  let E := Real.exp (K * T)
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hQ (t : ℝ) : 0 ≤ (F.metric t).inner x v v := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    change 0 ≤ inner ℝ v v
    exact real_inner_self_nonneg
  have hsub : I ⊆ J := hIJ
  have hgrad (t : ℝ) (ht : t ∈ I) (w : TangentSpace (𝓡 n) x) :
      |mvfderiv (𝓡 n) f x w| ≤ (G * E) * (F.metric t).tangentNorm x w := by
    have hnorm := F.tangentNorm_le_exp_of_ricci_bound hI hsub x w K
      (fun s hs => hRic s hs w) ht ha
    have he : Real.exp (K * |a - t|) ≤ E := by
      apply Real.exp_le_exp.mpr
      rw [abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (hT t ht) hK
    have hnorm' := hnorm.trans (mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg _))
    exact (hf w).trans ((mul_le_mul_of_nonneg_left hnorm' hG).trans_eq (by ring))
  have hmetric (t : ℝ) (ht : t ∈ I) :
      (F.metric t).inner x v v ≤ E ^ 2 * (F.metric a).inner x v v := by
    have h := (F.metric_inner_self_exp_bounds hI hsub x v K
      (fun s hs => hRic s hs v) ha ht).2
    have he : Real.exp ((2 * K) * |t - a|) ≤ E ^ 2 := by
      dsimp only [E]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      norm_num only [Nat.cast_ofNat]
      nlinarith [hT t ht]
    exact h.trans (mul_le_mul_of_nonneg_right he (hQ a))
  have hdiff (t : ℝ) (ht : t ∈ interior I) :
      DifferentiableAt ℝ (fun s => (F.connection s).hessian f x v v) t :=
    (F.hasDerivAt_hessian (interior_mono hIJ ht) f x v v).differentiableAt
  have hbound (t : ℝ) (ht : t ∈ interior I) :
      ‖deriv (fun s => (F.connection s).hessian f x v v) t‖ ≤
        3 * G * A * E ^ 3 * (F.metric a).inner x v v := by
    rw [Real.norm_eq_abs]
    have htI := interior_subset ht
    have h := F.abs_deriv_hessian_le (interior_mono hIJ ht) f A (G * E)
      (mul_nonneg hG hE) x (hRicDeriv t htI) (hgrad t htI) v
    refine h.trans ((mul_le_mul_of_nonneg_left (hmetric t htI)
      (by positivity : 0 ≤ 3 * (G * E) * A)).trans_eq ?_)
    ring
  have hcont : ContinuousOn (fun s => (F.connection s).hessian f x v v) I :=
    fun t ht => (F.contDiffWithinAt_hessian (hIJ ht) f x v v).continuousWithinAt.mono hIJ
  have hdiffOn : DifferentiableOn ℝ (fun s => (F.connection s).hessian f x v v) (interior I) :=
    fun t ht => (hdiff t ht).differentiableWithinAt
  have hu := hI.image_sub_le_mul_sub_of_deriv_le hcont hdiffOn
    (fun t ht => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound t ht))
  have hl := hI.mul_sub_le_image_sub_of_le_deriv hcont hdiffOn
    (fun t ht => (neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using hbound t ht)))
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact abs_le.mpr ⟨by have h := hl a ha b hb hab; linarith, hu a ha b hb hab⟩
  · rw [abs_of_nonpos (sub_nonpos.mpr hba)]
    apply abs_le.mpr
    constructor
    · have h := hu b hb a ha hba
      dsimp only [E] at *
      nlinarith
    · have h := hl b hb a ha hba
      dsimp only [E] at *
      nlinarith


lemma gradient_bound_of_initial
    (F : RicciFlow n M J) {I : Set ℝ} (hI : Convex ℝ I) (hIJ : I ⊆ J)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (O : M)
    (S : RiemannianMetric.SmoothDistanceLike (F.metric a) (F.connection a) O)
    (K : ℝ)
    (hRic : ∀ t ∈ I, ∀ x (v : TangentSpace (𝓡 n) x),
      |(F.connection t).ricci x v v| ≤ K * (F.metric t).inner x v v)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    |mvfderiv (𝓡 n) S.toFun x v| ≤
      (S.bound * Real.exp (K * |b - a|)) * (F.metric b).tangentNorm x v := by
  have h := F.tangentNorm_le_exp_of_ricci_bound hI hIJ x v K
    (fun t ht => hRic t ht x v) hb ha
  rw [abs_sub_comm a b] at h
  exact (S.gradient_bound x v).trans ((mul_le_mul_of_nonneg_left h S.bound_nonneg).trans_eq
    (by ring))



lemma hessian_bound_of_initial
    (F : RicciFlow n M J) {I : Set ℝ} (hI : Convex ℝ I)
    (hIJ : I ⊆ J)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (O : M)
    (S : RiemannianMetric.SmoothDistanceLike (F.metric a) (F.connection a) O)
    (K A T : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hT : ∀ t ∈ I, |t - a| ≤ T)
    (hRic : ∀ t ∈ I, ∀ x (v : TangentSpace (𝓡 n) x),
      |(F.connection t).ricci x v v| ≤ K * (F.metric t).inner x v v)
    (hRicDeriv : ∀ t ∈ I, ∀ x (u v w : TangentSpace (𝓡 n) x),
      |(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
        x ![u, v, w]| ≤ A * (F.metric t).tangentNorm x u *
          (F.metric t).tangentNorm x v * (F.metric t).tangentNorm x w)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (F.connection b).hessian S.toFun x v v ≤
      (S.bound * (1 + 3 * A * Real.exp (K * T) ^ 3 * T) * Real.exp (K * T) ^ 2) *
        (F.metric b).inner x v v := by
  let E := Real.exp (K * T)
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hT₀ : 0 ≤ T := by simpa using hT a ha
  have hS : 0 ≤ S.bound := S.bound_nonneg
  have hQ (t : ℝ) : 0 ≤ (F.metric t).inner x v v := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    change 0 ≤ inner ℝ v v
    exact real_inner_self_nonneg
  have h := F.abs_hessian_sub_le hI hIJ S.toFun K A S.bound T hK hA
    S.bound_nonneg x ha hb hT (fun t ht => hRic t ht x)
    (fun t ht => hRicDeriv t ht x) (S.gradient_bound x) v
  have hcoeff : 0 ≤ 3 * S.bound * A * E ^ 3 * (F.metric a).inner x v v :=
    mul_nonneg (by positivity) (hQ a)
  have hchange := (le_abs_self _).trans (h.trans
    (mul_le_mul_of_nonneg_left (hT b hb) hcoeff))
  have hstep : (F.connection b).hessian S.toFun x v v ≤
      (S.bound * (1 + 3 * A * E ^ 3 * T)) * (F.metric a).inner x v v := by
    have hs := S.hessian_bound x v
    dsimp only [E] at hchange ⊢
    nlinarith
  have hmetric := (F.metric_inner_self_exp_bounds hI hIJ
    x v K (fun t ht => hRic t ht x v) hb ha).2
  have hexp : Real.exp (2 * K * |a - b|) ≤ E ^ 2 := by
    dsimp only [E]
    rw [← Real.exp_nat_mul, abs_sub_comm a b]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith [hT b hb]
  have hm := hmetric.trans (mul_le_mul_of_nonneg_right hexp (hQ b))
  refine hstep.trans ((mul_le_mul_of_nonneg_left hm
    (by positivity : 0 ≤ S.bound * (1 + 3 * A * E ^ 3 * T))).trans_eq ?_)
  dsimp only [E]
  ring

private lemma edist_le_mul_of_tangentNorm_le
    (g h : RiemannianMetric n M) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ x (v : TangentSpace (𝓡 n) x), h.tangentNorm x v ≤ C * g.tangentNorm x v)
    (x y : M) : h.edist x y ≤ ENNReal.ofReal C * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdiv : h.edist x y / ENNReal.ofReal C ≤ g.edist x y := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro r hr
    obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlength⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hr
    have hlength := RiemannianMetric.pathELength_le_of_tangentNorm_le g h γ 0 1 C hC.le
      (fun _ _ => hbound _)
    have hdist : h.edist x y ≤ h.pathELength γ 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨h.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_le_pathELength hγsmooth hγ0 hγ1 zero_le_one
    apply (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top).mpr
    exact (hdist.trans hlength).trans (by
      rw [mul_comm r]
      exact mul_le_mul_right hγlength.le _)
  simpa only [mul_comm] using
    (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top).mp hdiv



lemma toReal_edist_le_exp_of_ricci_bound
    (F : RicciFlow n M J) {I : Set ℝ} (hI : Convex ℝ I) (hIJ : I ⊆ J)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (K : ℝ)
    (hRic : ∀ t ∈ I, ∀ x (v : TangentSpace (𝓡 n) x),
      |(F.connection t).ricci x v v| ≤ K * (F.metric t).inner x v v)
    (x y : M) :
    ((F.metric b).edist x y).toReal ≤
      Real.exp (K * |b - a|) * ((F.metric a).edist x y).toReal := by
  have hforward := edist_le_mul_of_tangentNorm_le (F.metric a) (F.metric b)
    (Real.exp (K * |b - a|)) (Real.exp_pos _)
    (fun z v => F.tangentNorm_le_exp_of_ricci_bound hI hIJ z v K
      (fun t ht => hRic t ht z v) ha hb) x y
  by_cases htop : (F.metric a).edist x y = ⊤
  · have hreverse := edist_le_mul_of_tangentNorm_le (F.metric b) (F.metric a)
      (Real.exp (K * |a - b|)) (Real.exp_pos _)
      (fun z v => F.tangentNorm_le_exp_of_ricci_bound hI hIJ z v K
        (fun t ht => hRic t ht z v) hb ha) x y
    have hbtop : (F.metric b).edist x y = ⊤ := by
      by_contra hfinite
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
        (top_unique (by simpa [htop] using hreverse))
    simp [htop, hbtop]
  · have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop) hforward
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] using h


lemma distance_bounds_of_initial
    (F : RicciFlow n M J) {I : Set ℝ} (hI : Convex ℝ I) (hIJ : I ⊆ J)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (O : M)
    (S : RiemannianMetric.SmoothDistanceLike (F.metric a) (F.connection a) O)
    (K T : ℝ) (hK : 0 ≤ K) (hT : |b - a| ≤ T)
    (hRic : ∀ t ∈ I, ∀ x (v : TangentSpace (𝓡 n) x),
      |(F.connection t).ricci x v v| ≤ K * (F.metric t).inner x v v)
    (x : M) :
    ((F.metric b).edist O x).toReal + 1 ≤ Real.exp (K * T) * S.toFun x ∧
      Real.exp (K * T) * S.toFun x ≤
        (S.bound * Real.exp (K * T) ^ 2) * (((F.metric b).edist O x).toReal + 1) := by
  let E := Real.exp (K * T)
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hE₁ : 1 ≤ E := Real.one_le_exp (mul_nonneg hK ((abs_nonneg _).trans hT))
  have he : Real.exp (K * |b - a|) ≤ E :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT hK)
  have hforward := (F.toReal_edist_le_exp_of_ricci_bound hI hIJ ha hb K hRic O x).trans
    (mul_le_mul_of_nonneg_right he ENNReal.toReal_nonneg)
  have hreverse := F.toReal_edist_le_exp_of_ricci_bound hI hIJ hb ha K hRic O x
  rw [abs_sub_comm a b] at hreverse
  have hreverse' := hreverse.trans (mul_le_mul_of_nonneg_right he ENNReal.toReal_nonneg)
  constructor
  · have hlower := mul_le_mul_of_nonneg_left (S.distance_lower x) hE
    dsimp only [E] at *
    nlinarith
  · have hu := mul_le_mul_of_nonneg_left (S.distance_upper x) hE
    have hdist : ((F.metric a).edist O x).toReal + 1 ≤
        E * (((F.metric b).edist O x).toReal + 1) := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hdist (mul_nonneg hE S.bound_nonneg)
    dsimp only [E] at *
    nlinarith

end PoincareConjecture.RicciFlow

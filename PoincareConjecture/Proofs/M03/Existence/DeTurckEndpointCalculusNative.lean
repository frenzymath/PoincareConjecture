import PoincareConjecture.Proofs.M03.Existence.VolterraPicard
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.ContinuousMap.Interval









set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set Filter Asymptotics
open scoped Topology ContDiff

namespace PoincareConjecture.DeTurckEndpointCalculusNative

variable {P Z K : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [TopologicalSpace K] [CompactSpace K]


theorem hasFDerivWithinAt_path_eval
    (ev : ℝ → K) (hev : Continuous ev) (f : P → C(K, Z))
    {p : P} {t : ℝ} {s : Set ℝ} (L : P →L[ℝ] C(K, Z)) (v : Z)
    (hf : HasFDerivAt f L p)
    (ht : HasDerivWithinAt (fun a => f p (ev a)) v s t) :
    HasFDerivWithinAt (fun q : ℝ × P => f q.2 (ev q.1))
      ((ContinuousLinearMap.toSpanSingleton ℝ v).coprod
        ((ContinuousMap.evalCLM ℝ (ev t)).comp L)) (s ×ˢ univ) (t, p) := by
  let ell := 𝓝[s ×ˢ univ] (t, p)
  let A : ℝ → P →L[ℝ] Z := fun a => (ContinuousMap.evalCLM ℝ (ev a)).comp L
  have hA : Continuous A := continuous_clm_apply.mpr fun w => (L w).continuous.comp hev
  have hfst : Tendsto (Prod.fst : ℝ × P → ℝ) ell (𝓝[s] t) := by
    simpa only [ell, nhdsWithin_prod_eq, nhdsWithin_univ] using
      (tendsto_fst : Tendsto (Prod.fst : ℝ × P → ℝ)
        ((𝓝[s] t) ×ˢ 𝓝 p) (𝓝[s] t))
  have hsnd : Tendsto (Prod.snd : ℝ × P → P) ell (𝓝 p) := by
    simpa only [ell, nhdsWithin_prod_eq, nhdsWithin_univ] using
      (tendsto_snd : Tendsto (Prod.snd : ℝ × P → P)
        ((𝓝[s] t) ×ˢ 𝓝 p) (𝓝 p))
  have hsndO : (fun q : ℝ × P => q.2 - p) =O[ell] (fun q => q - (t, p)) :=
    isBigO_of_le ell fun q => norm_snd_le (q - (t, p))
  have hfstO : (fun q : ℝ × P => q.1 - t) =O[ell] (fun q => q - (t, p)) :=
    isBigO_of_le ell fun q => norm_fst_le (q - (t, p))
  have hspatial :
      (fun q : ℝ × P => (f q.2 - f p - L (q.2 - p)) (ev q.1)) =o[ell]
        (fun q => q - (t, p)) := by
    have heval :
        (fun q : ℝ × P => (f q.2 - f p - L (q.2 - p)) (ev q.1)) =O[ell]
          (fun q => f q.2 - f p - L (q.2 - p)) :=
      isBigO_of_le ell fun q => (f q.2 - f p - L (q.2 - p)).norm_coe_le_norm (ev q.1)
    exact heval.trans_isLittleO ((hf.isLittleO.comp_tendsto hsnd).trans_isBigO hsndO)
  have hvariation :
      (fun q : ℝ × P => (A q.1 - A t) (q.2 - p)) =o[ell]
        (fun q => q - (t, p)) := by
    apply IsLittleO.of_bound
    intro eps heps
    have hclose : ∀ᶠ a in 𝓝 t, ‖A a - A t‖ < eps := by
      have hc := hA.continuousAt (Metric.ball_mem_nhds (A t) heps)
      change ∀ᶠ a in 𝓝 t, A a ∈ Metric.ball (A t) eps at hc
      simpa only [Metric.mem_ball, dist_eq_norm] using hc
    filter_upwards [(hfst.mono_right nhdsWithin_le_nhds) hclose] with q hq
    exact ((A q.1 - A t).le_opNorm (q.2 - p)).trans
      (mul_le_mul hq.le (norm_snd_le (q - (t, p))) (norm_nonneg _) heps.le)
  have htime :
      (fun q : ℝ × P => f p (ev q.1) - f p (ev t) - (q.1 - t) • v) =o[ell]
        (fun q => q - (t, p)) :=
    (ht.hasFDerivWithinAt.isLittleO.comp_tendsto hfst).trans_isBigO hfstO
  apply HasFDerivWithinAt.of_isLittleO
  apply ((hspatial.add hvariation).add htime).congr_left
  intro q
  change ((f q.2 - f p - L (q.2 - p)) (ev q.1) +
      (A q.1 - A t) (q.2 - p)) +
      (f p (ev q.1) - f p (ev t) - (q.1 - t) • v) =
    f q.2 (ev q.1) - f p (ev t) - ((q.1 - t) • v + (L (q.2 - p)) (ev t))
  simp only [A, ContinuousMap.sub_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply]
  abel

section IntegralOperator

variable [CompleteSpace Z] {T : ℝ}

def integralPath (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, Z)) : C(Icc (0 : ℝ) T, Z) :=
  ⟨fun t => ∫ s in (0 : ℝ)..t, IccExtend hT f s, by
    have hc : Continuous (IccExtend hT f) := f.continuous.comp continuous_projIcc
    have hv := continuousOn_volterraPath_Icc (x₀ := (0 : Z)) (T := T) hc.continuousOn
    have hcont : Continuous (fun t : Icc (0 : ℝ) T =>
        volterraPath (0 : Z) (IccExtend hT f) t) :=
      hv.comp_continuous continuous_subtype_val (fun t => t.2)
    exact hcont.congr (fun t => by simp only [volterraPath, zero_add])⟩

theorem integralPath_norm_le (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, Z)) :
    ‖integralPath hT f‖ ≤ T * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg f))).mpr
  intro t
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (t : ℝ)) (fun s _ => f.norm_coe_le_norm (projIcc 0 T hT s))
  change ‖∫ s in (0 : ℝ)..(t : ℝ), IccExtend hT f s‖ ≤ T * ‖f‖
  calc
    _ ≤ ‖f‖ * |(t : ℝ) - 0| := hbound
    _ = (t : ℝ) * ‖f‖ := by rw [sub_zero, abs_of_nonneg t.2.1, mul_comm]
    _ ≤ T * ‖f‖ := mul_le_mul_of_nonneg_right t.2.2 (norm_nonneg f)


def integralOperator (hT : 0 ≤ T) :
    C(Icc (0 : ℝ) T, Z) →L[ℝ] C(Icc (0 : ℝ) T, Z) :=
  LinearMap.mkContinuous
    { toFun := integralPath hT
      map_add' := by
        intro f g
        ext t
        exact intervalIntegral.integral_add
          ((f.continuous.comp continuous_projIcc).intervalIntegrable _ _)
          ((g.continuous.comp continuous_projIcc).intervalIntegrable _ _)
      map_smul' := by
        intro c f
        ext t
        exact intervalIntegral.integral_smul c (IccExtend hT f) }
    T (integralPath_norm_le hT)

theorem integralOperator_apply (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, Z))
    (t : Icc (0 : ℝ) T) :
    integralOperator hT f t = ∫ s in (0 : ℝ)..t, IccExtend hT f s := rfl

theorem integralOperator_hasDerivWithinAt (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, Z)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (IccExtend hT (integralOperator hT f)) (f ⟨t, ht⟩)
      (Icc (0 : ℝ) T) t := by
  have hc : Continuous (IccExtend hT f) := f.continuous.comp continuous_projIcc
  have hd := hasDerivWithinAt_volterraPath_Icc (x₀ := (0 : Z)) hc.continuousOn ht
  have heq : EqOn (IccExtend hT (integralOperator hT f))
      (volterraPath (0 : Z) (IccExtend hT f)) (Icc (0 : ℝ) T) := by
    intro a ha
    rw [IccExtend_of_mem hT _ ha]
    simp only [integralOperator_apply, volterraPath, zero_add]
  rw [IccExtend_of_mem hT f ht] at hd
  exact hd.congr_of_mem heq ht

end IntegralOperator

section JetBootstrap

variable {d : ℕ} {A : Type*} (J : A → Type*) [∀ a, Fintype (J a)]
  {T : ℝ} (hT : 0 < T)

def coordinateDifferential (V : Fin d → C(K, Z)) : (Fin d → ℝ) →L[ℝ] C(K, Z) :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (V i)

theorem coordinateDifferential_apply (V : Fin d → C(K, Z)) (w : Fin d → ℝ) (x : K) :
    coordinateDifferential V w x = ∑ i, w i • V i x := by
  simp [coordinateDifferential]



theorem contDiffOn_of_spatial_jet_system
    {Omega : Set (Fin d → ℝ)} (hOmega : IsOpen Omega)
    (U : A → (Fin d → ℝ) → C(Icc (0 : ℝ) T, Z))
    (next : A → Fin d → A) (select : (a : A) → J a → A)
    (R : (a : A) → ((Fin d → ℝ) × (J a → Z)) → Z)
    (hR : ∀ a, ContDiff ℝ ∞ (R a))
    (hspace : ∀ a p, p ∈ Omega → HasFDerivAt (U a)
      (coordinateDifferential (fun i => U (next a i) p)) p)
    (htime : ∀ a p, p ∈ Omega → ∀ t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (fun s => U a p (projIcc 0 T hT.le s))
        (R a (p, fun j => U (select a j) p (projIcc 0 T hT.le t)))
        (Icc (0 : ℝ) T) t) :
    ∀ a, ContDiffOn ℝ ∞ (fun q : ℝ × (Fin d → ℝ) =>
      U a q.2 (projIcc 0 T hT.le q.1)) (Icc (0 : ℝ) T ×ˢ Omega) := by
  let f : A → (ℝ × (Fin d → ℝ)) → Z :=
    fun a q => U a q.2 (projIcc 0 T hT.le q.1)
  let S : A → (ℝ × (Fin d → ℝ)) → Z :=
    fun a q => R a (q.2, fun j => f (select a j) q)
  let D : A → (ℝ × (Fin d → ℝ)) → (ℝ × (Fin d → ℝ)) →L[ℝ] Z :=
    fun a q => (ContinuousLinearMap.toSpanSingleton ℝ (S a q)).coprod
      ((ContinuousMap.evalCLM ℝ (projIcc 0 T hT.le q.1)).comp
        (coordinateDifferential (fun i => U (next a i) q.2)))
  have hdiff : ∀ a q, q ∈ Icc (0 : ℝ) T ×ˢ Omega →
      HasFDerivWithinAt (f a) (D a q) (Icc (0 : ℝ) T ×ˢ Omega) q := by
    intro a q hq
    have hd := hasFDerivWithinAt_path_eval (projIcc 0 T hT.le) continuous_projIcc
      (U a) (coordinateDifferential (fun i => U (next a i) q.2)) (S a q)
      (hspace a q.2 hq.2) (htime a q.2 hq.2 q.1 hq.1)
    exact hd.mono (prod_mono_right (subset_univ Omega))
  have hbase : ∀ a, ContinuousOn (f a) (Icc (0 : ℝ) T ×ˢ Omega) := by
    intro a
    have hu : ContinuousOn (U a) Omega :=
      fun p hp => (hspace a p hp).continuousAt.continuousWithinAt
    have he : Continuous (projIcc 0 T hT.le) := continuous_projIcc
    have hpair : ContinuousOn (fun q : ℝ × (Fin d → ℝ) =>
        (U a q.2, projIcc 0 T hT.le q.1)) (Icc (0 : ℝ) T ×ˢ Omega) :=
      ((hu.comp continuous_snd.continuousOn (fun q hq => hq.2)).prodMk
        (he.comp continuous_fst).continuousOn)
    exact continuous_eval.comp_continuousOn hpair
  have hs : UniqueDiffOn ℝ (Icc (0 : ℝ) T ×ˢ Omega) :=
    (uniqueDiffOn_Icc hT).prod hOmega.uniqueDiffOn
  have hall : ∀ k : ℕ, ∀ a, ContDiffOn ℝ k (f a) (Icc (0 : ℝ) T ×ˢ Omega) := by
    intro k
    induction k with
    | zero => exact fun a => contDiffOn_zero.mpr (hbase a)
    | succ k ih =>
      intro a
      have hsource : ContDiffOn ℝ k (S a) (Icc (0 : ℝ) T ×ˢ Omega) :=
        (contDiff_infty.mp (hR a) k).comp_contDiffOn
          (contDiffOn_snd.prodMk (contDiffOn_pi.mpr (fun j => ih (select a j))))
      have hD : ContDiffOn ℝ k (D a) (Icc (0 : ℝ) T ×ˢ Omega) := by
        apply contDiffOn_clm_apply.mpr
        intro w
        have hsum : ContDiffOn ℝ k
            (fun q => ∑ i : Fin d, w.2 i • f (next a i) q) (Icc (0 : ℝ) T ×ˢ Omega) :=
          ContDiffOn.sum fun i _ => (ih (next a i)).const_smul (w.2 i)
        have hregular := (hsource.const_smul w.1).add hsum
        convert hregular using 1
        funext q
        change w.1 • S a q + coordinateDifferential (fun i => U (next a i) q.2)
          w.2 (projIcc 0 T hT.le q.1) = _
        rw [coordinateDifferential_apply]
      have hsucc := (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hs).mpr
        ⟨by simp, D a, hD, hdiff a⟩
      simpa only [Nat.cast_add, Nat.cast_one] using hsucc
  exact fun a => contDiffOn_infty.mpr (fun k => hall k a)

end JetBootstrap

end PoincareConjecture.DeTurckEndpointCalculusNative

end

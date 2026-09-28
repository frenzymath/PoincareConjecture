import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessAmbientAcceleration
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessEmbeddedCurve
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCurveCoefficients
import PoincareConjecture.Proofs.M63.Mathlib.RetractionTangentContinuity
import PoincareConjecture.Proofs.M63.Adapters
import PoincareConjecture.Proofs.M62.Lemma0_4_Continuity
import PoincareConjecture.Proofs.M04.ScalarHessian
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.AddCircle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)
local notation "XR" => C(AddCircle curvePeriod, ℝ)

set_option maxHeartbeats 800000 in

theorem normalCurve_c2_of_uniform_embedded_field_limits
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (cn : ℕ → ℝ → ℝ → M) (hcn : ∀ j, M62ShrinkingCurve F (cn j))
    (Rn Sn Hn : ℕ → ℝ → X) (Vn Wn : ℕ → ℝ → XR)
    (hRrep : ∀ j t, t ∈ Icc a b → ∀ x : ℝ,
      Rn j t (x : AddCircle curvePeriod) = e (cn j x t))
    (hSrep : ∀ j t, t ∈ Icc a b → ∀ x : ℝ, Sn j t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (cn j x t) (spatialUnitTangent F (cn j) t x))
    (hHrep : ∀ j t, t ∈ Icc a b → ∀ x : ℝ, Hn j t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (cn j x t) (m62CurvatureVector F (cn j) t x))
    (hVrep : ∀ j t, t ∈ Icc a b → ∀ x : ℝ,
      Vn j t (x : AddCircle curvePeriod) = curveSpeed F (cn j) t x)
    (hWrep : ∀ j t, t ∈ Icc a b → ∀ x : ℝ,
      Wn j t (x : AddCircle curvePeriod) = deriv (curveSpeed F (cn j) t) x)
    (r s h : ℝ → X) (v g : ℝ → XR)
    (hr : ContinuousOn r (Icc a b)) (hs : ContinuousOn s (Icc a b))
    (hh : ContinuousOn h (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (_hg : ContinuousOn g (Icc a b))
    (hR : TendstoUniformlyOn Rn r atTop (Icc a b))
    (hS : TendstoUniformlyOn Sn s atTop (Icc a b))
    (hH : TendstoUniformlyOn Hn h atTop (Icc a b))
    (hV : TendstoUniformlyOn Vn v atTop (Icc a b))
    (hW : TendstoUniformlyOn Wn g atTop (Icc a b))
    (hrU : ∀ t ∈ Icc a b, ∀ x : ℝ, r t (x : AddCircle curvePeriod) ∈ U)
    (hvpos : ∀ t ∈ Icc a b, ∀ x : ℝ, 0 < v t (x : AddCircle curvePeriod)) :
    let c := fun (x t : ℝ) => ρ (r t (x : AddCircle curvePeriod))
    let p := fun (t x : ℝ) => v t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod)
    let Z := fun (t x : ℝ) => (v t (x : AddCircle curvePeriod)) ^ 2 •
      (h t (x : AddCircle curvePeriod) - ambientCurveLower F e ρ t
        (r t (x : AddCircle curvePeriod)) (p t x)) +
      g t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod)
    M63C2ShrinkingCurveOn F c (Icc a b) ∧
      (∀ t ∈ Icc a b, ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => r t (y : AddCircle curvePeriod)) (p t x) x ∧
        HasDerivAt (p t) (Z t x) x ∧ curveSpeed F c t x = v t (x : AddCircle curvePeriod) ∧
        deriv (curveSpeed F c t) x = g t (x : AddCircle curvePeriod) ∧
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) =
          h t (x : AddCircle curvePeriod)) ∧
      (∀ t ∈ Ioo a b, ∀ x : ℝ, HasDerivAt
        (fun u => r u (x : AddCircle curvePeriod)) (h t (x : AddCircle curvePeriod)) t) ∧
      ∀ ε > 0, ∃ d > 0, ∀ t ∈ Icc a b, t - a < d → ∀ x : ℝ,
        ‖HSub.hSub (α := W) (β := W) (γ := W)
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x))
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x a) (m62CurvatureVector F c a x))‖ < ε := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  dsimp only
  let c := fun (x t : ℝ) => ρ (r t (x : AddCircle curvePeriod))
  let mulC (q : XR × X) : X :=
    ⟨fun z => q.1 z • q.2 z, q.1.continuous.smul q.2.continuous⟩
  have hmulC : Continuous mulC := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hscalar : Continuous (fun q : (XR × X) × AddCircle curvePeriod => q.1.1 q.2) :=
      continuous_fst.fst.eval continuous_snd
    have hvector : Continuous (fun q : (XR × X) × AddCircle curvePeriod => q.1.2 q.2) :=
      continuous_fst.snd.eval continuous_snd
    exact hscalar.smul hvector
  let Pn := fun j t => mulC (Vn j t, Sn j t)
  let p := fun t => mulC (v t, s t)
  have hp : ContinuousOn p (Icc a b) := hmulC.comp_continuousOn (hv.prodMk hs)
  have hab : a < b := by
    obtain ⟨u, hu, w, hw, hne⟩ := F.nontrivial
    by_contra hnot
    have heq : a = b := le_antisymm (hu.1.trans hu.2) (le_of_not_gt hnot)
    apply hne
    rw [← heq] at hu hw
    exact (le_antisymm hu.2 hu.1).trans (le_antisymm hw.2 hw.1).symm
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hdata (j : ℕ) := c2ShrinkingCurve_embedded_closed_data (m63C2_of_m62 (hcn j)) he
  have htimeData (j : ℕ) :=
    c2ShrinkingCurve_embedded_interior_equation (m63C2_of_m62 (hcn j)) he
  have liftCont (f : ℝ → X)
      (hf : ContinuousOn f (Icc a b)) :
      ContinuousOn (fun z : ℝ × ℝ => f z.2 (z.1 : AddCircle curvePeriod))
        (univ ×ˢ Icc a b) :=
    (hf.comp continuous_snd.continuousOn (fun z hz => hz.2)).eval
      ((AddCircle.continuous_mk' curvePeriod).comp continuous_fst).continuousOn
  have hquot : IsOpenQuotientMap
      (fun z : Icc a b × ℝ => (z.1, (z.2 : AddCircle curvePeriod))) :=
    IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
  have hVcont (j : ℕ) : ContinuousOn (Vn j) (Icc a b) := by
    have hlift : ContinuousOn (fun z : ℝ × ℝ => Vn j z.2 (z.1 : AddCircle curvePeriod))
        (univ ×ˢ Icc a b) :=
      (speed_continuousOn F (cn j) (hcn j)).congr (fun z hz => hVrep j z.2 hz.2 z.1)
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hquot.continuous_comp_iff.mp
      (hlift.comp_continuous
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        (fun z => ⟨mem_univ _, z.1.2⟩))
  have hScont (j : ℕ) : ContinuousOn (Sn j) (Icc a b) := by
    have hlift : ContinuousOn (fun z : ℝ × ℝ => Sn j z.2 (z.1 : AddCircle curvePeriod))
        (univ ×ˢ Icc a b) := by
      have hsp := (speed_continuousOn F (cn j) (hcn j)).inv₀
        (fun z hz => (speed_pos F (cn j) (hcn j) hz.2 z.1).ne')
      apply (hsp.smul (hdata j).2.2.2.1).congr
      intro z hz
      change Sn j z.2 (z.1 : AddCircle curvePeriod) =
        (curveSpeed F (cn j) z.2 z.1)⁻¹ • deriv (fun y => e (cn j y z.2)) z.1
      rw [((hdata j).2.1 z.2 hz.2 z.1).deriv]
      rw [hSrep j z.2 hz.2 z.1, spatialUnitTangent, map_smul]
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hquot.continuous_comp_iff.mp
      (hlift.comp_continuous
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        (fun z => ⟨mem_univ _, z.1.2⟩))
  let Vm (j : ℕ) : C(Icc a b, XR) := ⟨fun t => Vn j t, (hVcont j).domRestrict⟩
  let Sm (j : ℕ) : C(Icc a b, X) := ⟨fun t => Sn j t, (hScont j).domRestrict⟩
  let vm : C(Icc a b, XR) := ⟨fun t => v t, hv.domRestrict⟩
  let sm : C(Icc a b, X) := ⟨fun t => s t, hs.domRestrict⟩
  let pmul (q : C(Icc a b, XR) × C(Icc a b, X)) : C(Icc a b, X) :=
    ⟨fun t => mulC (q.1 t, q.2 t), hmulC.comp (q.1.continuous.prodMk q.2.continuous)⟩
  have hpmul : Continuous pmul := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hmulC.comp ((continuous_fst.fst.eval continuous_snd).prodMk
      (continuous_fst.snd.eval continuous_snd))
  have hP : TendstoUniformlyOn Pn p atTop (Icc a b) := by
    apply (hp.tendsto_domRestrict_iff_tendstoUniformlyOn
      (fun j => hmulC.comp_continuousOn ((hVcont j).prodMk (hScont j)))).mp
    exact (hpmul.tendsto (vm, sm)).comp
      (((hv.tendsto_domRestrict_iff_tendstoUniformlyOn hVcont).mpr hV).prodMk_nhds
        ((hs.tendsto_domRestrict_iff_tendstoUniformlyOn hScont).mpr hS))
  have hrfix (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      e (c x t) = r t (x : AddCircle curvePeriod) := by
    have hz := (continuous_eval_const (x : AddCircle curvePeriod)).tendsto (r t)
      |>.comp (hR.tendsto_at ht)
    have hguard : ∀ j, Rn j t (x : AddCircle curvePeriod) ∈ U := by
      intro j
      rw [hRrep j t ht]
      exact heU (mem_range_self _)
    have hpost := ((he.continuous.comp_continuousOn hρ.continuousOn)
      _ (hrU t ht x)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hz, Eventually.of_forall hguard⟩)
    have heq : ∀ j, e (ρ (Rn j t (x : AddCircle curvePeriod))) =
        Rn j t (x : AddCircle curvePeriod) := by
      intro j
      rw [hRrep j t ht, hρe]
    exact tendsto_nhds_unique (hpost.congr' (Eventually.of_forall heq)) hz
  have hmetric := (flow_pullback_metric_hessian_contDiffOn F hU hρ
    (f := fun _ => 0) contMDiff_const).1.continuousOn
  have hunit (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      (F.metric t).inner (c x t)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
          (s t (x : AddCircle curvePeriod)))
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
          (s t (x : AddCircle curvePeriod))) = 1 := by
    have hRz := (continuous_eval_const (x : AddCircle curvePeriod)).tendsto (r t)
      |>.comp (hR.tendsto_at ht)
    have hSz := (continuous_eval_const (x : AddCircle curvePeriod)).tendsto (s t)
      |>.comp (hS.tendsto_at ht)
    have hguard (j : ℕ) : ((t, Rn j t (x : AddCircle curvePeriod)),
        Sn j t (x : AddCircle curvePeriod)) ∈ ((Icc a b ×ˢ U) ×ˢ univ) := by
      refine ⟨⟨ht, ?_⟩, mem_univ _⟩
      change Rn j t (x : AddCircle curvePeriod) ∈ U
      rw [hRrep j t ht]
      exact heU (mem_range_self _)
    have hlim := (hmetric ((t, r t (x : AddCircle curvePeriod)), s t (x : AddCircle curvePeriod))
      ⟨⟨ht, hrU t ht x⟩, mem_univ _⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨(tendsto_const_nhds.prodMk_nhds hRz).prodMk_nhds hSz,
          Eventually.of_forall hguard⟩)
    have heq (j : ℕ) : (F.metric t).inner (ρ (Rn j t (x : AddCircle curvePeriod)))
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (Rn j t (x : AddCircle curvePeriod))
          (Sn j t (x : AddCircle curvePeriod)))
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (Rn j t (x : AddCircle curvePeriod))
          (Sn j t (x : AddCircle curvePeriod))) = 1 := by
      rw [hRrep j t ht, hSrep j t ht, hleft, hρe]
      exact unitTangent_inner_self F (cn j) (hcn j) ht x
    exact tendsto_nhds_unique (hlim.congr' (Eventually.of_forall heq)) tendsto_const_nhds
  have hfirstn (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      HasDerivAt (fun y : ℝ => Rn j t (y : AddCircle curvePeriod))
        (Pn j t (x : AddCircle curvePeriod)) x := by
    have hd := (hdata j).2.1 t ht x
    have hvel : curveVelocity (fun y => cn j y t) x =
        curveSpeed F (cn j) t x • spatialUnitTangent F (cn j) t x := by
      simp only [spatialUnitTangent, smul_smul,
        mul_inv_cancel₀ (speed_pos F (cn j) (hcn j) ht x).ne', one_smul]
    rw [hvel, map_smul] at hd
    change HasDerivAt _ (Vn j t (x : AddCircle curvePeriod) •
      Sn j t (x : AddCircle curvePeriod)) x
    rw [hVrep j t ht, hSrep j t ht]
    exact hd.congr_of_eventuallyEq (Eventually.of_forall (hRrep j t ht))
  have hfirst (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      HasDerivAt (fun y : ℝ => r t (y : AddCircle curvePeriod))
        (p t (x : AddCircle curvePeriod)) x :=
    hasDerivAt_of_tendstoUniformly
      ((ContinuousMap.tendsto_iff_tendstoUniformly.mp (hP.tendsto_at ht)).comp
        (fun y : ℝ => (y : AddCircle curvePeriod)))
      (Eventually.of_forall (fun j y => hfirstn j t ht y))
      (fun y => (continuous_eval_const (y : AddCircle curvePeriod)).tendsto (r t)
        |>.comp (hR.tendsto_at ht)) x
  have hrC1 (t : ℝ) (ht : t ∈ Icc a b) :
      ContDiff ℝ 1 (fun x : ℝ => r t (x : AddCircle curvePeriod)) := by
    apply contDiff_one_iff_hasFDerivAt.mpr
    refine ⟨fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (p t (x : AddCircle curvePeriod)),
      (ContinuousLinearMap.smulRightL ℝ ℝ W 1).continuous.comp
        ((p t).continuous.comp (AddCircle.continuous_mk' curvePeriod)), ?_⟩
    exact fun x => (hfirst t ht x).hasFDerivAt
  have hcC1 (t : ℝ) (ht : t ∈ Icc a b) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => c x t) :=
    (hρ.of_le (by norm_num)).comp_contMDiff (hrC1 t ht).contMDiff (hrU t ht)
  have hvel (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      curveVelocity (fun y => c y t) x =
        v t (x : AddCircle curvePeriod) • mfderiv 𝓘(ℝ, W) (𝓡 n) ρ
          (r t (x : AddCircle curvePeriod)) (s t (x : AddCircle curvePeriod)) := by
    have hchain := mfderiv_comp x
      ((hρ.contMDiffAt (hU.mem_nhds (hrU t ht x))).mdifferentiableAt (by simp))
      (hfirst t ht x).differentiableAt.mdifferentiableAt
    have hv := congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡 n) (c x t) => L 1) hchain
    rw [mfderiv_eq_fderiv, (hfirst t ht x).hasFDerivAt.fderiv] at hv
    change curveVelocity (fun y => c y t) x =
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
        ((1 : ℝ) • p t (x : AddCircle curvePeriod)) at hv
    simpa only [one_smul, p, mulC, ContinuousMap.coe_mk, map_smul] using! hv
  have himm (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      (curveVelocity (fun y => c y t) x : TangentSpace (𝓡 n) (c x t)) ≠ 0 := by
    have hv := hvel t ht x
    rw [hv]
    apply smul_ne_zero (hvpos t ht x).ne'
    intro hz
    simpa [hz] using hunit t ht x
  have hspeed (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      curveSpeed F c t x = v t (x : AddCircle curvePeriod) := by
    change Real.sqrt ((F.metric t).inner (c x t)
      (curveVelocity (fun y => c y t) x) (curveVelocity (fun y => c y t) x)) = _
    rw [hvel t ht x]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [hunit t ht x]
    simp only [mul_one]
    rw [← pow_two, Real.sqrt_sq (hvpos t ht x).le]
  have hspeedDeriv (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      HasDerivAt (fun y : ℝ => v t (y : AddCircle curvePeriod))
        (g t (x : AddCircle curvePeriod)) x := by
    apply hasDerivAt_of_tendstoUniformly
      ((ContinuousMap.tendsto_iff_tendstoUniformly.mp (hW.tendsto_at ht)).comp
        (fun y : ℝ => (y : AddCircle curvePeriod)))
      (Eventually.of_forall (fun j y => ?_))
      (fun y => (continuous_eval_const (y : AddCircle curvePeriod)).tendsto (v t)
        |>.comp (hV.tendsto_at ht)) x
    change HasDerivAt (fun z : ℝ => (Vn j t) (z : AddCircle curvePeriod))
      ((Wn j t) (y : AddCircle curvePeriod)) y
    rw [hWrep j t ht]
    exact (((speed_contDiff_of_c2 F (cn j) ((m63C2_of_m62 (hcn j)).spatial_regular t ht)
      ((hcn j).immersed t ht)).differentiable (by simp)) y).hasDerivAt.congr_of_eventuallyEq
        (Eventually.of_forall (hVrep j t ht))
  have hgrad (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      deriv (curveSpeed F c t) x = g t (x : AddCircle curvePeriod) := by
    rw [show curveSpeed F c t = (fun y : ℝ => v t (y : AddCircle curvePeriod)) from
      funext (hspeed t ht)]
    exact (hspeedDeriv t ht x).deriv
  have pushDeriv (q : ℝ → M) (hq : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 q) (x : ℝ) :
      HasDerivAt (fun y => e (q y)) (mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x)
        (curveVelocity q x) : W) x := by
    have hd :=
      (((he.of_le (by norm_num)).comp hq).contDiff.differentiable (by norm_num) x).hasDerivAt
    have hchain := mfderiv_comp x (he.mdifferentiable (by simp)).mdifferentiableAt
      ((hq x).mdifferentiableAt (by norm_num))
    rw [mfderiv_eq_fderiv] at hchain
    exact hd.congr_deriv (congrArg (fun L : ℝ →L[ℝ] W => L 1) hchain)
  have hpush (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (curveVelocity (fun y => c y t) x) =
        p t (x : AddCircle curvePeriod) :=
    ((pushDeriv (fun y => c y t) (hcC1 t ht) x).congr_of_eventuallyEq
      (Eventually.of_forall (fun y => (hrfix t ht y).symm))).unique (hfirst t ht x)
  have hpushS (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x) =
        s t (x : AddCircle curvePeriod) := by
    rw [spatialUnitTangent, map_smul, hpush t ht x, hspeed t ht x]
    simp only [p, mulC, ContinuousMap.coe_mk]
    rw [smul_smul, inv_mul_cancel₀ (hvpos t ht x).ne', one_smul]
  have hraw (q : ℝ → ℝ → M) {t : ℝ}
      (hq : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => q y t))
      (hqi : ∀ x, curveVelocity (n := n) (fun y => q y t) x ≠ 0) (x : ℝ) :
      deriv (deriv (fun y => e (q y t))) x =
        HAdd.hAdd (α := W) (β := W) (γ := W)
          (curveSpeed F q t x ^ 2 •
            HSub.hSub (α := W) (β := W) (γ := W)
              (mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t)
                (m62CurvatureVector F q t x) : W)
              (ambientCurveLower F e ρ t (e (q x t))
                (deriv (fun y => e (q y t)) x)))
          (deriv (curveSpeed F q t) x •
            (mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t)
              (spatialUnitTangent F q t x) : W)) := by
    have hvq := (Real.sqrt_pos.mpr ((F.metric t).pos _ _ (hqi x))).ne'
    have hspeedq : curveSpeed F q t x ≠ 0 := by
      change Real.sqrt _ ≠ 0
      exact hvq
    have hfirstq := (pushDeriv (fun y => q y t) (hq.of_le (by norm_num)) x).deriv
    have hB : ambientCurveLower F e ρ t (e (q x t)) (deriv (fun y => e (q y t)) x) =
        -((curveSpeed F q t x ^ 2)⁻¹ • coordinateHessian (F.connection t) e (q x t)
          (curveVelocity (fun y => q y t) x) (curveVelocity (fun y => q y t) x)) := by
      dsimp only [ambientCurveLower, ambientCurvePrincipal]
      rw [hfirstq, hleft, hρe, ← speed_sq]
    have hcurv := embedded_curvature_eq_acceleration_sub_tangent F he q hq hqi x
    have hS : (mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t) (spatialUnitTangent F q t x) : W) =
        (curveSpeed F q t x)⁻¹ • deriv (fun y => e (q y t)) x := by
      rw [spatialUnitTangent, map_smul, hfirstq]
    rw [hB]
    ext i
    have hi := congrArg (fun z : W => z i) hcurv
    have hiS := congrArg (fun z : W => z i) hS
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply,
      smul_eq_mul] at hi hiS ⊢
    change _ = curveSpeed F q t x ^ 2 * (_ - _) +
      deriv (curveSpeed F q t) x *
        ((mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t)
          (spatialUnitTangent F q t x) : W).ofLp i)
    change _ = (curveSpeed F q t x ^ 2)⁻¹ * (_ - _) -
      (deriv (curveSpeed F q t) x / curveSpeed F q t x ^ 3) * _ at hi
    rw [hiS] at ⊢
    field_simp [hvq, hspeedq] at hi hiS ⊢
    nlinarith [hi, hiS]
  let Ω : Set (W × W) := {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  have hguardn (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) (z : AddCircle curvePeriod) :
      (Rn j t z, Pn j t z) ∈ Ω := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    refine ⟨by rw [hRrep j t ht]; exact heU (mem_range_self _), ?_⟩
    let E := NormedSpace.fromTangentSpace (𝕜 := ℝ) (e (cn j x t))
    have hSval :
        E.symm (Sn j t (x : AddCircle curvePeriod)) =
          mfderiv (𝓡 n) 𝓘(ℝ, W) e (cn j x t)
            (spatialUnitTangent F (cn j) t x) := by
      have hSraw := congrArg E.symm (hSrep j t ht x)
      exact hSraw
    change mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (Rn j t (x : AddCircle curvePeriod))
      (Vn j t (x : AddCircle curvePeriod) •
        E.symm (Sn j t (x : AddCircle curvePeriod))) ≠ 0
    rw [hRrep j t ht, hVrep j t ht, hSval, ← map_smul, hleft,
      spatialUnitTangent, smul_smul, mul_inv_cancel₀ (speed_pos F (cn j) (hcn j) ht x).ne',
      one_smul]
    exact (hcn j).immersed t ht x
  have hguard (t : ℝ) (ht : t ∈ Icc a b) (z : AddCircle curvePeriod) :
      (r t z, p t z) ∈ Ω := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    refine ⟨hrU t ht x, ?_⟩
    change mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
      (v t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod)) ≠ 0
    rw [map_smul, ← hvel t ht x]
    exact himm t ht x
  have hpair : Continuous (fun q : X × X => q.1.prodMk q.2) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.fst.eval continuous_snd).prodMk
      (continuous_fst.snd.eval continuous_snd)
  have hcoeff := (ambientCurveCoefficients_contDiffOn F he hU hρ).2.1.continuousOn
  let Bc (t : ℝ) (ht : t ∈ Icc a b) : C(Ω, W) :=
    ⟨fun z => ambientCurveLower F e ρ t z.1.1 z.1.2,
      hcoeff.comp_continuous
        ((continuous_const.prodMk continuous_subtype_val.fst).prodMk continuous_subtype_val.snd)
        (fun z => ⟨ht, z.2.1, z.2.2⟩)⟩
  let Zc (t : ℝ) (ht : t ∈ Icc a b) : X :=
    mulC ((v t) ^ 2, h t - (Bc t ht).comp
      ⟨fun z => ⟨(r t z, p t z), hguard t ht z⟩,
        ((r t).continuous.prodMk (p t).continuous).subtype_mk _⟩) + mulC (g t, s t)
  have hsecond (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      HasDerivAt (fun y : ℝ => p t (y : AddCircle curvePeriod))
        (Zc t ht (x : AddCircle curvePeriod)) x := by
    let qn (j : ℕ) : C(AddCircle curvePeriod, Ω) :=
      ⟨fun z => ⟨(Rn j t z, Pn j t z), hguardn j t ht z⟩,
        ((Rn j t).continuous.prodMk (Pn j t).continuous).subtype_mk _⟩
    let q : C(AddCircle curvePeriod, Ω) :=
      ⟨fun z => ⟨(r t z, p t z), hguard t ht z⟩,
        ((r t).continuous.prodMk (p t).continuous).subtype_mk _⟩
    let inc : C(Ω, W × W) := ⟨Subtype.val, continuous_subtype_val⟩
    have hq : Tendsto qn atTop (𝓝 q) :=
      (inc.isEmbedding_postcomp Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr
        ((hpair.tendsto _).comp ((hR.tendsto_at ht).prodMk_nhds (hP.tendsto_at ht)))
    let zn (j : ℕ) : X := mulC ((Vn j t) ^ 2, Hn j t - (Bc t ht).comp (qn j)) +
      mulC (Wn j t, Sn j t)
    have hz : Tendsto zn atTop (𝓝 (Zc t ht)) :=
      ((hmulC.tendsto _).comp (((hV.tendsto_at ht).pow 2).prodMk_nhds
        ((hH.tendsto_at ht).sub ((Bc t ht).continuous_postcomp.tendsto _ |>.comp hq)))).add
      ((hmulC.tendsto _).comp ((hW.tendsto_at ht).prodMk_nhds (hS.tendsto_at ht)))
    apply hasDerivAt_of_tendstoUniformly
      ((ContinuousMap.tendsto_iff_tendstoUniformly.mp hz).comp
        (fun y : ℝ => (y : AddCircle curvePeriod)))
      (Eventually.of_forall (fun j y => ?_))
      (fun y => (continuous_eval_const (y : AddCircle curvePeriod)).tendsto (p t)
        |>.comp (hP.tendsto_at ht)) x
    have hqspace := (m63C2_of_m62 (hcn j)).spatial_regular t ht
    have hd := (((hdata j).1 t ht).deriv' (n := 1)).differentiable (by norm_num) y
    have heq : (fun y : ℝ => Pn j t (y : AddCircle curvePeriod)) =
        deriv (fun y => e (cn j y t)) := by
      funext y
      exact (hfirstn j t ht y).deriv.symm.trans
        (congrArg (fun f : ℝ → W => deriv f y) (funext (hRrep j t ht)))
    change HasDerivAt (fun y : ℝ => Pn j t (y : AddCircle curvePeriod)) _ y
    rw [heq]
    apply hd.hasDerivAt.congr_deriv
    rw [hraw (cn j) hqspace ((hcn j).immersed t ht) y]
    change _ = Vn j t (y : AddCircle curvePeriod) ^ 2 •
      (Hn j t (y : AddCircle curvePeriod) - ambientCurveLower F e ρ t
        (Rn j t (y : AddCircle curvePeriod)) (Pn j t (y : AddCircle curvePeriod))) +
      Wn j t (y : AddCircle curvePeriod) • Sn j t (y : AddCircle curvePeriod)
    rw [hVrep j t ht, hHrep j t ht, hRrep j t ht, hWrep j t ht, hSrep j t ht,
      congrFun heq y]
  have hpC1 (t : ℝ) (ht : t ∈ Icc a b) :
      ContDiff ℝ 1 (fun x : ℝ => p t (x : AddCircle curvePeriod)) := by
    apply contDiff_one_iff_hasFDerivAt.mpr
    refine ⟨fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (Zc t ht (x : AddCircle curvePeriod)),
      (ContinuousLinearMap.smulRightL ℝ ℝ W 1).continuous.comp
        ((Zc t ht).continuous.comp (AddCircle.continuous_mk' curvePeriod)), ?_⟩
    exact fun x => (hsecond t ht x).hasFDerivAt
  have hrC2 (t : ℝ) (ht : t ∈ Icc a b) :
      ContDiff ℝ 2 (fun x : ℝ => r t (x : AddCircle curvePeriod)) := by
    apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
    exact ⟨fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (p t (x : AddCircle curvePeriod)),
      (ContinuousLinearMap.smulRightL ℝ ℝ W 1).contDiff.comp (hpC1 t ht),
      fun x => (hfirst t ht x).hasFDerivAt⟩
  have hcC2 (t : ℝ) (ht : t ∈ Icc a b) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun x => c x t) :=
    (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp_contMDiff
      (hrC2 t ht).contMDiff (hrU t ht)
  have hcurv (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) =
        h t (x : AddCircle curvePeriod) := by
    have hacc := hraw c (hcC2 t ht) (himm t ht) x
    have heq : (fun y => e (c y t)) = (fun y : ℝ => r t (y : AddCircle curvePeriod)) :=
      funext (hrfix t ht)
    have hder : deriv (fun y : ℝ => r t (y : AddCircle curvePeriod)) =
        (fun y : ℝ => p t (y : AddCircle curvePeriod)) := funext fun y => (hfirst t ht y).deriv
    rw [heq, hder, (hsecond t ht x).deriv, hspeed t ht x, hgrad t ht x,
      hpushS t ht x, hrfix t ht x] at hacc
    change (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t)
      (m62CurvatureVector F c t x) : W) = (h t (x : AddCircle curvePeriod) : W)
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z : W => z i) hacc
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hi ⊢
    have hi' := add_right_cancel hi
    have hi'' := mul_left_cancel₀ (pow_ne_zero 2 (hvpos t ht x).ne') hi'
    change (h t (x : AddCircle curvePeriod)).ofLp i -
        (ambientCurveLower F e ρ t (r t (x : AddCircle curvePeriod))
          (p t (x : AddCircle curvePeriod))).ofLp i =
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t)
        (m62CurvatureVector F c t x) : W).ofLp i -
        (ambientCurveLower F e ρ t (r t (x : AddCircle curvePeriod))
          (p t (x : AddCircle curvePeriod))).ofLp i at hi''
    exact (sub_left_inj.mp hi'').symm
  have liftUniform (fn : ℕ → ℝ → X) (f : ℝ → X)
      (hf : TendstoUniformlyOn fn f atTop (Icc a b)) :
      TendstoUniformlyOn (fun (j : ℕ) (z : ℝ × ℝ) => fn j z.2 (z.1 : AddCircle curvePeriod))
        (fun z : ℝ × ℝ => f z.2 (z.1 : AddCircle curvePeriod)) atTop (univ ×ˢ Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hf ε hε] with j hj
    intro z hz
    exact (ContinuousMap.dist_apply_le_dist (f := f z.2) (g := fn j z.2)
      (z.1 : AddCircle curvePeriod)).trans_lt (hj z.2 hz.2)
  let L1 : W →L[ℝ] ((ℝ × ℝ) →L[ℝ] W) :=
    ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) W (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let L2 : W →L[ℝ] ((ℝ × ℝ) →L[ℝ] W) :=
    ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) W (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let Dn := fun (j : ℕ) (z : ℝ × ℝ) => L1 (Pn j z.2 (z.1 : AddCircle curvePeriod)) +
    L2 (Hn j z.2 (z.1 : AddCircle curvePeriod))
  let D := fun z : ℝ × ℝ => L1 (p z.2 (z.1 : AddCircle curvePeriod)) +
    L2 (h z.2 (z.1 : AddCircle curvePeriod))
  let O := (univ ×ˢ Ioo a b : Set (ℝ × ℝ))
  have hO : IsOpen O := isOpen_univ.prod isOpen_Ioo
  have hDlim : TendstoUniformlyOn Dn D atTop O :=
    ((L1.uniformContinuous.comp_tendstoUniformlyOn (liftUniform Pn p hP)).add
      (L2.uniformContinuous.comp_tendstoUniformlyOn (liftUniform Hn h hH))).mono
        (prod_mono_right Ioo_subset_Icc_self)
  have hDcont : ContinuousOn D O :=
    ((L1.continuous.comp_continuousOn (liftCont p hp)).add
      (L2.continuous.comp_continuousOn (liftCont h hh))).mono
        (prod_mono_right Ioo_subset_Icc_self)
  have hDactual (j : ℕ) (z : ℝ × ℝ) (hz : z ∈ O) :
      HasFDerivAt (fun w : ℝ × ℝ => Rn j w.2 (w.1 : AddCircle curvePeriod)) (Dn j z) z := by
    have hd0 := ((htimeData j).1.contDiffAt
      ((isOpen_univ.prod isOpen_interior).mem_nhds
        ⟨mem_univ _, by simpa only [interior_Icc] using hz.2⟩)).differentiableAt (by norm_num)
    have hd := hd0.hasFDerivAt
    have hdx := (hd.comp_hasDerivAt z.1 ((hasDerivAt_id z.1).prodMk
      (hasDerivAt_const z.1 z.2))).unique (by
        simpa +instances only [Function.comp_def, id_eq] using!
          (hdata j).2.1 z.2 (Ioo_subset_Icc_self hz.2) z.1)
    have hdt := (hd.comp_hasDerivAt z.2 ((hasDerivAt_const z.2 z.1).prodMk
      (hasDerivAt_id z.2))).unique (by
        simpa +instances only [Function.comp_def, id_eq] using!
          ((htimeData j).2 z.2 (by simpa only [interior_Icc] using hz.2) z.1))
    have hdx' : fderiv ℝ (fun w : ℝ × ℝ => e (cn j w.1 w.2)) z (1, 0) =
        Pn j z.2 (z.1 : AddCircle curvePeriod) := by
      have hfirstj := hfirstn j z.2 (Ioo_subset_Icc_self hz.2) z.1
      have hhj := hfirstj.congr_of_eventuallyEq
        (Eventually.of_forall (fun y => (hRrep j z.2 (Ioo_subset_Icc_self hz.2) y).symm))
      exact hdx.trans (((hdata j).2.1 z.2 (Ioo_subset_Icc_self hz.2) z.1).unique hhj)
    have hdt' : fderiv ℝ (fun w : ℝ × ℝ => e (cn j w.1 w.2)) z (0, 1) =
        Hn j z.2 (z.1 : AddCircle curvePeriod) :=
      hdt.trans (hHrep j z.2 (Ioo_subset_Icc_self hz.2) z.1).symm
    have hlinear : fderiv ℝ (fun w : ℝ × ℝ => e (cn j w.1 w.2)) z = Dn j z := by
      apply ContinuousLinearMap.ext
      intro w
      rw [show w = w.1 • (1, 0) + w.2 • (0, 1) by ext <;> simp]
      simp only [map_add, map_smul, hdx', hdt']
      simp [Dn, L1, L2]
    apply (hd.congr_fderiv hlinear).congr_of_eventuallyEq
    filter_upwards [hO.mem_nhds hz] with w hw
    exact hRrep j w.2 (Ioo_subset_Icc_self hw.2) w.1
  have hDlimit (z : ℝ × ℝ) (hz : z ∈ O) :
      HasFDerivAt (fun w : ℝ × ℝ => r w.2 (w.1 : AddCircle curvePeriod)) (D z) z :=
    hasFDerivAt_of_tendstoUniformlyOn hO hDlim hDactual
      (fun w hw => (continuous_eval_const (w.1 : AddCircle curvePeriod)).tendsto (r w.2)
        |>.comp (hR.tendsto_at (Ioo_subset_Icc_self hw.2))) hz
  have hrjoint : ContDiffOn ℝ 1
      (fun z : ℝ × ℝ => r z.2 (z.1 : AddCircle curvePeriod)) O := by
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0)
      hO.uniqueDiffOn).mpr
    exact ⟨by norm_num, D, contDiffOn_zero.mpr hDcont,
      fun z hz => (hDlimit z hz).hasFDerivWithinAt⟩
  have htime (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (fun u => r u (x : AddCircle curvePeriod))
        (h t (x : AddCircle curvePeriod)) t := by
    have hd := (hDlimit (x, t) ⟨mem_univ _, ht⟩).comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
    simpa +instances [D, L1, L2, Function.comp_def] using! hd
  have hcjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) 1
      (fun z : ℝ × ℝ => c z.1 z.2) O :=
    (hρ.of_le (by norm_num)).comp hrjoint.contMDiffOn
      (fun z hz => hrU z.2 (Ioo_subset_Icc_self hz.2) z.1)
  have hccont : ContinuousOn (fun z : ℝ × ℝ => c z.1 z.2) (univ ×ˢ Icc a b) :=
    hρ.continuousOn.comp (liftCont r hr) (fun z hz => hrU z.2 hz.2 z.1)
  have hcactual : M63C2ShrinkingCurveOn F c (Icc a b) := by
    refine ⟨Subset.rfl, ?_, hcC2, ?_, himm, hccont, ?_, ?_, ?_⟩
    · intro t _ x
      simp only [c, AddCircle.coe_add_period]
    · simpa only [interior_Icc] using hcjoint
    · apply continuousOn_tangentSection_of_retraction_pushforward he hU heU hρ hρe
        (fun z : ℝ × ℝ => c z.1 z.2)
        (fun z => curveVelocity (fun y => c y z.2) z.1) hccont
      exact (liftCont p hp).congr (fun z hz => hpush z.2 hz.2 z.1)
    · apply continuousOn_tangentSection_of_retraction_pushforward he hU heU hρ hρe
        (fun z : ℝ × ℝ => c z.1 z.2)
        (fun z => m62CurvatureVector F c z.2 z.1) hccont
      exact (liftCont h hh).congr (fun z hz => hcurv z.2 hz.2 z.1)
    · intro t ht x
      have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      have hd := htime t ht' x
      have hchain := mfderiv_comp t
        ((hρ.contMDiffAt (hU.mem_nhds (hrU t (Ioo_subset_Icc_self ht') x))).mdifferentiableAt
          (by simp)) hd.differentiableAt.mdifferentiableAt
      have hval := congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡 n) (c x t) => L 1) hchain
      rw [mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv] at hval
      change curveVelocity (fun u => c x u) t =
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
          ((1 : ℝ) • h t (x : AddCircle curvePeriod)) at hval
      have hval' : curveVelocity (fun u => c x u) t =
          mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
            (h t (x : AddCircle curvePeriod)) := by
        simpa only [one_smul] using! hval
      rw [← hcurv t (Ioo_subset_Icc_self ht') x, ← hrfix t (Ioo_subset_Icc_self ht') x,
        hleft] at hval'
      exact hval'
  refine ⟨hcactual, fun t ht x => ⟨hfirst t ht x, hsecond t ht x,
    hspeed t ht x, hgrad t ht x, hcurv t ht x⟩, htime, ?_⟩
  intro ε hε
  obtain ⟨d, hd, hmod⟩ := Metric.continuousWithinAt_iff.mp (hh a ha) ε hε
  refine ⟨d, hd, ?_⟩
  intro t ht htd x
  rw [hcurv t ht x, hcurv a ha x]
  have hdist : dist t a < d := by
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)] using htd
  have hb := (ContinuousMap.dist_apply_le_dist (f := h t) (g := h a)
    (x : AddCircle curvePeriod)).trans_lt (hmod ht hdist)
  simpa only [dist_eq_norm] using! hb

end PoincareConjecture.M63

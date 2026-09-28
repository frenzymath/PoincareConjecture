import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceNormalLimit
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.MixedEmbeddingHessian
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2Locality
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Separation.Basic

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

theorem closed_c2_tail_of_terminal_fields
    [T2Space M] (F : RicciFlow n M (Icc a b))
    {alpha tau T : ℝ} (haa : a ≤ alpha) (hat : alpha < tau)
    (htT : tau < T) (hTb : T ≤ b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U)
    {ρ : W → M} (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    (hρe : ∀ p, ρ (e p) = p)
    {c : ℝ → ℝ → M} (hc : M63C2ShrinkingCurveOn F c (Ico alpha T))
    (r s h : C(Icc tau T, X)) (v g : C(Icc tau T, XR))
    (hrep : ∀ (t : Icc tau T), (t : ℝ) < T → ∀ x : ℝ,
      r t (x : AddCircle curvePeriod) = e (c x t) ∧
      s t (x : AddCircle curvePeriod) =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x) : W) ∧
      h t (x : AddCircle curvePeriod) =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x) : W) ∧
      v t (x : AddCircle curvePeriod) = curveSpeed F c t x ∧
      g t (x : AddCircle curvePeriod) = deriv (curveSpeed F c t) x)
    (hrange : ∀ (t : Icc tau T) z, r t z ∈ range e)
    (hvpos : ∀ (t : Icc tau T) z, 0 < v t z)
    (hfirst : ∀ (t : Icc tau T) (x : ℝ), HasDerivAt
      (fun y : ℝ => r t (y : AddCircle curvePeriod))
      (v t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod)) x)
    (hsecond : ∀ (t : Icc tau T) (x : ℝ), HasDerivAt
      (fun y : ℝ => v t (y : AddCircle curvePeriod) • s t (y : AddCircle curvePeriod))
      (HAdd.hAdd (α := W) (β := W) (γ := W)
        (g t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod))
        (v t (x : AddCircle curvePeriod) ^ 2 •
          HAdd.hAdd (α := W) (β := W) (γ := W)
            (h t (x : AddCircle curvePeriod))
            (coordinateHessian (F.connection t) e (ρ (r t (x : AddCircle curvePeriod)))
              (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
                (s t (x : AddCircle curvePeriod)))
              (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r t (x : AddCircle curvePeriod))
                (s t (x : AddCircle curvePeriod)))))) x)
    (hvder : ∀ (t : Icc tau T) (x : ℝ), HasDerivAt
      (fun y : ℝ => v t (y : AddCircle curvePeriod)) (g t (x : AddCircle curvePeriod)) x) :
    ∃ d : ℝ → ℝ → M, M63C2ShrinkingCurveOn F d (Icc tau T) ∧
      ∀ t, t ∈ Ico tau T → ∀ x, d x t = c x t := by
  classical
  let : Fact (0 < curvePeriod) := ⟨Real.two_pi_pos⟩
  let pi : ℝ → Icc tau T := projIcc tau T htT.le
  have hpi : Continuous pi := continuous_projIcc
  have hpi_eq (t : ℝ) (ht : t ∈ Icc tau T) : pi t = ⟨t, ht⟩ :=
    projIcc_of_mem htT.le ht
  let R := fun t => r (pi t)
  let S := fun t => s (pi t)
  let H := fun t => h (pi t)
  let V := fun t => v (pi t)
  let G := fun t => g (pi t)
  let d := fun (x t : ℝ) => ρ (R t (x : AddCircle curvePeriod))
  have hR : Continuous R := r.continuous.comp hpi
  have hS : Continuous S := s.continuous.comp hpi
  have hH : Continuous H := h.continuous.comp hpi
  have hV : Continuous V := v.continuous.comp hpi
  have hpos (t : ℝ) (z : AddCircle curvePeriod) : 0 < V t z := hvpos (pi t) z
  have hRU (t : ℝ) (z : AddCircle curvePeriod) : R t z ∈ U := heU (hrange (pi t) z)
  have htime : Icc tau T ⊆ Icc a b := Icc_subset_Icc (haa.trans hat.le) hTb
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hfix (t x : ℝ) : e (d x t) = R t (x : AddCircle curvePeriod) := by
    obtain ⟨p, hp⟩ := hrange (pi t) (x : AddCircle curvePeriod)
    change e (ρ (r (pi t) (x : AddCircle curvePeriod))) = _
    rw [← hp, hρe]
  have hagree (t : ℝ) (ht : t ∈ Ico tau T) (x : ℝ) : d x t = c x t := by
    dsimp only [d, R]
    rw [hpi_eq t (Ico_subset_Icc_self ht), (hrep ⟨t, Ico_subset_Icc_self ht⟩ ht.2 x).1, hρe]
  have liftW (f : ℝ → X) (hf : Continuous f) :
      Continuous (fun z : ℝ × ℝ => f z.2 (z.1 : AddCircle curvePeriod)) :=
    (hf.comp continuous_snd).eval ((AddCircle.continuous_mk' curvePeriod).comp continuous_fst)
  have hccont : ContinuousOn (fun z : ℝ × ℝ => d z.1 z.2) (univ ×ˢ Icc tau T) :=
    hρ.continuousOn.comp (liftW R hR).continuousOn (fun z _ => hRU z.2 _)
  let B : (ℝ × W) × (W × W) → W := fun z =>
    coordinateHessian (F.connection z.1.1) e (ρ z.1.2)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.1)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2.2)
  have hB : ContinuousOn B ((Icc a b ×ˢ U) ×ˢ univ) :=
    (flow_coordinateHessian_mixed_pullback_contDiffOn F he hU hρ).continuousOn
  let p : ℝ → X := fun t =>
    ⟨fun z => V t z • S t z, (V t).continuous.smul (S t).continuous⟩
  have hp : Continuous p := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((hV.comp continuous_fst).eval continuous_snd).smul
      ((hS.comp continuous_fst).eval continuous_snd)
  let Z : ℝ → AddCircle curvePeriod → W := fun t z =>
    G t z • S t z + V t z ^ 2 • (H t z + B ((t, R t z), (S t z, S t z)))
  have hZ (t : ℝ) (ht : t ∈ Icc tau T) : Continuous (Z t) := by
    let input : AddCircle curvePeriod → (ℝ × W) × (W × W) :=
      fun z => ((t, R t z), (S t z, S t z))
    have hi : Continuous input :=
      (continuous_const.prodMk (R t).continuous).prodMk
        ((S t).continuous.prodMk (S t).continuous)
    have hm (z : AddCircle curvePeriod) : input z ∈ ((Icc a b ×ˢ U) ×ˢ univ) :=
      ⟨⟨htime ht, hRU t z⟩, mem_univ _⟩
    exact ((G t).continuous.smul (S t).continuous).add
      (((V t).continuous.pow 2).smul ((H t).continuous.add
        (hB.comp_continuous (f := input) hi hm)))
  have hfirst0 (t : ℝ) (ht : t ∈ Icc tau T) (x : ℝ) :
      HasDerivAt (fun y : ℝ => R t (y : AddCircle curvePeriod))
        (p t (x : AddCircle curvePeriod)) x := by
    simpa only [R, p, V, S, hpi_eq t ht, ContinuousMap.coe_mk] using hfirst ⟨t, ht⟩ x
  have hsecond0 (t : ℝ) (ht : t ∈ Icc tau T) (x : ℝ) :
      HasDerivAt (fun y : ℝ => p t (y : AddCircle curvePeriod))
        (Z t (x : AddCircle curvePeriod)) x := by
    have htv : (pi t : ℝ) = t := congrArg Subtype.val (hpi_eq t ht)
    have hb : B ((t, R t (x : AddCircle curvePeriod)),
        (S t (x : AddCircle curvePeriod), S t (x : AddCircle curvePeriod))) =
        B (((pi t : ℝ), R t (x : AddCircle curvePeriod)),
          (S t (x : AddCircle curvePeriod), S t (x : AddCircle curvePeriod))) :=
      congrArg (fun u : ℝ => B ((u, R t (x : AddCircle curvePeriod)),
        (S t (x : AddCircle curvePeriod), S t (x : AddCircle curvePeriod)))) htv.symm
    dsimp only [Z]
    rw [hb]
    simpa +instances only [p, B, R, V, S, H, G, ContinuousMap.coe_mk] using!
      hsecond (pi t) x
  have hpC1 (t : ℝ) (ht : t ∈ Icc tau T) :
      ContDiff ℝ 1 (fun x : ℝ => p t (x : AddCircle curvePeriod)) := by
    apply contDiff_one_iff_hasFDerivAt.mpr
    exact ⟨fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (Z t (x : AddCircle curvePeriod)),
      (ContinuousLinearMap.smulRightL ℝ ℝ W 1).continuous.comp
        ((hZ t ht).comp (AddCircle.continuous_mk' curvePeriod)),
      fun x => (hsecond0 t ht x).hasFDerivAt⟩
  have hRC2 (t : ℝ) (ht : t ∈ Icc tau T) :
      ContDiff ℝ 2 (fun x : ℝ => R t (x : AddCircle curvePeriod)) := by
    apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
    exact ⟨fun x => (1 : ℝ →L[ℝ] ℝ).smulRight (p t (x : AddCircle curvePeriod)),
      (ContinuousLinearMap.smulRightL ℝ ℝ W 1).contDiff.comp (hpC1 t ht),
      fun x => (hfirst0 t ht x).hasFDerivAt⟩
  have hdC2 (t : ℝ) (ht : t ∈ Icc tau T) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun x => d x t) :=
    (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp_contMDiff
      (hRC2 t ht).contMDiff (fun x => hRU t (x : AddCircle curvePeriod))
  have hmetric := (flow_pullback_metric_hessian_contDiffOn F hU hρ
    (f := fun _ => 0) contMDiff_const).1.continuousOn
  have hunit (t : ℝ) (ht : t ∈ Icc tau T) (x : ℝ) :
      (F.metric t).inner (d x t)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (R t (x : AddCircle curvePeriod))
          (S t (x : AddCircle curvePeriod)))
        (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (R t (x : AddCircle curvePeriod))
          (S t (x : AddCircle curvePeriod))) = 1 := by
    let f : ℝ → ℝ := fun u => (F.metric u).inner (d x u)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (R u (x : AddCircle curvePeriod))
        (S u (x : AddCircle curvePeriod)))
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (R u (x : AddCircle curvePeriod))
        (S u (x : AddCircle curvePeriod)))
    have hf : ContinuousOn f (Icc tau T) :=
      hmetric.comp ((continuous_id.prodMk ((continuous_eval_const
        (x : AddCircle curvePeriod)).comp hR)).prodMk
          ((continuous_eval_const (x : AddCircle curvePeriod)).comp hS)).continuousOn
        (fun u hu => ⟨⟨htime hu, hRU u _⟩, mem_univ _⟩)
    apply ((hf t ht).mono Ico_subset_Icc_self).eq_const_of_mem_closure
      (by rw [closure_Ico htT.ne]; exact ht)
    intro u hu
    obtain ⟨hru, hsu, _hhu, hvu, _hgu⟩ :=
      hrep ⟨u, Ico_subset_Icc_self hu⟩ hu.2 x
    have hvu0 : curveSpeed F c u x ≠ 0 := by
      rw [← hvu]
      exact (hvpos ⟨u, Ico_subset_Icc_self hu⟩ _).ne'
    have huc : (F.metric u).inner (c x u) (spatialUnitTangent F c u x)
        (spatialUnitTangent F c u x) = 1 := by
      simp only [spatialUnitTangent, map_smul, smul_apply, smul_eq_mul]
      rw [← speed_sq F c u x]
      field_simp [hvu0]
    let metricValue : W × W → ℝ := fun z => (F.metric u).inner (ρ z.1)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2)
    have hru' : R u (x : AddCircle curvePeriod) = e (c x u) := by
      dsimp only [R]
      rw [hpi_eq u (Ico_subset_Icc_self hu)]
      exact hru
    have hsu' : S u (x : AddCircle curvePeriod) =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x u) (spatialUnitTangent F c u x) : W) := by
      dsimp only [S]
      rw [hpi_eq u (Ico_subset_Icc_self hu)]
      exact hsu
    change metricValue (R u (x : AddCircle curvePeriod), S u (x : AddCircle curvePeriod)) = 1
    rw [hru', hsu']
    dsimp only [metricValue]
    erw [hleft, hρe]
    exact huc
  have hvel (t : ℝ) (ht : t ∈ Icc tau T) (x : ℝ) :
      curveVelocity (fun y => d y t) x = V t (x : AddCircle curvePeriod) •
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (R t (x : AddCircle curvePeriod))
          (S t (x : AddCircle curvePeriod)) := by
    have hchain := mfderiv_comp x
      ((hρ.contMDiffAt (hU.mem_nhds (hRU t _))).mdifferentiableAt (by simp))
      (hfirst0 t ht x).differentiableAt.mdifferentiableAt
    have hv := congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡 n) (d x t) => L 1) hchain
    rw [mfderiv_eq_fderiv, (hfirst0 t ht x).hasFDerivAt.fderiv] at hv
    change curveVelocity (fun y => d y t) x =
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (R t (x : AddCircle curvePeriod))
        ((1 : ℝ) • p t (x : AddCircle curvePeriod)) at hv
    simpa only [one_smul, p, ContinuousMap.coe_mk, map_smul] using! hv
  have himm (t : ℝ) (ht : t ∈ Icc tau T) (x : ℝ) :
      (curveVelocity (fun y => d y t) x : TangentSpace (𝓡 n) (d x t)) ≠ 0 := by
    have hv := hvel t ht x
    rw [hv]
    apply smul_ne_zero (hpos t _).ne'
    intro hz
    simpa [hz] using hunit t ht x
  have hspeed (t : ℝ) (ht : t ∈ Icc tau T) (x : ℝ) :
      curveSpeed F d t x = V t (x : AddCircle curvePeriod) := by
    change Real.sqrt ((F.metric t).inner (d x t)
      (curveVelocity (fun y => d y t) x) (curveVelocity (fun y => d y t) x)) = _
    rw [hvel t ht x]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [hunit t ht x]
    simp only [mul_one]
    rw [← pow_two, Real.sqrt_sq (hpos t _).le]
  have hgrad (t : ℝ) (ht : t ∈ Icc tau T) (x : ℝ) :
      deriv (curveSpeed F d t) x = G t (x : AddCircle curvePeriod) := by
    rw [show curveSpeed F d t = (fun y : ℝ => V t (y : AddCircle curvePeriod)) from
      funext (hspeed t ht)]
    simpa only [V, G, hpi_eq t ht] using (hvder ⟨t, ht⟩ x).deriv
  have hpush (t : ℝ) (ht : t ∈ Icc tau T) (x : ℝ) :
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (d x t)
        (curveVelocity (fun y => d y t) x) : W) = p t (x : AddCircle curvePeriod) := by
    have hdc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun y => d y t) :=
      (hdC2 t ht).of_le (by norm_num)
    have hd := (((he.of_le (by norm_num)).comp hdc).contDiff.differentiable
      (by norm_num) x).hasDerivAt
    have hchain := mfderiv_comp x (he.mdifferentiable (by simp)).mdifferentiableAt
      ((hdc x).mdifferentiableAt (by norm_num))
    rw [mfderiv_eq_fderiv] at hchain
    have hde := hd.congr_deriv (congrArg (fun L : ℝ →L[ℝ] W => L 1) hchain)
    exact (hde.congr_of_eventuallyEq
      (Eventually.of_forall (fun y => (hfix t y).symm))).unique (hfirst0 t ht x)
  have hcurv (t : ℝ) (ht : t ∈ Icc tau T) (x : ℝ) :
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (d x t)
        (m62CurvatureVector F d t x) : W) = H t (x : AddCircle curvePeriod) := by
    let v0 := V t (x : AddCircle curvePeriod)
    let S0 : TangentSpace (𝓡 n) (d x t) :=
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (R t (x : AddCircle curvePeriod))
        (S t (x : AddCircle curvePeriod))
    have hv0 : v0 ≠ 0 := (hpos t _).ne'
    have hscale : coordinateHessian (F.connection t) e (d x t) (v0 • S0) (v0 • S0) =
        v0 ^ 2 • coordinateHessian (F.connection t) e (d x t) S0 S0 := by
      ext i
      have hei : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun q => e q i) :=
        (EuclideanSpace.proj i).contDiff.contMDiff.comp he
      obtain ⟨L, hL⟩ := (M04.isSmoothCovariantTensor_hessian (F.connection t) hei).1 (d x t)
      have h0 (Y Q : TangentSpace (𝓡 n) (d x t)) :
          Function.update ![S0, Q] 0 Y = ![Y, Q] := by
        ext k
        fin_cases k <;> simp [Function.update]
      have h1 (Y : TangentSpace (𝓡 n) (d x t)) :
          Function.update ![S0, S0] 1 Y = ![S0, Y] := by
        ext k
        fin_cases k <;> simp [Function.update]
      have hfst : (F.connection t).hessian (fun q => e q i) (d x t) (v0 • S0) (v0 • S0) =
          v0 * (F.connection t).hessian (fun q => e q i) (d x t) S0 (v0 • S0) := by
        simpa only [h0, ← hL, smul_eq_mul] using! L.map_update_smul ![S0, v0 • S0] 0 v0 S0
      have hsnd : (F.connection t).hessian (fun q => e q i) (d x t) S0 (v0 • S0) =
          v0 * (F.connection t).hessian (fun q => e q i) (d x t) S0 S0 := by
        simpa only [h1, ← hL, smul_eq_mul] using! L.map_update_smul ![S0, S0] 1 v0 S0
      change (F.connection t).hessian (fun q => e q i) (d x t) (v0 • S0) (v0 • S0) =
        v0 ^ 2 * (F.connection t).hessian (fun q => e q i) (d x t) S0 S0
      rw [hfst, hsnd]
      ring
    have hacc := embedded_curvature_eq_acceleration_sub_tangent F he d
      (hdC2 t ht) (himm t ht) x
    have heq : (fun y => e (d y t)) = (fun y : ℝ => R t (y : AddCircle curvePeriod)) :=
      funext (hfix t)
    have hder : deriv (fun y : ℝ => R t (y : AddCircle curvePeriod)) =
        (fun y : ℝ => p t (y : AddCircle curvePeriod)) :=
      funext (fun y => (hfirst0 t ht y).deriv)
    rw [hvel t ht x, hscale, heq, hder, (hsecond0 t ht x).deriv,
      hspeed t ht x, hgrad t ht x] at hacc
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z : W => z i) hacc
    simp only [Z, p, ContinuousMap.coe_mk, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul] at hi
    change _ = (v0 ^ 2)⁻¹ *
      (G t (x : AddCircle curvePeriod) * (S t (x : AddCircle curvePeriod)).ofLp i +
        v0 ^ 2 * ((H t (x : AddCircle curvePeriod)).ofLp i +
          (coordinateHessian (F.connection t) e (d x t) S0 S0).ofLp i) -
        v0 ^ 2 * (coordinateHessian (F.connection t) e (d x t) S0 S0).ofLp i) -
      (G t (x : AddCircle curvePeriod) / v0 ^ 3) *
        (v0 * (S t (x : AddCircle curvePeriod)).ofLp i) at hi
    field_simp [hv0] at hi
    apply mul_right_cancel₀ (pow_ne_zero 2 hv0)
    nlinarith only [hi]
  have hjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) 1
      (fun z : ℝ × ℝ => d z.1 z.2) (univ ×ˢ Ioo tau T) := by
    apply (hc.joint_c1.mono ?_).congr (fun z hz => hagree z.2
      (Ioo_subset_Ico_self hz.2) z.1)
    rw [interior_Ico]
    exact fun z hz => ⟨mem_univ _, hat.trans hz.2.1, hz.2.2⟩
  refine ⟨d, ?_, hagree⟩
  refine ⟨htime, ?_, hdC2, ?_, himm, hccont, ?_, ?_, ?_⟩
  · intro t _ x
    simp only [d, AddCircle.coe_add_period]
  · simpa only [interior_Icc] using hjoint
  · apply continuousOn_tangentSection_of_retraction_pushforward he hU heU hρ hρe
      (fun z : ℝ × ℝ => d z.1 z.2)
      (fun z => curveVelocity (fun y => d y z.2) z.1) hccont
    exact (liftW p hp).continuousOn.congr (fun z hz => hpush z.2 hz.2 z.1)
  · apply continuousOn_tangentSection_of_retraction_pushforward he hU heU hρ hρe
      (fun z : ℝ × ℝ => d z.1 z.2) (fun z => m62CurvatureVector F d z.2 z.1) hccont
    exact (liftW H hH).continuousOn.congr (fun z hz => hcurv z.2 hz.2 z.1)
  · intro t ht x
    rw [interior_Icc] at ht
    have heq : (fun u => d x u) =ᶠ[𝓝 t] (fun u => c x u) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
      exact hagree u (Ioo_subset_Ico_self hu) x
    have hvelocity : curveVelocity (n := n) (fun u => d x u) t =
        curveVelocity (n := n) (fun u => c x u) t := by
      unfold curveVelocity
      rw [heq.mfderiv_eq]
      rfl
    have hslice : (fun y => d y t) = (fun y => c y t) :=
      funext (hagree t (Ioo_subset_Ico_self ht))
    have hcurvature : m62CurvatureVector F d t x = m62CurvatureVector F c t x :=
      congrArg (fun q : ℝ → M => m62CurvatureVector F (fun y _ => q y) t x) hslice
    rw [hvelocity, hcurvature]
    exact hc.equation t (by rw [interior_Ico]; exact ⟨hat.trans ht.1, ht.2⟩) x

end PoincareConjecture.M63

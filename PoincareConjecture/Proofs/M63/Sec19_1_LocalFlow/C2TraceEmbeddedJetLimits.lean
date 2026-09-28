import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessAmbientAcceleration
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessEmbeddedCurve
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import PoincareConjecture.Proofs.M04.ScalarHessian
import Mathlib.Topology.ContinuousMap.Compact










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)
local notation "XR" => C(AddCircle curvePeriod, ℝ)

set_option maxHeartbeats 800000 in




theorem exists_closed_embedded_threeJet_limits
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (c : ℕ → ℝ → ℝ → M) (c0 : ℝ → ℝ → M)
    (hc : ∀ j, M63C2ShrinkingCurveOn F (c j) (Icc a b))
    (hc0 : M63C2ShrinkingCurveOn F c0 (Icc a b))
    (R S H : ℕ → C(Icc a b, X)) (V G : ℕ → C(Icc a b, XR))
    (r s h : C(Icc a b, X)) (v g : C(Icc a b, XR))
    (hR : Tendsto R atTop (𝓝 r)) (hS : Tendsto S atTop (𝓝 s))
    (hH : Tendsto H atTop (𝓝 h)) (hV : Tendsto V atTop (𝓝 v))
    (hG : Tendsto G atTop (𝓝 g))
    (hRrep : ∀ j (t : Icc a b) (x : ℝ),
      R j t (x : AddCircle curvePeriod) = e (c j x t))
    (hSrep : ∀ j (t : Icc a b) (x : ℝ), S j t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (spatialUnitTangent F (c j) t x))
    (hHrep : ∀ j (t : Icc a b) (x : ℝ), H j t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c j x t) (m62CurvatureVector F (c j) t x))
    (hVrep : ∀ j (t : Icc a b) (x : ℝ),
      V j t (x : AddCircle curvePeriod) = curveSpeed F (c j) t x)
    (hGrep : ∀ j (t : Icc a b) (x : ℝ),
      G j t (x : AddCircle curvePeriod) = deriv (curveSpeed F (c j) t) x)
    (hrrep : ∀ (t : Icc a b) (x : ℝ), r t (x : AddCircle curvePeriod) = e (c0 x t))
    (hsrep : ∀ (t : Icc a b) (x : ℝ), s t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c0 x t) (spatialUnitTangent F c0 t x))
    (hhrep : ∀ (t : Icc a b) (x : ℝ), h t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c0 x t) (m62CurvatureVector F c0 t x))
    (hvrep : ∀ (t : Icc a b) (x : ℝ),
      v t (x : AddCircle curvePeriod) = curveSpeed F c0 t x)
    (hgrep : ∀ (t : Icc a b) (x : ℝ),
      g t (x : AddCircle curvePeriod) = deriv (curveSpeed F c0 t) x) :
    let B := fun t z p => coordinateHessian (F.connection t) e (ρ z)
      (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z p) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z p)
    ∃ (D Z : ℕ → C(Icc a b, X)) (d z : C(Icc a b, X)),
      Tendsto D atTop (𝓝 d) ∧ Tendsto Z atTop (𝓝 z) ∧
      (∀ j (t : Icc a b) (x : ℝ),
        D j t (x : AddCircle curvePeriod) = deriv (fun y => e (c j y t)) x ∧
        Z j t (x : AddCircle curvePeriod) = deriv (deriv (fun y => e (c j y t))) x) ∧
      (∀ (t : Icc a b) (x : ℝ),
        d t (x : AddCircle curvePeriod) = deriv (fun y => e (c0 y t)) x ∧
        z t (x : AddCircle curvePeriod) = deriv (deriv (fun y => e (c0 y t))) x) ∧
      (∀ j (t : Icc a b) y, D j t y = V j t y • S j t y ∧
        Z j t y = G j t y • S j t y + (V j t y) ^ 2 •
          (H j t y + B t (R j t y) (S j t y))) ∧
      (∀ (t : Icc a b) y, d t y = v t y • s t y ∧
        z t y = g t y • s t y + (v t y) ^ 2 • (h t y + B t (r t y) (s t y))) ∧
      ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ (t : Icc a b) (x : ℝ),
        ‖e (c j x t) - e (c0 x t)‖ < ε ∧
        ‖deriv (fun y => e (c j y t)) x - deriv (fun y => e (c0 y t)) x‖ < ε ∧
        ‖deriv (deriv (fun y => e (c j y t))) x -
          deriv (deriv (fun y => e (c0 y t))) x‖ < ε := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  dsimp only
  let B : ℝ → W → W → W := fun t z p => coordinateHessian (F.connection t) e (ρ z)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z p) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z p)
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hBval (t : ℝ) (p : M) (Y : TangentSpace (𝓡 n) p) :
      B t (e p) (mfderiv (𝓡 n) 𝓘(ℝ, W) e p Y) =
        coordinateHessian (F.connection t) e p Y Y := by
    dsimp only [B]
    rw [hleft, hρe]
  have hjet (q : ℝ → ℝ → M) (hq : M63C2ShrinkingCurveOn F q (Icc a b))
      (t : Icc a b) (x : ℝ) :
      deriv (fun y => e (q y t)) x = curveSpeed F q t x •
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t) (spatialUnitTangent F q t x) ∧
      deriv (deriv (fun y => e (q y t))) x =
        HAdd.hAdd (α := W) (β := W) (γ := W)
          (deriv (curveSpeed F q t) x •
            mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t) (spatialUnitTangent F q t x))
          (curveSpeed F q t x ^ 2 • HAdd.hAdd (α := W) (β := W) (γ := W)
            (mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t) (m62CurvatureVector F q t x))
            (coordinateHessian (F.connection t) e (q x t)
              (spatialUnitTangent F q t x) (spatialUnitTangent F q t x))) := by
    let v0 := curveSpeed F q t x
    let S0 := spatialUnitTangent F q t x
    have hv0 : v0 ≠ 0 :=
      (Real.sqrt_pos.mpr ((F.metric t).pos _ _ (hq.immersed t t.2 x))).ne'
    have hvel : curveVelocity (fun y => q y t) x = v0 • S0 := by
      dsimp only [S0, spatialUnitTangent]
      rw [smul_smul, mul_inv_cancel₀ hv0, one_smul]
    have hfirst := (c2ShrinkingCurve_embedded_closed_data hq he).2.1 t t.2 x
    rw [hvel, map_smul] at hfirst
    refine ⟨hfirst.deriv, ?_⟩
    have hscale : coordinateHessian (F.connection t) e (q x t)
        (v0 • S0) (v0 • S0) =
        v0 ^ 2 • coordinateHessian (F.connection t) e (q x t) S0 S0 := by
      ext i
      have hei : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun p => e p i) :=
        (EuclideanSpace.proj i).contDiff.contMDiff.comp he
      obtain ⟨L, hL⟩ := (M04.isSmoothCovariantTensor_hessian (F.connection t) hei).1
        (q x t)
      have h0 (Y Z : TangentSpace (𝓡 n) (q x t)) :
          Function.update ![S0, Z] 0 Y = ![Y, Z] := by
        ext k
        fin_cases k <;> simp [Function.update]
      have h1 (Y : TangentSpace (𝓡 n) (q x t)) :
          Function.update ![S0, S0] 1 Y = ![S0, Y] := by
        ext k
        fin_cases k <;> simp [Function.update]
      have hfirstSlot :
          (F.connection t).hessian (fun p => e p i) (q x t) (v0 • S0) (v0 • S0) =
            v0 * (F.connection t).hessian (fun p => e p i) (q x t) S0 (v0 • S0) := by
        simpa only [h0, ← hL, smul_eq_mul] using! L.map_update_smul ![S0, v0 • S0] 0 v0 S0
      have hsecondSlot :
          (F.connection t).hessian (fun p => e p i) (q x t) S0 (v0 • S0) =
            v0 * (F.connection t).hessian (fun p => e p i) (q x t) S0 S0 := by
        simpa only [h1, ← hL, smul_eq_mul] using! L.map_update_smul ![S0, S0] 1 v0 S0
      change (F.connection t).hessian (fun p => e p i) (q x t) (v0 • S0) (v0 • S0) =
        v0 ^ 2 * (F.connection t).hessian (fun p => e p i) (q x t) S0 S0
      rw [hfirstSlot, hsecondSlot]
      ring
    have hcurv := embedded_curvature_eq_acceleration_sub_tangent F he q
      (hq.spatial_regular t t.2) (hq.immersed t t.2) x
    rw [hvel, hscale, hfirst.deriv] at hcurv
    ext i
    have hi := congrArg (fun z : W => z i) hcurv
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hi ⊢
    change _ = deriv (curveSpeed F q t) x * _ + v0 ^ 2 * (_ + _)
    change _ = (v0 ^ 2)⁻¹ * (_ - v0 ^ 2 * _) -
      (deriv (curveSpeed F q t) x / v0 ^ 3) * (v0 * _) at hi
    field_simp [hv0] at hi
    nlinarith [hi]
  let Y := Icc a b × AddCircle curvePeriod
  let E := (Icc a b × U) × W
  have hBC : ContinuousOn (fun z : (ℝ × W) × W => B z.1.1 z.1.2 z.2)
      ((Icc a b ×ˢ U) ×ˢ univ) :=
    (flow_coordinateHessian_pullback_contDiffOn F he hU hρ).continuousOn
  let coefficientInput : E → (ℝ × W) × W :=
    fun z => ((z.1.1.1, z.1.2.1), z.2)
  have hInput : Continuous coefficientInput :=
    (((continuous_subtype_val.comp continuous_fst.fst).prodMk
      (continuous_subtype_val.comp continuous_fst.snd)).prodMk continuous_snd)
  have hInput_mem (z : E) : coefficientInput z ∈ ((Icc a b ×ˢ U) ×ˢ univ) :=
    ⟨⟨z.1.1.2, z.1.2.2⟩, mem_univ _⟩
  let BC : C(E, W) := ⟨fun z => B z.1.1 z.1.2 z.2,
    hBC.comp_continuous (f := coefficientInput) hInput hInput_mem⟩
  have hRU (j : ℕ) (y : Y) : (R j).uncurry y ∈ U := by
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective y.2
    change R j y.1 y.2 ∈ U
    rw [← hx, hRrep]
    exact heU (mem_range_self _)
  have hrU (y : Y) : r.uncurry y ∈ U := by
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective y.2
    change r y.1 y.2 ∈ U
    rw [← hx, hrrep]
    exact heU (mem_range_self _)
  let R0 (j : ℕ) : C(Y, U) :=
    ⟨fun y => ⟨(R j).uncurry y, hRU j y⟩, (R j).uncurry.continuous.subtype_mk _⟩
  let r0 : C(Y, U) := ⟨fun y => ⟨r.uncurry y, hrU y⟩,
    r.uncurry.continuous.subtype_mk _⟩
  let inc : C(U, W) := ⟨Subtype.val, continuous_subtype_val⟩
  have hR0 : Tendsto R0 atTop (𝓝 r0) := by
    apply (inc.isEmbedding_postcomp Topology.IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr
    exact (ContinuousMap.continuous_uncurry.tendsto r).comp hR
  have hS0 := (ContinuousMap.continuous_uncurry.tendsto s).comp hS
  have hH0 := (ContinuousMap.continuous_uncurry.tendsto h).comp hH
  have hV0 := (ContinuousMap.continuous_uncurry.tendsto v).comp hV
  have hG0 := (ContinuousMap.continuous_uncurry.tendsto g).comp hG
  let bundle (q : C(Y, U) × C(Y, W)) : C(Y, E) :=
    ((ContinuousMap.fst : C(Y, Icc a b)).prodMk q.1).prodMk q.2
  have hbundle : Continuous bundle := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.fst.eval continuous_snd)).prodMk
      (continuous_fst.snd.eval continuous_snd)
  let En (j : ℕ) : C(Y, W) := BC.comp (bundle (R0 j, (S j).uncurry))
  let E0 : C(Y, W) := BC.comp (bundle (r0, s.uncurry))
  have hEn : Tendsto En atTop (𝓝 E0) :=
    (BC.continuous_postcomp.tendsto _).comp
      ((hbundle.tendsto _).comp (hR0.prodMk_nhds hS0))
  let mulV (q : C(Y, ℝ) × C(Y, W)) : C(Y, W) :=
    ⟨fun y => q.1 y • q.2 y, q.1.continuous.smul q.2.continuous⟩
  have hmulV : Continuous mulV := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hscalar : Continuous (fun q : (C(Y, ℝ) × C(Y, W)) × Y => q.1.1 q.2) :=
      continuous_fst.fst.eval continuous_snd
    have hvector : Continuous (fun q : (C(Y, ℝ) × C(Y, W)) × Y => q.1.2 q.2) :=
      continuous_fst.snd.eval continuous_snd
    exact hscalar.smul hvector
  let square (q : C(Y, ℝ)) : C(Y, ℝ) := ⟨fun y => (q y) ^ 2, q.continuous.pow 2⟩
  have hsquare : Continuous square := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.eval continuous_snd).pow 2
  let Dn (j : ℕ) : C(Y, W) := mulV ((V j).uncurry, (S j).uncurry)
  let d0 : C(Y, W) := mulV (v.uncurry, s.uncurry)
  let Zn (j : ℕ) : C(Y, W) := mulV ((G j).uncurry, (S j).uncurry) +
    mulV (square (V j).uncurry, (H j).uncurry + En j)
  let z0 : C(Y, W) := mulV (g.uncurry, s.uncurry) +
    mulV (square v.uncurry, h.uncurry + E0)
  have hDn : Tendsto Dn atTop (𝓝 d0) :=
    (hmulV.tendsto _).comp (hV0.prodMk_nhds hS0)
  have hZn : Tendsto Zn atTop (𝓝 z0) :=
    ((hmulV.tendsto _).comp (hG0.prodMk_nhds hS0)).add
      ((hmulV.tendsto _).comp (((hsquare.tendsto _).comp hV0).prodMk_nhds (hH0.add hEn)))
  have hDj (j : ℕ) (t : Icc a b) (x : ℝ) :
      (Dn j).curry t (x : AddCircle curvePeriod) = deriv (fun y => e (c j y t)) x ∧
      (Zn j).curry t (x : AddCircle curvePeriod) =
        deriv (deriv (fun y => e (c j y t))) x := by
    change V j t (x : AddCircle curvePeriod) • S j t (x : AddCircle curvePeriod) = _ ∧
      G j t (x : AddCircle curvePeriod) • S j t (x : AddCircle curvePeriod) +
        (V j t (x : AddCircle curvePeriod)) ^ 2 •
          (H j t (x : AddCircle curvePeriod) +
            B t (R j t (x : AddCircle curvePeriod)) (S j t (x : AddCircle curvePeriod))) = _
    rw [hRrep, hSrep, hHrep, hVrep, hGrep, hBval]
    exact ⟨(hjet (c j) (hc j) t x).1.symm, (hjet (c j) (hc j) t x).2.symm⟩
  have hdj (t : Icc a b) (x : ℝ) :
      d0.curry t (x : AddCircle curvePeriod) = deriv (fun y => e (c0 y t)) x ∧
      z0.curry t (x : AddCircle curvePeriod) = deriv (deriv (fun y => e (c0 y t))) x := by
    change v t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod) = _ ∧
      g t (x : AddCircle curvePeriod) • s t (x : AddCircle curvePeriod) +
        (v t (x : AddCircle curvePeriod)) ^ 2 •
          (h t (x : AddCircle curvePeriod) +
            B t (r t (x : AddCircle curvePeriod)) (s t (x : AddCircle curvePeriod))) = _
    rw [hrrep, hsrep, hhrep, hvrep, hgrep, hBval]
    exact ⟨(hjet c0 hc0 t x).1.symm, (hjet c0 hc0 t x).2.symm⟩
  have hD := (ContinuousMap.continuous_curry.tendsto d0).comp hDn
  have hZ := (ContinuousMap.continuous_curry.tendsto z0).comp hZn
  refine ⟨fun j => (Dn j).curry, fun j => (Zn j).curry, d0.curry, z0.curry,
    hD, hZ, hDj, hdj, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
  intro ε hε
  obtain ⟨NR, hNR⟩ := (Metric.tendsto_atTop (u := R) (a := r)).mp hR ε hε
  obtain ⟨ND, hND⟩ :=
    (Metric.tendsto_atTop (u := fun j => (Dn j).curry) (a := d0.curry)).mp hD ε hε
  obtain ⟨NZ, hNZ⟩ :=
    (Metric.tendsto_atTop (u := fun j => (Zn j).curry) (a := z0.curry)).mp hZ ε hε
  refine ⟨max NR (max ND NZ), ?_⟩
  intro j hj t x
  have hval (f f0 : C(Icc a b, X)) (hf : dist f f0 < ε) :
      ‖f t (x : AddCircle curvePeriod) - f0 t (x : AddCircle curvePeriod)‖ < ε := by
    have hd : dist (f t (x : AddCircle curvePeriod))
        (f0 t (x : AddCircle curvePeriod)) < ε :=
      (ContinuousMap.dist_apply_le_dist (f := f t) (g := f0 t)
        (x : AddCircle curvePeriod)).trans_lt
        ((ContinuousMap.dist_apply_le_dist (f := f) (g := f0) t).trans_lt hf)
    simpa only [dist_eq_norm] using! hd
  have h0 := hval (R j) r (hNR j ((le_max_left _ _).trans hj))
  have h1 := hval (Dn j).curry d0.curry
    (hND j ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hj))
  have h2 := hval (Zn j).curry z0.curry
    (hNZ j ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hj))
  rw [hRrep, hrrep] at h0
  rw [(hDj j t x).1, (hdj t x).1] at h1
  rw [(hDj j t x).2, (hdj t x).2] at h2
  exact ⟨h0, h1, h2⟩

end PoincareConjecture.M63

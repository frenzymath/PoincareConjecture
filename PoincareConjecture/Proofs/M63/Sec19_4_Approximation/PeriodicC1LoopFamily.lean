import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.RawLoopLength
import PoincareConjecture.Proofs.M58.Sec18_4_LoopExtension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Maps.Proper.Basic











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

open Proofs.M58




theorem exists_continuous_c1Loop_family_of_periodic
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {Z : Type v} [TopologicalSpace Z]
    (beta : Z → ℝ → M)
    (hperiod : ∀ z, Function.Periodic (beta z) curvePeriod)
    (hC1 : ∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) 1 (beta z))
    (hvalue : Continuous (fun p : Z × ℝ => beta p.1 p.2))
    (hfirst : Continuous (fun p : Z × ℝ =>
      m63AngularFirstJet (n := 3) (beta p.1) p.2)) :
    ∃ family : C(Z, C1FreeLoopSpace (M := M)),
      ∀ z x, periodicFreeLoop (family z) x = beta z x := by
  let w : LoopPlane →L[ℝ] ℂ := Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    ((EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj (1 : Fin 2)))
  have hw (q : LoopPlane) : w q = (q 0 : ℂ) + (q 1 : ℂ) * Complex.I := by
    simp only [w, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearEquiv.coe_coe, Complex.equivRealProdCLM_symm_apply,
      EuclideanSpace.coe_proj]
  have hw0 {q : LoopPlane} (hq : q ≠ 0) : w q ≠ 0 := by
    intro h
    apply hq
    apply PiLp.ext
    intro i
    fin_cases i
    · have hh := congrArg Complex.re h
      simpa [hw] using hh
    · have hh := congrArg Complex.im h
      simpa [hw] using hh
  have hangle (z : Z) {x y : ℝ} (h : (x : Real.Angle) = (y : Real.Angle)) :
      beta z x = beta z y := by
    exact congrArg (hperiod z).lift h
  let Ext : Z → LoopPlane → M := fun z q => beta z (Complex.arg (w q))
  have hExt (z : Z) : ContMDiffOn (𝓡 2) (𝓡 3) 1 (Ext z) loopAnnulus := by
    intro q hq
    have hq0 : q ≠ 0 := by
      intro h
      have hpos := hq.1
      norm_num [h] at hpos
    have hwq : w q ≠ 0 := hw0 hq0
    let ratio : LoopPlane → ℂ := fun y => w y / w q
    have hratio : ContDiff ℝ 1 ratio := w.contDiff.div_const _
    have hratioq : ratio q = 1 := div_self hwq
    have hlog : ContDiffAt ℝ 1 Complex.log (ratio q) :=
      (Complex.contDiffAt_log
        (show ratio q ∈ Complex.slitPlane by
          rw [hratioq]
          exact Complex.one_mem_slitPlane)).restrict_scalars ℝ
    let A : LoopPlane → ℝ := fun y =>
      Complex.arg (w q) + (Complex.log (ratio y)).im
    have hA : ContDiffAt ℝ 1 A q :=
      contDiffAt_const.add
        (Complex.imCLM.contDiff.contDiffAt.comp q (hlog.comp q hratio.contDiffAt))
    have hmem : ∀ᶠ y in 𝓝 q, ratio y ∈ Complex.slitPlane :=
      hratio.continuous.continuousAt.eventually
        (Complex.isOpen_slitPlane.mem_nhds (by
          rw [hratioq]
          exact Complex.one_mem_slitPlane))
    have heq : Ext z =ᶠ[𝓝 q] fun y => beta z (A y) := by
      filter_upwards [hmem] with y hy
      have hwy : w y ≠ 0 := by
        intro h
        apply Complex.slitPlane_ne_zero hy
        simp only [ratio, h, zero_div]
      apply hangle z
      dsimp only [A]
      rw [Complex.log_im, Real.Angle.coe_add]
      change (Complex.arg (w y) : Real.Angle) =
        Complex.arg (w q) + (Complex.arg (w y / w q) : Real.Angle)
      rw [Complex.arg_div_coe_angle hwy hwq]
      abel
    exact (((hC1 z).contMDiffAt.comp q hA.contMDiffAt).congr_of_eventuallyEq
      heq).contMDiffWithinAt
  let f : Z → C1FreeLoopSpace (M := M) := fun z => loopOfExtension (Ext z) (hExt z)
  have htrace (z : Z) (x : ℝ) : periodicFreeLoop (f z) x = beta z x := by
    change beta z (Complex.arg (w (angularPoint x))) = beta z x
    apply hangle z
    simpa only [hw, angularPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Real.Angle.cos_coe, Real.Angle.sin_coe] using
      Complex.arg_cos_add_sin_mul_I_coe_angle (x : Real.Angle)
  let I := Icc (0 : ℝ) rampPeriod
  let qI : I → LoopCircle := fun t => ⟨angularPoint t, norm_angularPoint t⟩
  have hqI : Continuous qI :=
    (contDiff_angularPoint.continuous.comp continuous_subtype_val).subtype_mk _
  have hqIsurj : Function.Surjective qI := by
    intro c
    obtain ⟨t, ht, htc⟩ := exists_angularPoint c
    exact ⟨⟨t, ht⟩, Subtype.ext htc⟩
  have hproper : IsProperMap (Prod.map (id : Z → Z) qI) :=
    isProperMap_id.prodMap hqI.isProperMap
  have hquot : Topology.IsQuotientMap (Prod.map (id : Z → Z) qI) :=
    hproper.isClosedMap.isQuotientMap hproper.continuous
      (Function.surjective_id.prodMap hqIsurj)
  have hvalueq (z : Z) (t : I) : f z (qI t) = beta z t := htrace z t
  have htangentq (z : Z) (t : I) :
      c1LoopTangent (f z) (qI t) = m63AngularFirstJet (n := 3) (beta z) t := by
    change c1LoopTangent (f z) ⟨angularPoint t, norm_angularPoint t⟩ = _
    rw [← m63AngularFirstJet_eq_c1LoopTangent (f z) (t : ℝ)]
    rw [show periodicFreeLoop (f z) = beta z from funext (htrace z)]
  have hvalues : Continuous (fun p : Z × LoopCircle => f p.1 p.2) := by
    apply hquot.continuous_iff.mpr
    change Continuous (fun p : Z × I => f p.1 (qI p.2))
    exact (hvalue.comp
      (continuous_fst.prodMk continuous_snd.subtype_val)).congr
        (fun p => (hvalueq p.1 p.2).symm)
  have htangents : Continuous (fun p : Z × LoopCircle => c1LoopTangent (f p.1) p.2) := by
    apply hquot.continuous_iff.mpr
    change Continuous (fun p : Z × I => c1LoopTangent (f p.1) (qI p.2))
    exact (hfirst.comp
      (continuous_fst.prodMk continuous_snd.subtype_val)).congr
        (fun p => (htangentq p.1 p.2).symm)
  have hf : Continuous f := by
    apply (continuous_iff_values_tangents f).mpr
    exact ⟨ContinuousMap.continuous_of_continuous_uncurry _ hvalues,
      ContinuousMap.continuous_of_continuous_uncurry _ htangents⟩
  exact ⟨⟨f, hf⟩, htrace⟩

end PoincareConjecture.M63

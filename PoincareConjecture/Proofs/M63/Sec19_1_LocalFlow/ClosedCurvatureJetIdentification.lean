import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C1EmbeddingPushforward
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2GaugeWitnesses
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.MixedEmbeddingHessian
import PoincareConjecture.Proofs.M63.Mathlib.RetractionTangentContinuity
import PoincareConjecture.Definitions.M63Ramp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)

set_option maxHeartbeats 800000 in





theorem curvatureJet_identification_of_embedded_recurrences
    [T2Space M] (F : RicciFlow n M (Icc a b)) {tau s : ℝ}
    (_hat : a < tau) (hts : tau < s) (_hsb : s ≤ b)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {c : ℝ → ℝ → M} (hc : M63C2ShrinkingCurveOn F c (Icc tau s))
    (η : ℕ → C(Icc tau s, X))
    (hzero : ∀ (t : Icc tau s) (x : ℝ), η 0 t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m62CurvatureVector F c t x))
    (hrec : ∀ i (t : Icc tau s) (x : ℝ),
      HasDerivAt (fun y : ℝ => η i t (y : AddCircle curvePeriod))
        (curveSpeed F c t x • (η (i + 1) t (x : AddCircle curvePeriod) +
          coordinateHessian (F.connection t) e (ρ (e (c x t)))
            (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e (c x t))
              (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x)))
            (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e (c x t))
              (η i t (x : AddCircle curvePeriod))))) x) :
    (∀ i (t : Icc tau s) (x : ℝ), η i t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m63CurvatureJet F c i t x)) ∧
    (∀ i (t : Icc tau s), ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
      (fun x => (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M))) ∧
    ∀ i, ContinuousOn
      (fun z : ℝ × ℝ => (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ :
        TangentBundle (𝓡 n) M)) (univ ×ˢ Icc tau s) := by
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  let B := fun (t : ℝ) (z p q : W) => coordinateHessian (F.connection t) e (ρ z)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z p) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z q)
  have hpush : Continuous (fun p : TangentBundle (𝓡 n) M =>
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e p.1 p.2 : W)) :=
    (contMDiff_snd_tangentBundle_modelSpace (n := ∞) W 𝓘(ℝ, W)).continuous.comp
      (he.continuous_tangentMap (by simp))
  have hvpos (t : Icc tau s) (x : ℝ) : 0 < curveSpeed F c t x :=
    Real.sqrt_pos.mpr ((F.metric t).pos _ _ (hc.immersed t t.property x))
  have hηcont (i : ℕ) (t : Icc tau s) :
      Continuous (fun x : ℝ => η i t (x : AddCircle curvePeriod)) :=
    (η i t).continuous.comp (AddCircle.continuous_mk' curvePeriod)
  have hB : ContinuousOn
      (fun z : (ℝ × W) × (W × W) => B z.1.1 z.1.2 z.2.1 z.2.2)
      ((Icc a b ×ˢ U) ×ˢ univ) :=
    (flow_coordinateHessian_mixed_pullback_contDiffOn F he hU hρ).continuousOn
  have hηC1 (i : ℕ) (t : Icc tau s) :
      ContDiff ℝ 1 (fun x : ℝ => η i t (x : AddCircle curvePeriod)) := by
    have hbase := hc.spatial_regular t t.property
    have hS : Continuous (fun x => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t)
        (spatialUnitTangent F c t x) : W)) :=
      hpush.comp (unitTangent_contMDiff_of_c2 F c hbase
        (hc.immersed t t.property)).continuous
    let coefficientInput : ℝ → (ℝ × W) × (W × W) := fun x => ((t.1, e (c x t)),
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x),
          η i t (x : AddCircle curvePeriod)))
    have hmap : Continuous coefficientInput :=
      (continuous_const.prodMk (he.continuous.comp hbase.continuous)).prodMk
        (hS.prodMk (hηcont i t))
    have hBi := hB.comp_continuous (f := coefficientInput) hmap (fun x =>
      show coefficientInput x ∈ ((Icc a b ×ˢ U) ×ˢ univ) from
        ⟨⟨hc.domain_subset t.property, heU (mem_range_self (c x t))⟩, mem_univ _⟩)
    have hRHS : Continuous (fun x : ℝ => curveSpeed F c t x •
        (η (i + 1) t (x : AddCircle curvePeriod) + B t (e (c x t))
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x))
          (η i t (x : AddCircle curvePeriod)))) :=
      (speed_contDiff_of_c2 F c hbase (hc.immersed t t.property)).continuous.smul
        ((hηcont (i + 1) t).add hBi)
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (hrec i t x).differentiableAt, ?_⟩
    have hd : deriv (fun x : ℝ => η i t (x : AddCircle curvePeriod)) =
        fun x => curveSpeed F c t x •
          (η (i + 1) t (x : AddCircle curvePeriod) + B t (e (c x t))
            (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x))
            (η i t (x : AddCircle curvePeriod))) :=
      funext (fun x => (hrec i t x).deriv)
    rw [hd]
    exact hRHS
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hfield (i : ℕ)
      (hi : ∀ (t : Icc tau s) (x : ℝ), η i t (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m63CurvatureJet F c i t x))
      (t : Icc tau s) : ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun x => (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M)) := by
    let T : ℝ → TangentBundle 𝓘(ℝ, W) W :=
      fun x => ⟨e (c x t), η i t (x : AddCircle curvePeriod)⟩
    have he1 : ContMDiff (𝓡 n) 𝓘(ℝ, W) 1 e := he.of_le (by simp)
    have hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => c x t) :=
      (hc.spatial_regular t t.property).of_le (by norm_num)
    have hmodel : ContMDiff (𝓘(ℝ, W)).tangent (𝓘(ℝ, W)).tangent 1
        (fun q : W × W => (⟨q.1, q.2⟩ : TangentBundle 𝓘(ℝ, W) W)) := by
      convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm
        (I := 𝓘(ℝ, W)) (n := 1)) using 1
      rw [chartedSpaceSelf_prod]
      rfl
    have hT : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, W)).tangent 1 T :=
      hmodel.comp ((he1.comp hc1).prodMk (hηC1 i t).contMDiff)
    have hr := hρ.contMDiffOn_tangentMapWithin (m := 1) (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top) hU.uniqueMDiffOn
    have hcomp := hr.comp_contMDiff hT (fun x => heU (mem_range_self (c x t)))
    have heq : tangentMapWithin 𝓘(ℝ, W) (𝓡 n) ρ U ∘ T =
        fun x => (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M) := by
      funext x
      dsimp only [Function.comp_def, T, tangentMapWithin]
      rw [mfderivWithin_of_isOpen hU (heU (mem_range_self (c x t))), hi t x]
      apply Bundle.TotalSpace.ext (hρe (c x t))
      apply heq_of_eq
      exact hleft (c x t) (m63CurvatureJet F c i t x)
    rw [heq] at hcomp
    exact hcomp
  have hscale (t : ℝ) (p : M) (Y Z : TangentSpace (𝓡 n) p) (r : ℝ) :
      coordinateHessian (F.connection t) e p (r • Y) Z =
        r • coordinateHessian (F.connection t) e p Y Z := by
    ext k
    have hek : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun q => e q k) :=
      (EuclideanSpace.proj k).contDiff.contMDiff.comp he
    obtain ⟨A, hA⟩ := (M04.isSmoothCovariantTensor_hessian (F.connection t) hek).1 p
    have hrep (v w : TangentSpace (𝓡 n) p) :
        (F.connection t).hessian (fun q => e q k) p v w = A ![v, w] := hA ![v, w]
    change (F.connection t).hessian (fun q => e q k) p (r • Y) Z =
      r * (F.connection t).hessian (fun q => e q k) p Y Z
    rw [hrep, hrep]
    simpa only [Matrix.vecCons, smul_eq_mul] using A.cons_smul ![Z] r Y
  have hident : ∀ i (t : Icc tau s) (x : ℝ), η i t (x : AddCircle curvePeriod) =
      mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m63CurvatureJet F c i t x) := by
    intro i
    induction i with
    | zero => exact hzero
    | succ i hi =>
      intro t x
      have hvel : curveVelocity (n := n) (fun y => c y t) x =
          curveSpeed F c t x • spatialUnitTangent F c t x := by
        symm
        change curveSpeed F c t x • ((curveSpeed F c t x)⁻¹ •
          curveVelocity (n := n) (fun y => c y t) x) = _
        rw [smul_smul, mul_inv_cancel₀ (hvpos t x).ne', one_smul]
      have hcov : rampHorizontalCovariantDerivative (F.connection t) (fun y => c y t)
          (fun y => m63CurvatureJet F c i t y) x =
          curveSpeed F c t x • m63CurvatureJet F c (i + 1) t x := by
        change _ = curveSpeed F c t x • ((curveSpeed F c t x)⁻¹ • _)
        rw [smul_smul, mul_inv_cancel₀ (hvpos t x).ne', one_smul]
      have hBi : B t (e (c x t))
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x))
          (η i t (x : AddCircle curvePeriod)) =
          coordinateHessian (F.connection t) e (c x t)
            (spatialUnitTangent F c t x) (m63CurvatureJet F c i t x) := by
        dsimp only [B]
        rw [hi t x]
        erw [hleft (c x t) (spatialUnitTangent F c t x),
          hleft (c x t) (m63CurvatureJet F c i t x), hρe (c x t)]
      have hp := hasDerivAt_embedding_pushforward_of_contMDiffAt_one
        (F.connection t) he ((hc.spatial_regular t t.property).of_le (by norm_num) x)
        (fun y => m63CurvatureJet F c i t y) (hfield i hi t x)
      have hp' : HasDerivAt (fun y : ℝ => η i t (y : AddCircle curvePeriod))
          (curveSpeed F c t x •
            (HAdd.hAdd (α := W) (β := W) (γ := W)
              (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (m63CurvatureJet F c (i + 1) t x))
              (B t (e (c x t))
                (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t) (spatialUnitTangent F c t x))
                (η i t (x : AddCircle curvePeriod))))) x := by
        rw [show (fun y : ℝ => η i t (y : AddCircle curvePeriod)) =
          (fun y => mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y t) (m63CurvatureJet F c i t y))
          from funext (hi t)]
        apply hp.congr_deriv
        change HAdd.hAdd (α := W) (β := W) (γ := W)
          (coordinateHessian (F.connection t) e (c x t)
            (curveVelocity (n := n) (fun y => c y t) x) (m63CurvatureJet F c i t x))
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x t)
            (rampHorizontalCovariantDerivative (F.connection t) (fun y => c y t)
              (fun y => m63CurvatureJet F c i t y) x)) = _
        rw [hvel, hcov, hscale, map_smul, smul_add, hBi]
        exact add_comm _ _
      have hd := congrArg (fun w : W => (curveSpeed F c t x)⁻¹ • w)
        ((hrec i t x).unique hp')
      simp only [smul_smul, inv_mul_cancel₀ (hvpos t x).ne', one_smul] at hd
      exact add_right_cancel hd
  refine ⟨hident, fun i t => hfield i (hident i) t, ?_⟩
  intro i
  apply continuousOn_tangentSection_of_retraction_pushforward he hU heU hρ hρe
    (fun z : ℝ × ℝ => c z.1 z.2)
    (fun z => m63CurvatureJet F c i z.2 z.1) hc.continuous
  have heval : Continuous (fun z : ℝ × ℝ =>
      η i (projIcc tau s hts.le z.2) (z.1 : AddCircle curvePeriod)) :=
    ((η i).continuous.comp (continuous_projIcc.comp continuous_snd)).eval
      ((AddCircle.continuous_mk' curvePeriod).comp continuous_fst)
  apply heval.continuousOn.congr
  intro z hz
  exact (hident i ⟨z.2, hz.2⟩ z.1).symm.trans
    (congrArg (fun t : Icc tau s => η i t (z.1 : AddCircle curvePeriod))
      (projIcc_of_mem hts.le hz.2).symm)

end PoincareConjecture.M63

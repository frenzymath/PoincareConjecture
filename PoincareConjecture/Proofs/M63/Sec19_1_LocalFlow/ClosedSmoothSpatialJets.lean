import PoincareConjecture.Proofs.M63.Mathlib.SpatialPartialDerivative
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ClosedCurvatureJetIdentification
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PullbackMetricHessian
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessEmbeddedCurve
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "X" => C(AddCircle curvePeriod, W)

theorem c2ShrinkingCurve_closed_spatial_jets_of_joint_smooth
    [T2Space M] (F : RicciFlow n M (Icc a b))
    {s t : ℝ} (has : a < s) (hst : s < t)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U)
    {ρ : W → M} (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    (hρe : ∀ p, ρ (e p) = p)
    {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc s t))
    (hjoint : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => c z.1 z.2) (univ ×ˢ Icc s t)) :
    (∀ i (u : Icc s t),
      ContMDiff 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n)) 1
        (fun x => (⟨c x u, m63CurvatureJet F c i u x⟩ :
          TangentBundle (𝓡 n) M))) ∧
    ∀ i, ContinuousOn
      (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ :
          TangentBundle (𝓡 n) M)) (univ ×ˢ Icc s t) := by
  classical
  let : Fact (0 < curvePeriod) := ⟨Real.two_pi_pos⟩
  let D : Set (ℝ × ℝ) := Icc s t ×ˢ univ
  let q : ℝ → ℝ → W := fun u x => e (c x u)
  let p : ℝ → ℝ → W := fun u => deriv (q u)
  let v : ℝ → ℝ → ℝ := fun u x => curveSpeed F c u x
  have hq : ContDiffOn ℝ ∞ (Function.uncurry q) D :=
    ((he.comp_contMDiffOn hjoint).contDiffOn).comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun _ hz => ⟨mem_univ _, hz.1⟩)
  have hp : ContDiffOn ℝ ∞ (Function.uncurry p) D :=
    contDiffOn_spatial_deriv_of_uniqueDiffOn (uniqueDiffOn_Icc hst) (by simp) hq
  have hdata := c2ShrinkingCurve_embedded_closed_data hc he
  have hpeq (u : ℝ) (hu : u ∈ Icc s t) (x : ℝ) :
      p u x = mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x u)
        (curveVelocity (n := n) (fun y => c y u) x) :=
    (hdata.2.1 u hu x).deriv
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  let G := fun (u : ℝ) (z w : W) => (F.metric u).inner (ρ z)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z w) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z w)
  have hG : ContDiffOn ℝ ∞
      (fun z : (ℝ × W) × W => G z.1.1 z.1.2 z.2)
      ((Icc a b ×ˢ U) ×ˢ univ) :=
    (flow_pullback_metric_hessian_contDiffOn F hU hρ
      (contMDiff_const (c := (0 : ℝ)))).1
  have hGq : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => G z.1 (q z.1 z.2) (p z.1 z.2)) D :=
    hG.comp ((contDiffOn_fst.prodMk hq).prodMk hp)
      (fun z hz => ⟨⟨hc.domain_subset hz.1, heU (mem_range_self _)⟩, mem_univ _⟩)
  have hGactual (u : ℝ) (hu : u ∈ Icc s t) (x : ℝ) :
      G u (q u x) (p u x) = (F.metric u).inner (c x u)
        (curveVelocity (n := n) (fun y => c y u) x)
        (curveVelocity (n := n) (fun y => c y u) x) := by
    dsimp only [G, q]
    rw [hpeq u hu x]
    erw [hleft (c x u) (curveVelocity (n := n) (fun y => c y u) x), hρe (c x u)]
  have hGpos (u : ℝ) (hu : u ∈ Icc s t) (x : ℝ) : 0 < G u (q u x) (p u x) := by
    rw [hGactual u hu x]
    exact (F.metric u).pos _ _ (hc.immersed u hu x)
  have hvrep (u : ℝ) (hu : u ∈ Icc s t) (x : ℝ) :
      Real.sqrt (G u (q u x) (p u x)) = v u x := by
    rw [hGactual u hu x]
    rfl
  have hv : ContDiffOn ℝ ∞ (Function.uncurry v) D :=
    (hGq.sqrt (fun z hz => (hGpos z.1 hz.1 z.2).ne')).congr
      (fun z hz => (hvrep z.1 hz.1 z.2).symm)
  have hvpos (u : ℝ) (hu : u ∈ Icc s t) (x : ℝ) : 0 < v u x :=
    Real.sqrt_pos.mpr ((F.metric u).pos _ _ (hc.immersed u hu x))
  have hvinv : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => (v z.1 z.2)⁻¹) D :=
    hv.inv (fun z hz => (hvpos z.1 hz.1 z.2).ne')
  let B := fun (u : ℝ) (z w r : W) => coordinateHessian (F.connection u) e (ρ z)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z w) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z r)
  have hB : ContDiffOn ℝ ∞
      (fun z : (ℝ × W) × (W × W) => B z.1.1 z.1.2 z.2.1 z.2.2)
      ((Icc a b ×ˢ U) ×ˢ univ) :=
    flow_coordinateHessian_mixed_pullback_contDiffOn F he hU hρ
  let R0 : ℝ → ℝ → W := fun u x => (v u x)⁻¹ • p u x
  let R : ℕ → ℝ → ℝ → W := fun j => Nat.rec R0
    (fun _ f u x => (v u x)⁻¹ • deriv (f u) x - B u (q u x) (R0 u x) (f u x)) j
  have hR0 : ContDiffOn ℝ ∞ (Function.uncurry R0) D := hvinv.smul hp
  have hR (j : ℕ) : ContDiffOn ℝ ∞ (Function.uncurry (R j)) D := by
    induction j with
    | zero => exact hR0
    | succ j ih =>
      have hd : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => deriv (R j z.1) z.2) D :=
        contDiffOn_spatial_deriv_of_uniqueDiffOn (uniqueDiffOn_Icc hst)
          (q := R j) (by simp) ih
      have hinput : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
          ((z.1, q z.1 z.2), (R0 z.1 z.2, R j z.1 z.2))) D :=
        (contDiffOn_fst.prodMk hq).prodMk (hR0.prodMk ih)
      have hcoefficient : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
          B z.1 (q z.1 z.2) (R0 z.1 z.2) (R j z.1 z.2)) D :=
        hB.comp (s := D) (f := fun z : ℝ × ℝ =>
          ((z.1, q z.1 z.2), (R0 z.1 z.2, R j z.1 z.2))) hinput
          (fun z hz => ⟨⟨hc.domain_subset hz.1, heU (mem_range_self _)⟩, mem_univ _⟩)
      change ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
        (v z.1 z.2)⁻¹ • deriv (R j z.1) z.2 -
          B z.1 (q z.1 z.2) (R0 z.1 z.2) (R j z.1 z.2)) D
      exact (hvinv.smul hd).sub hcoefficient
  have hRslice (j : ℕ) (u : ℝ) (hu : u ∈ Icc s t) : ContDiff ℝ ∞ (R j u) :=
    (hR j).comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun _ => ⟨hu, mem_univ _⟩)
  have hRzero (u : ℝ) (hu : u ∈ Icc s t) (x : ℝ) :
      R0 u x = mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x u) (spatialUnitTangent F c u x) := by
    dsimp only [R0]
    rw [hpeq u hu x]
    exact (map_smul _ _ _).symm
  have hrec (j : ℕ) (u : ℝ) (hu : u ∈ Icc s t) (x : ℝ) :
      HasDerivAt (R j u)
        (v u x • (R (j + 1) u x + B u (q u x) (R0 u x) (R j u x))) x := by
    apply ((hRslice j u hu).differentiable (by simp) x).hasDerivAt.congr_deriv
    change deriv (R j u) x = v u x •
      ((v u x)⁻¹ • deriv (R j u) x - B u (q u x) (R0 u x) (R j u x) +
        B u (q u x) (R0 u x) (R j u x))
    rw [sub_add_cancel, smul_smul, mul_inv_cancel₀ (hvpos u hu x).ne', one_smul]
  have hscale (u : ℝ) (z : M) (Y Z : TangentSpace (𝓡 n) z) (r : ℝ) :
      coordinateHessian (F.connection u) e z (r • Y) Z =
        r • coordinateHessian (F.connection u) e z Y Z := by
    ext k
    have hek : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun q => e q k) :=
      (EuclideanSpace.proj k).contDiff.contMDiff.comp he
    obtain ⟨A, hA⟩ := (M04.isSmoothCovariantTensor_hessian (F.connection u) hek).1 z
    have hrep (Y' Z' : TangentSpace (𝓡 n) z) :
        (F.connection u).hessian (fun q => e q k) z Y' Z' = A ![Y', Z'] := hA ![Y', Z']
    change (F.connection u).hessian (fun q => e q k) z (r • Y) Z =
      r * (F.connection u).hessian (fun q => e q k) z Y Z
    rw [hrep, hrep]
    simpa only [Matrix.vecCons, smul_eq_mul] using A.cons_smul ![Z] r Y
  have hRone (u : ℝ) (hu : u ∈ Icc s t) (x : ℝ) :
      R 1 u x = mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x u) (m62CurvatureVector F c u x) := by
    have hvel : curveVelocity (n := n) (fun y => c y u) x =
        v u x • spatialUnitTangent F c u x := by
      change _ = v u x • ((v u x)⁻¹ • _)
      rw [smul_smul, mul_inv_cancel₀ (hvpos u hu x).ne', one_smul]
    have hcov : rampHorizontalCovariantDerivative (F.connection u) (fun y => c y u)
        (spatialUnitTangent F c u) x = v u x • m62CurvatureVector F c u x := by
      change _ = v u x • ((v u x)⁻¹ • _)
      rw [smul_smul, mul_inv_cancel₀ (hvpos u hu x).ne', one_smul]
    have hBzero : B u (q u x) (R0 u x) (R0 u x) =
        coordinateHessian (F.connection u) e (c x u)
          (spatialUnitTangent F c u x) (spatialUnitTangent F c u x) := by
      dsimp only [B, q]
      rw [hRzero u hu x]
      erw [hleft (c x u) (spatialUnitTangent F c u x), hρe (c x u)]
    have hd := hasDerivAt_embedding_pushforward_of_contMDiffAt_one
      (F.connection u) he ((hc.spatial_regular u hu).of_le (by norm_num) x)
      (spatialUnitTangent F c u)
      (unitTangent_contMDiff_of_c2 F c (hc.spatial_regular u hu) (hc.immersed u hu) x)
    have hd' : HasDerivAt (R 0 u)
        (v u x • (HAdd.hAdd (α := W) (β := W) (γ := W)
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x u) (m62CurvatureVector F c u x))
          (B u (q u x) (R0 u x) (R0 u x)))) x := by
      rw [show R 0 u = (fun y => mfderiv (𝓡 n) 𝓘(ℝ, W) e (c y u)
        (spatialUnitTangent F c u y)) from funext (hRzero u hu)]
      apply hd.congr_deriv
      change HAdd.hAdd (α := W) (β := W) (γ := W)
        (coordinateHessian (F.connection u) e (c x u)
          (curveVelocity (n := n) (fun y => c y u) x) (spatialUnitTangent F c u x))
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x u)
          (rampHorizontalCovariantDerivative (F.connection u) (fun y => c y u)
            (spatialUnitTangent F c u) x)) = _
      rw [hvel, hcov, hscale, map_smul, smul_add, hBzero]
      exact add_comm _ _
    have h := congrArg (fun w : W => (v u x)⁻¹ • w) ((hrec 0 u hu x).unique hd')
    simp only [smul_smul, inv_mul_cancel₀ (hvpos u hu x).ne', one_smul] at h
    exact add_right_cancel h
  have hderivper {f : ℝ → W} (hf : Function.Periodic f curvePeriod) :
      Function.Periodic (deriv f) curvePeriod := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun g : ℝ → W => deriv g x) (funext hf)
  have hqper (u : ℝ) (hu : u ∈ Icc s t) : Function.Periodic (q u) curvePeriod :=
    fun x => congrArg e (hc.periodic u hu x)
  have hpper (u : ℝ) (hu : u ∈ Icc s t) : Function.Periodic (p u) curvePeriod :=
    hderivper (hqper u hu)
  have hvper (u : ℝ) (hu : u ∈ Icc s t) : Function.Periodic (v u) curvePeriod := by
    intro x
    rw [← hvrep u hu (x + curvePeriod), ← hvrep u hu x, hqper u hu, hpper u hu]
  have hR0per (u : ℝ) (hu : u ∈ Icc s t) : Function.Periodic (R0 u) curvePeriod := by
    intro x
    dsimp only [R0]
    rw [hvper u hu, hpper u hu]
  have hRper (j : ℕ) (u : ℝ) (hu : u ∈ Icc s t) :
      Function.Periodic (R j u) curvePeriod := by
    induction j with
    | zero => exact hR0per u hu
    | succ j ih =>
      intro x
      change (v u (x + curvePeriod))⁻¹ • deriv (R j u) (x + curvePeriod) -
        B u (q u (x + curvePeriod)) (R0 u (x + curvePeriod)) (R j u (x + curvePeriod)) =
        (v u x)⁻¹ • deriv (R j u) x - B u (q u x) (R0 u x) (R j u x)
      rw [hvper u hu, hderivper ih, hqper u hu, hR0per u hu, ih]
  let η : ℕ → C(Icc s t, X) := fun j =>
    { toFun := fun u =>
        ⟨(hRper (j + 1) u u.property).lift,
          (QuotientAddGroup.isQuotientMap_mk
            (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
              (hRslice (j + 1) u u.property).continuous⟩
      continuous_toFun := by
        apply ContinuousMap.continuous_of_continuous_uncurry
        have hquot : IsOpenQuotientMap
            (fun z : Icc s t × ℝ => (z.1, (z.2 : AddCircle curvePeriod))) :=
          IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
        apply hquot.continuous_comp_iff.mp
        exact ((hR (j + 1)).continuousOn.comp_continuous
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
          (fun z => ⟨z.1.2, mem_univ _⟩)).congr (fun _ => rfl) }
  have hη (j : ℕ) (u : Icc s t) (x : ℝ) :
      η j u (x : AddCircle curvePeriod) = R (j + 1) u x := by
    change (hRper (j + 1) u u.property).lift (x : AddCircle curvePeriod) =
      R (j + 1) u x
    exact Function.Periodic.lift_coe (hRper (j + 1) u u.property) x
  have hzero (u : Icc s t) (x : ℝ) :
      η 0 u (x : AddCircle curvePeriod) =
        mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x u) (m62CurvatureVector F c u x) :=
    (hη 0 u x).trans (hRone u u.property x)
  have hηrec (j : ℕ) (u : Icc s t) (x : ℝ) :
      HasDerivAt (fun y : ℝ => η j u (y : AddCircle curvePeriod))
        (curveSpeed F c u x • (η (j + 1) u (x : AddCircle curvePeriod) +
          coordinateHessian (F.connection u) e (ρ (e (c x u)))
            (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e (c x u))
              (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c x u) (spatialUnitTangent F c u x)))
            (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (e (c x u))
              (η j u (x : AddCircle curvePeriod))))) x := by
    rw [show (fun y : ℝ => η j u (y : AddCircle curvePeriod)) = R (j + 1) u
      from funext (hη j u), hη (j + 1) u x, hη j u x]
    have h := hrec (j + 1) u u.property x
    rw [hRzero u u.property x] at h
    exact h
  exact (curvatureJet_identification_of_embedded_recurrences F has hst
    (hc.domain_subset ⟨hst.le, le_rfl⟩).2 he hU heU hρ hρe hc η hzero hηrec).2

end PoincareConjecture.M63

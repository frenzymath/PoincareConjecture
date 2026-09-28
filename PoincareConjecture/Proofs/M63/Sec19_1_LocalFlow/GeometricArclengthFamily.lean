import PoincareConjecture.Proofs.M63.Mathlib.ContinuousArclengthFamily
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PullbackMetricHessian
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v w

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {Z : Type w} [TopologicalSpace Z] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem exists_continuous_geometric_arclength_family
    (F : RicciFlow n M (Icc a b)) {tau : ℝ} (htau : tau ∈ Icc a b)
    {L0 : ℝ} (hL0 : 0 < L0)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    (gamma : Z → ℝ → M)
    (hperiod : ∀ z, Function.Periodic (gamma z) L0)
    (hC2 : ∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gamma z))
    (himm : ∀ z x, curveVelocity (n := n) (gamma z) x ≠ 0)
    (hzero : Continuous (fun p : Z × ℝ => e (gamma p.1 p.2)))
    (hfirst : Continuous (fun p : Z × ℝ =>
      deriv (fun y => e (gamma p.1 y)) p.2))
    (hsecond : Continuous (fun p : Z × ℝ =>
      deriv (deriv (fun y => e (gamma p.1 y))) p.2)) :
    let v := fun (z : Z) (x : ℝ) => curveSpeed F (fun y _ => gamma z y) tau x
    let m := fun z => (∫ x in (0 : ℝ)..L0, v z x) / L0
    (∀ z, 0 < m z) ∧ Continuous m ∧
      ∃ phi : Z → (ℝ ≃o ℝ),
        let q := fun (z : Z) (x : ℝ) => e (gamma z ((phi z).symm x))
        (∀ z,
          (∀ x, phi z x = (m z)⁻¹ * ∫ y in (0 : ℝ)..x, v z y) ∧
          ContDiff ℝ 2 (phi z : ℝ → ℝ) ∧
          ContDiff ℝ 2 ((phi z).symm : ℝ → ℝ) ∧
          phi z 0 = 0 ∧
          (∀ x, phi z (x + L0) = phi z x + L0) ∧
          (∀ x, (phi z).symm (x + L0) = (phi z).symm x + L0) ∧
          (∀ x, 0 < deriv (phi z : ℝ → ℝ) x ∧
            0 < deriv ((phi z).symm : ℝ → ℝ) x)) ∧
        Continuous (fun p : Z × ℝ => phi p.1 p.2) ∧
        Continuous (fun p : Z × ℝ => deriv (phi p.1 : ℝ → ℝ) p.2) ∧
        Continuous (fun p : Z × ℝ => deriv (deriv (phi p.1 : ℝ → ℝ)) p.2) ∧
        Continuous (fun p : Z × ℝ => (phi p.1).symm p.2) ∧
        Continuous (fun p : Z × ℝ => deriv ((phi p.1).symm : ℝ → ℝ) p.2) ∧
        Continuous (fun p : Z × ℝ =>
          deriv (deriv ((phi p.1).symm : ℝ → ℝ)) p.2) ∧
        (∀ z,
          Function.Periodic (fun x => gamma z ((phi z).symm x)) L0 ∧
          ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun x => gamma z ((phi z).symm x)) ∧
          (∀ x, curveVelocity (n := n) (fun y => gamma z ((phi z).symm y)) x ≠ 0) ∧
          (∀ x, curveSpeed F (fun y _ => gamma z ((phi z).symm y)) tau x = m z) ∧
          (∀ x, gamma z ((phi z).symm (phi z x)) = gamma z x)) ∧
        Continuous (fun p : Z × ℝ => q p.1 p.2) ∧
        Continuous (fun p : Z × ℝ => deriv (q p.1) p.2) ∧
        Continuous (fun p : Z × ℝ => deriv (deriv (q p.1)) p.2) := by
  classical
  let : Fact (0 < L0) := ⟨hL0⟩
  let f : Z → ℝ → W := fun z x => e (gamma z x)
  let p : Z → ℝ → W := fun z => deriv (f z)
  let r : Z → ℝ → W := fun z => deriv (p z)
  let v : Z → ℝ → ℝ := fun z x => curveSpeed F (fun y _ => gamma z y) tau x
  let m : Z → ℝ := fun z => (∫ x in (0 : ℝ)..L0, v z x) / L0
  have hf (z : Z) : ContDiff ℝ 2 (f z) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp (hC2 z)).contDiff
  have hfd (z : Z) (x : ℝ) : HasDerivAt (f z) (p z x) x :=
    ((hf z).differentiable (by norm_num) x).hasDerivAt
  have hpd (z : Z) (x : ℝ) : HasDerivAt (p z) (r z x) x :=
    (((hf z).deriv' (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have hpush (z : Z) (x : ℝ) : p z x =
      (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma z x)
        (curveVelocity (n := n) (gamma z) x) : W) := by
    have hchain : fderiv ℝ (f z) x =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma z x)).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (gamma z) x) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp x (he.mdifferentiable (by simp)).mdifferentiableAt
        ((hC2 z x).mdifferentiableAt (by norm_num))
    exact congrArg (fun L : ℝ →L[ℝ] W => L 1) hchain
  let O : Set (W × W) := U ×ˢ univ
  have hO : IsOpen O := hU.prod isOpen_univ
  let G : W × W → ℝ := fun z => (F.metric tau).inner (ρ z.1)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2)
  have hG0 := (flow_pullback_metric_hessian_contDiffOn F hU hρ
    (contMDiff_const (c := (0 : ℝ)))).1
  have hG : ContDiffOn ℝ ∞ G O :=
    hG0.comp (s := O)
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨⟨htau, hz.1⟩, hz.2⟩)
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hGvalue (z : Z) (x : ℝ) : G (f z x, p z x) =
      (F.metric tau).inner (gamma z x)
        (curveVelocity (n := n) (gamma z) x) (curveVelocity (n := n) (gamma z) x) := by
    dsimp only [G, f]
    rw [hpush]
    erw [hleft (gamma z x) (curveVelocity (n := n) (gamma z) x), hρe (gamma z x)]
  have hGpos (z : Z) (x : ℝ) : 0 < G (f z x, p z x) := by
    rw [hGvalue]
    exact (F.metric tau).pos _ _ (himm z x)
  have hvvalue (z : Z) (x : ℝ) : v z x = Real.sqrt (G (f z x, p z x)) := by
    rw [hGvalue]
    rfl
  have hvpos (z : Z) (x : ℝ) : 0 < v z x := by
    rw [hvvalue]
    exact Real.sqrt_pos.mpr (hGpos z x)
  let input : Z × ℝ → W × W := fun z => (f z.1 z.2, p z.1 z.2)
  have hinput : Continuous input := hzero.prodMk hfirst
  have hmem (z : Z × ℝ) : input z ∈ O := ⟨heU (mem_range_self _), mem_univ _⟩
  have hvc : Continuous (fun z : Z × ℝ => v z.1 z.2) :=
    (Real.continuous_sqrt.comp (hG.continuousOn.comp_continuous
      (f := input) hinput hmem)).congr (fun z => (hvvalue z.1 z.2).symm)
  have hDG : ContinuousOn (fderiv ℝ G) O :=
    hG.continuousOn_fderiv_of_isOpen hO (by simp)
  let direction : Z × ℝ → W × W := fun z => (p z.1 z.2, r z.1 z.2)
  have hdir : Continuous direction := hfirst.prodMk hsecond
  let v1 : Z → ℝ → ℝ := fun z x =>
    fderiv ℝ G (f z x, p z x) (p z x, r z x) / (2 * v z x)
  have hv1c : Continuous (fun z : Z × ℝ => v1 z.1 z.2) :=
    ((hDG.comp_continuous (f := input) hinput hmem).clm_apply hdir).div
      (continuous_const.mul hvc) (fun z => mul_ne_zero (by norm_num) (hvpos z.1 z.2).ne')
  have hvder (z : Z) (x : ℝ) : HasDerivAt (v z) (v1 z x) x := by
    have hd := ((hG.contDiffAt (hO.mem_nhds (hmem (z, x)))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt x ((hfd z x).prodMk (hpd z x))
    have hs : HasDerivAt (v z)
        (fderiv ℝ G (f z x, p z x) (p z x, r z x) /
          (2 * Real.sqrt (G (f z x, p z x)))) x :=
      (hd.sqrt (hGpos z x).ne').congr_of_eventuallyEq
        (Eventually.of_forall (hvvalue z))
    simpa only [v1, hvvalue z x] using hs
  have hfper (z : Z) : Function.Periodic (f z) L0 :=
    fun x => congrArg e (hperiod z x)
  have hpper (z : Z) : Function.Periodic (p z) L0 :=
    (hfper z).deriv_of_differentiable ((hf z).differentiable (by norm_num))
  have hvper (z : Z) : Function.Periodic (v z) L0 := by
    intro x
    rw [hvvalue z (x + L0), hvvalue z x, hfper z x, hpper z x]
  have hv1per (z : Z) : Function.Periodic (v1 z) L0 := by
    have hd := (hvper z).deriv_of_differentiable (fun x => (hvder z x).differentiableAt)
    have heq : deriv (v z) = v1 z := funext fun x => (hvder z x).deriv
    rwa [heq] at hd
  have descend (w : Z → ℝ → ℝ) (hw : Continuous (fun z : Z × ℝ => w z.1 z.2))
      (hp : ∀ z, Function.Periodic (w z) L0) :
      ∃ V : Z → C(AddCircle L0, ℝ), Continuous V ∧
        ∀ z (x : ℝ), V z (x : AddCircle L0) = w z x := by
    let V : Z → C(AddCircle L0, ℝ) := fun z => ⟨(hp z).lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L0)).continuous_iff.mpr
        (hw.comp (continuous_const.prodMk continuous_id))⟩
    have hrep (z : Z) (x : ℝ) : V z (x : AddCircle L0) = w z x := by
      change (hp z).lift (x : AddCircle L0) = w z x
      exact Function.Periodic.lift_coe _ x
    refine ⟨V, ?_, hrep⟩
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap (fun z : Z × ℝ => (z.1, (z.2 : AddCircle L0))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    simpa only [Function.comp_def, Function.uncurry, hrep] using hw
  obtain ⟨V, hV, hVrep⟩ := descend v hvc hvper
  obtain ⟨V1, hV1, hV1rep⟩ := descend v1 hv1c hv1per
  have hVder (z : Z) (x : ℝ) : HasDerivAt
      (fun y : ℝ => V z (y : AddCircle L0)) (V1 z (x : AddCircle L0)) x := by
    simpa only [hVrep, hV1rep] using hvder z x
  have hVpos (z : Z) (x : ℝ) : 0 < V z (x : AddCircle L0) := by
    rw [hVrep]
    exact hvpos z x
  have harclength := exists_continuous_C2_arclength_family V V1 hV hV1 hVder hVpos
  dsimp only at harclength
  simp only [hVrep, hV1rep] at harclength
  obtain ⟨hmpos, hmc, phi, hphi, hphic, hphidc, hphiddc, hpsic, hpsidc, hpsiddc⟩ := harclength
  let psi : Z → ℝ → ℝ := fun z => (phi z).symm
  let q : Z → ℝ → W := fun z x => f z (psi z x)
  have hpsi (z : Z) : ContDiff ℝ 2 (psi z) := (hphi z).2.2.1
  have hpsipos (z : Z) (x : ℝ) : 0 < deriv (psi z) x := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hp⟩ := hphi z
    exact (hp x).2
  have hpsider (z : Z) (x : ℝ) : HasDerivAt (psi z) (deriv (psi z) x) x :=
    ((hpsi z).differentiable (by norm_num) x).hasDerivAt
  have hpsiSecond (z : Z) (x : ℝ) :
      HasDerivAt (deriv (psi z)) (deriv (deriv (psi z)) x) x :=
    (((hpsi z).deriv' (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have hqfirst (z : Z) (x : ℝ) : deriv (q z) x = deriv (psi z) x • p z (psi z x) := by
    exact ((hfd z (psi z x)).scomp x (hpsider z x)).deriv
  have hqsecond (z : Z) (x : ℝ) : deriv (deriv (q z)) x =
      deriv (psi z) x ^ 2 • r z (psi z x) +
        deriv (deriv (psi z)) x • p z (psi z x) := by
    have heq : deriv (q z) = fun y => deriv (psi z) y • p z (psi z y) :=
      funext (hqfirst z)
    rw [heq]
    have hd := (hpsiSecond z x).fun_smul ((hpd z (psi z x)).scomp x (hpsider z x))
    simpa only [Function.comp_def, smul_smul, ← pow_two] using hd.deriv
  have hmap : Continuous (fun z : Z × ℝ => (z.1, psi z.1 z.2)) :=
    continuous_fst.prodMk hpsic
  have hq0 : Continuous (fun z : Z × ℝ => q z.1 z.2) := hzero.comp hmap
  have hq1 : Continuous (fun z : Z × ℝ => deriv (q z.1) z.2) :=
    (hpsidc.smul (hfirst.comp hmap)).congr (fun z => (hqfirst z.1 z.2).symm)
  have hq2 : Continuous (fun z : Z × ℝ => deriv (deriv (q z.1)) z.2) :=
    (((hpsidc.pow 2).smul (hsecond.comp hmap)).add
      (hpsiddc.smul (hfirst.comp hmap))).congr (fun z => (hqsecond z.1 z.2).symm)
  refine ⟨hmpos, hmc, phi, ?_, hphic, hphidc, hphiddc, hpsic, hpsidc, hpsiddc,
    ?_, hq0, hq1, hq2⟩
  · intro z
    obtain ⟨hform, hpc, hpic, hpzero, hshift, hishift, _, _, _, _, hpos⟩ := hphi z
    exact ⟨hform, hpc, hpic, hpzero, hshift, hishift, hpos⟩
  · intro z
    obtain ⟨_, _, _, _, _, hshift, _, _, hinvd, _, _⟩ := hphi z
    refine ⟨?_, (hC2 z).comp (hpsi z).contMDiff, ?_, ?_, ?_⟩
    · intro x
      change gamma z ((phi z).symm (x + L0)) = gamma z ((phi z).symm x)
      rw [hshift, hperiod z]
    · intro x
      rw [curveVelocity_comp ((hC2 z).mdifferentiable (by norm_num) (psi z x))
        (hpsider z x)]
      exact smul_ne_zero (hpsipos z x).ne' (himm z (psi z x))
    · intro x
      have hd : HasDerivAt (psi z) (m z / v z (psi z x)) x := hinvd x
      have hpos : 0 < m z / v z (psi z x) := div_pos (hmpos z) (hvpos z _)
      have hs := curveSpeed_comp F (fun y _ => gamma z y) (t := tau)
        ((hC2 z).mdifferentiable (by norm_num) (psi z x)) hd hpos.le
      change curveSpeed F (fun y _ => gamma z (psi z y)) tau x = _
      rw [hs]
      change m z / v z (psi z x) * v z (psi z x) = m z
      exact div_mul_cancel₀ _ (hvpos z _).ne'
    · intro x
      rw [(phi z).symm_apply_apply]

end PoincareConjecture.M63

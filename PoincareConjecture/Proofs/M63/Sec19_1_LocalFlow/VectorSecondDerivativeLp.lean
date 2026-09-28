import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH2SecondDerivative
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.VectorSpectralTranslation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Deriv










set_option autoImplicit false

open AddCircle MeasureTheory PoincareConjecture.SpectralHeatNative
open scoped BigOperators Topology ContDiff

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)] {ι : Type*} [Fintype ι]

local notation "V" => State ((ℤ × Fin 2) × ι)
local notation "W" => EuclideanSpace ℝ ι




noncomputable def vectorPeriodicSecondDerivativeLp :
    V →L[ℝ] Lp W 2 (@haarAddCircle L _) := by
  classical
  let C (i : ι) : V →L[ℝ] lp (fun _ : ℤ => ℂ) 2 :=
    complexLpRealEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj i).comp (lpFinitePiEquiv ℝ).toContinuousLinearMap)
  let B (i : ι) : ℝ →L[ℝ] W :=
    ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i 1)
  let D := (periodicH1DerivativeLp (L := L)).comp
    (periodicH2JetCoordinates (L := L) 1 (by omega))
  exact ∑ i, ((B i |>.comp Complex.reCLM).compLpL 2 haarAddCircle).comp
    ((D.restrictScalars ℝ).comp (C i))




theorem vectorPeriodicSecondDerivativeLp_spec (u : V)
    (hu : DifferentiableAt ℝ
      (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s u) 0) :
    let q0 := fun x : AddCircle L =>
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) u x)
    let q1 := fun x : AddCircle L =>
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) u x)
    ∃ q2 : C(AddCircle L, W),
      ContDiff ℝ 2 (fun x : ℝ => q0 (x : AddCircle L)) ∧
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => q1 (y : AddCircle L))
        (q2 (x : AddCircle L)) x) ∧
      (∀ x : ℝ, iteratedDeriv 2 (fun y : ℝ => q0 (y : AddCircle L)) x =
        q2 (x : AddCircle L)) ∧
      vectorPeriodicSecondDerivativeLp (L := L) u =
        ContinuousMap.toLp 2 haarAddCircle ℝ q2 := by
  classical
  let C (i : ι) : V →L[ℝ] lp (fun _ : ℤ => ℂ) 2 :=
    complexLpRealEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj i).comp (lpFinitePiEquiv ℝ).toContinuousLinearMap)
  let B (i : ι) : ℝ →L[ℝ] W :=
    ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i 1)
  let A (i : ι) : ℂ →L[ℝ] W := (B i).comp Complex.reCLM
  let D := (periodicH1DerivativeLp (L := L)).comp
    (periodicH2JetCoordinates (L := L) 1 (by omega))
  let f (i : ι) := periodicSobolevJet (L := L) 1 1 (by omega) (C i u)
  let G (i : ι) (s : ℝ) := periodicSobolevJet (L := L) 1 1 (by omega)
    (C i (vectorPeriodicSpectralTranslation (L := L) s u))
  have hGdiff (i : ι) : DifferentiableAt ℝ (G i) 0 :=
    ((periodicSobolevJet (L := L) 1 1 (by omega)).restrictScalars ℝ).differentiableAt.comp 0
      ((C i).differentiableAt.comp 0 hu)
  have horbit (i : ι) (s : ℝ) (x : AddCircle L) : G i s x = f i (x - (s : AddCircle L)) := by
    have hs : C i (vectorPeriodicSpectralTranslation (L := L) s u) =
        periodicSpectralTranslation (L := L) s (C i u) := by
      change complexLpRealEquiv.symm
        (lpFinitePiEquiv ℝ (vectorPeriodicSpectralTranslation (L := L) s u) i) = _
      rw [(vectorPeriodicSpectralTranslation_spec s u).1 i,
        (realPeriodicSpectralTranslation_spec s _).1]
      rfl
    change periodicSobolevJet (L := L) 1 1 (by omega)
      (C i (vectorPeriodicSpectralTranslation (L := L) s u)) x = _
    rw [hs, periodicSobolevJet_periodicSpectralTranslation]
    rfl
  let g (i : ι) : C(AddCircle L, ℂ) := -deriv (G i) 0
  have hg (i : ι) (x : ℝ) : HasDerivAt
      (fun y : ℝ => f i (y : AddCircle L)) (g i (x : AddCircle L)) x := by
    have hd := (ContinuousMap.evalCLM ℝ (x : AddCircle L)).hasFDerivAt.comp_hasDerivAt 0
      (hGdiff i).hasDerivAt
    have hd' : HasDerivAt (fun s : ℝ => G i s (x : AddCircle L))
        (deriv (G i) 0 (x : AddCircle L)) (x - x) := by
      simpa only [sub_self, Function.comp_def] using! hd
    have hc := hd'.scomp x ((hasDerivAt_const x x).sub (hasDerivAt_id x))
    change HasDerivAt (fun y : ℝ => G i (x - y) (x : AddCircle L))
      ((0 - 1 : ℝ) • deriv (G i) 0 (x : AddCircle L)) x at hc
    have heq : (fun y : ℝ => G i (x - y) (x : AddCircle L)) =
        (fun y : ℝ => f i (y : AddCircle L)) := by
      funext y
      rw [horbit, AddCircle.coe_sub, sub_sub_cancel]
    rw [heq] at hc
    simpa only [zero_sub, neg_one_smul, g, ContinuousMap.neg_apply] using hc
  let E := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let q0 : C(AddCircle L, W) := E.symm.toContinuousLinearMap.compLeftContinuous ℝ _
    (vectorPeriodicJet (L := L) 1 0 (by omega) u)
  let q1 : C(AddCircle L, W) := E.symm.toContinuousLinearMap.compLeftContinuous ℝ _
    (vectorPeriodicJet (L := L) 1 1 (by omega) u)
  let h (i : ι) : C(AddCircle L, W) := (A i).compLeftContinuous ℝ _ (g i)
  let q2 : C(AddCircle L, W) := ∑ i, h i
  have hsum (z : AddCircle L) : (∑ i, A i (f i z)) = q1 z := by
    apply PiLp.ext
    intro i
    change WithLp.ofLp (∑ j, (f j z).re • EuclideanSpace.single j (1 : ℝ)) i = (f i z).re
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
      EuclideanSpace.single, PiLp.ofLp_single, Pi.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    simp
  have hq1 (x : ℝ) : HasDerivAt (fun y : ℝ => q1 (y : AddCircle L))
      (q2 (x : AddCircle L)) x := by
    have hd := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (A i).hasFDerivAt.comp_hasDerivAt x (hg i x))
    simp only [q2, ContinuousMap.sum_apply]
    change HasDerivAt (fun y : ℝ => q1 (y : AddCircle L))
      (∑ i, A i (g i (x : AddCircle L))) x
    simpa only [Function.comp_def, hsum] using hd
  have hq0 (x : ℝ) : HasDerivAt (fun y : ℝ => q0 (y : AddCircle L))
      (q1 (x : AddCircle L)) x :=
    E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
      (hasDerivAt_vectorPeriodicJet (L := L) (by omega : 0 < 1) u x)
  have hderiv0 : deriv (fun y : ℝ => q0 (y : AddCircle L)) =
      fun y : ℝ => q1 (y : AddCircle L) := funext fun x => (hq0 x).deriv
  have hderiv1 : deriv (fun y : ℝ => q1 (y : AddCircle L)) =
      fun y : ℝ => q2 (y : AddCircle L) := funext fun x => (hq1 x).deriv
  have hq1c1 : ContDiff ℝ 1 (fun y : ℝ => q1 (y : AddCircle L)) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (hq1 x).differentiableAt, ?_⟩
    rw [hderiv1]
    exact q2.continuous.comp (AddCircle.continuous_mk' L)
  have hq0c2 : ContDiff ℝ 2 (fun y : ℝ => q0 (y : AddCircle L)) := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hq0 x).differentiableAt, by simp, ?_⟩
    rw [hderiv0]
    exact hq1c1
  change ∃ q2 : C(AddCircle L, W),
    ContDiff ℝ 2 (fun x : ℝ => q0 (x : AddCircle L)) ∧
    (∀ x : ℝ, HasDerivAt (fun y : ℝ => q1 (y : AddCircle L)) (q2 (x : AddCircle L)) x) ∧
    (∀ x : ℝ, iteratedDeriv 2 (fun y : ℝ => q0 (y : AddCircle L)) x =
      q2 (x : AddCircle L)) ∧
    vectorPeriodicSecondDerivativeLp (L := L) u = ContinuousMap.toLp 2 haarAddCircle ℝ q2
  refine ⟨q2, hq0c2, hq1, ?_, ?_⟩
  · intro x
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, hderiv0] using (hq1 x).deriv
  · have hcoord (i : ι) : (A i).compLpL 2 haarAddCircle (D (C i u)) =
        ContinuousMap.toLp 2 haarAddCircle ℝ (h i) := by
      change (A i).compLpL 2 haarAddCircle
        (periodicH1DerivativeLp (periodicH2JetCoordinates (L := L) 1 (by omega) (C i u))) = _
      rw [periodicH2_secondDerivativeLp_eq (C i u) (g i) (hg i)]
      apply Lp.ext
      filter_upwards [(A i).coeFn_compLpL (ContinuousMap.toLp 2 haarAddCircle ℂ (g i)),
        ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℂ) (g i),
        ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) (h i)] with x hA hgx hhx
      rw [hA, hgx, hhx]
      rfl
    change (∑ i, ((A i).compLpL 2 haarAddCircle).comp
      ((D.restrictScalars ℝ).comp (C i))) u = ContinuousMap.toLp 2 haarAddCircle ℝ (∑ i, h i)
    rw [map_sum]
    simp only [sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', hcoord]

end PoincareConjecture.M63

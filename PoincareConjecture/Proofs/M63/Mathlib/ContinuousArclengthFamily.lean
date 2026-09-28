import PoincareConjecture.Proofs.M63.Mathlib.PeriodicArclength
import PoincareConjecture.Proofs.M63.Mathlib.ContinuousOrderIsoInverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Instances.AddCircle.Real










set_option autoImplicit false

open Set MeasureTheory
open scoped Topology ContDiff

universe u

namespace PoincareConjecture.M63




theorem exists_continuous_C2_arclength_family
    {Z : Type u} [TopologicalSpace Z] {L0 : ℝ} [Fact (0 < L0)]
    (V V1 : Z → C(AddCircle L0, ℝ))
    (hV : Continuous V) (hV1 : Continuous V1)
    (hder : ∀ (z : Z) (x : ℝ),
      HasDerivAt (fun y : ℝ => V z (y : AddCircle L0))
        (V1 z (x : AddCircle L0)) x)
    (hpos : ∀ (z : Z) (x : ℝ), 0 < V z (x : AddCircle L0)) :
    let v := fun (z : Z) (x : ℝ) => V z (x : AddCircle L0)
    let v1 := fun (z : Z) (x : ℝ) => V1 z (x : AddCircle L0)
    let m := fun z => (∫ x in (0 : ℝ)..L0, v z x) / L0
    (∀ z, 0 < m z) ∧ Continuous m ∧
      ∃ phi : Z → (ℝ ≃o ℝ),
        (∀ z,
          (∀ x, phi z x = (m z)⁻¹ * ∫ y in (0 : ℝ)..x, v z y) ∧
          ContDiff ℝ 2 (phi z : ℝ → ℝ) ∧
          ContDiff ℝ 2 ((phi z).symm : ℝ → ℝ) ∧
          phi z 0 = 0 ∧
          (∀ x, phi z (x + L0) = phi z x + L0) ∧
          (∀ x, (phi z).symm (x + L0) = (phi z).symm x + L0) ∧
          (∀ x, HasDerivAt (phi z) (v z x / m z) x) ∧
          (∀ x, HasDerivAt (deriv (phi z : ℝ → ℝ)) (v1 z x / m z) x) ∧
          (∀ x, HasDerivAt (phi z).symm (m z / v z ((phi z).symm x)) x) ∧
          (∀ x, HasDerivAt (deriv ((phi z).symm : ℝ → ℝ))
            (-(m z ^ 2 * v1 z ((phi z).symm x)) /
              v z ((phi z).symm x) ^ 3) x) ∧
          ∀ x, 0 < deriv (phi z : ℝ → ℝ) x ∧
            0 < deriv ((phi z).symm : ℝ → ℝ) x) ∧
        Continuous (fun p : Z × ℝ => phi p.1 p.2) ∧
        Continuous (fun p : Z × ℝ => deriv (phi p.1 : ℝ → ℝ) p.2) ∧
        Continuous (fun p : Z × ℝ => deriv (deriv (phi p.1 : ℝ → ℝ)) p.2) ∧
        Continuous (fun p : Z × ℝ => (phi p.1).symm p.2) ∧
        Continuous (fun p : Z × ℝ => deriv ((phi p.1).symm : ℝ → ℝ) p.2) ∧
        Continuous (fun p : Z × ℝ =>
          deriv (deriv ((phi p.1).symm : ℝ → ℝ)) p.2) := by
  classical
  dsimp only
  let v := fun (z : Z) (x : ℝ) => V z (x : AddCircle L0)
  let v1 := fun (z : Z) (x : ℝ) => V1 z (x : AddCircle L0)
  let m := fun z => (∫ x in (0 : ℝ)..L0, v z x) / L0
  have hL : 0 < L0 := Fact.out
  have hvc : Continuous (Function.uncurry v) :=
    continuous_eval.comp ((hV.comp continuous_fst).prodMk
      ((AddCircle.continuous_mk' L0).comp continuous_snd))
  have hv1c : Continuous (Function.uncurry v1) :=
    continuous_eval.comp ((hV1.comp continuous_fst).prodMk
      ((AddCircle.continuous_mk' L0).comp continuous_snd))
  have hv (z : Z) : ContDiff ℝ 1 (v z) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (hder z x).differentiableAt, ?_⟩
    have heq : deriv (v z) = v1 z := funext fun x => (hder z x).deriv
    rw [heq]
    exact hv1c.comp (continuous_const.prodMk continuous_id)
  have hperiod (z : Z) : Function.Periodic (v z) L0 := by
    intro x
    simp only [v, AddCircle.coe_add_period]
  have hhome (z : Z) :=
    exists_periodic_arclength_homeomorph hL (hv z) (hperiod z) (hpos z)
  have hmpos (z : Z) : 0 < m z := div_pos (hhome z).1 hL
  choose H hformula hHC2 hHinvC2 hzero hshift hinvshift hd hid using
    fun z => (hhome z).2
  have hmono (z : Z) : StrictMono (H z) :=
    strictMono_of_hasDerivAt_pos (fun x => (hd z x).1)
      (fun x => mul_pos (div_pos hL (hhome z).1) (hpos z x))
  let phi : Z → (ℝ ≃o ℝ) := fun z =>
    StrictMono.orderIsoOfSurjective (H z) (hmono z) (H z).surjective
  have hphi (z : Z) : (phi z : ℝ → ℝ) = H z := rfl
  have hpsi (z : Z) : ((phi z).symm : ℝ → ℝ) = (H z).symm := by
    funext x
    apply (H z).injective
    rw [(H z).apply_symm_apply]
    exact (phi z).apply_symm_apply x
  have hform (z : Z) (x : ℝ) :
      phi z x = (m z)⁻¹ * ∫ y in (0 : ℝ)..x, v z y := by
    rw [show phi z x = H z x from rfl, hformula]
    simp only [m, inv_div]
  have hd' (z : Z) (x : ℝ) : HasDerivAt (phi z) (v z x / m z) x := by
    rw [hphi]
    convert (hd z x).1 using 1
    dsimp only [m]
    field_simp
  have hid' (z : Z) (x : ℝ) :
      HasDerivAt (phi z).symm (m z / v z ((phi z).symm x)) x := by
    rw [hpsi]
    convert (hid z x).1 using 1
    dsimp only [m]
    field_simp
  have hderiv (z : Z) : deriv (phi z : ℝ → ℝ) = fun x => v z x / m z :=
    funext fun x => (hd' z x).deriv
  have hinderiv (z : Z) : deriv ((phi z).symm : ℝ → ℝ) =
      fun x => m z / v z ((phi z).symm x) := funext fun x => (hid' z x).deriv
  have hdd (z : Z) (x : ℝ) :
      HasDerivAt (deriv (phi z : ℝ → ℝ)) (v1 z x / m z) x := by
    rw [hderiv]
    exact (hder z x).div_const (m z)
  have hidd (z : Z) (x : ℝ) : HasDerivAt (deriv ((phi z).symm : ℝ → ℝ))
      (-(m z ^ 2 * v1 z ((phi z).symm x)) / v z ((phi z).symm x) ^ 3) x := by
    rw [hinderiv]
    have hc := (hder z ((phi z).symm x)).comp x (hid' z x)
    convert (hasDerivAt_const x (m z)).div hc (hpos z _).ne' using 1 <;>
      first | rfl | (simp only [Function.comp_apply]; field_simp; ring)
  have hprimitive : Continuous (fun p : Z × ℝ => ∫ y in (0 : ℝ)..p.2, v p.1 y) :=
    intervalIntegral.continuous_parametric_primitive_of_continuous hvc
  have hmc : Continuous m :=
    (hprimitive.comp (continuous_id.prodMk continuous_const)).div_const L0
  have hmprod : Continuous (fun p : Z × ℝ => m p.1) := hmc.comp continuous_fst
  have hphic : Continuous (fun p : Z × ℝ => phi p.1 p.2) := by
    have hminv : Continuous (fun p : Z × ℝ => (m p.1)⁻¹) :=
      hmprod.inv₀ (fun p => (hmpos p.1).ne')
    have hc : Continuous (fun p : Z × ℝ =>
        (m p.1)⁻¹ * ∫ y in (0 : ℝ)..p.2, v p.1 y) := hminv.mul hprimitive
    exact hc.congr (fun p => (hform p.1 p.2).symm)
  have hfixed (x : ℝ) : Continuous (fun z : Z => phi z x) :=
    hphic.comp (f := fun z : Z => (z, x)) (continuous_id.prodMk continuous_const)
  have hpsic := continuous_inverse_orderIso_family (Z := Z) phi hfixed
  have hdc : Continuous (fun p : Z × ℝ => deriv (phi p.1 : ℝ → ℝ) p.2) := by
    have hc : Continuous (fun p : Z × ℝ => v p.1 p.2 / m p.1) :=
      hvc.div hmprod (fun p => (hmpos p.1).ne')
    exact hc.congr (fun p => (hd' p.1 p.2).deriv.symm)
  have hddc : Continuous
      (fun p : Z × ℝ => deriv (deriv (phi p.1 : ℝ → ℝ)) p.2) := by
    have hc : Continuous (fun p : Z × ℝ => v1 p.1 p.2 / m p.1) :=
      hv1c.div hmprod (fun p => (hmpos p.1).ne')
    exact hc.congr (fun p => (hdd p.1 p.2).deriv.symm)
  have hcompv : Continuous (fun p : Z × ℝ => v p.1 ((phi p.1).symm p.2)) :=
    hvc.comp (continuous_fst.prodMk hpsic)
  have hcompv1 : Continuous (fun p : Z × ℝ => v1 p.1 ((phi p.1).symm p.2)) :=
    hv1c.comp (continuous_fst.prodMk hpsic)
  have hidc : Continuous
      (fun p : Z × ℝ => deriv ((phi p.1).symm : ℝ → ℝ) p.2) := by
    have hc : Continuous (fun p : Z × ℝ => m p.1 / v p.1 ((phi p.1).symm p.2)) :=
      hmprod.div hcompv (fun p => (hpos p.1 _).ne')
    exact hc.congr (fun p => (hid' p.1 p.2).deriv.symm)
  have hiddc : Continuous
      (fun p : Z × ℝ => deriv (deriv ((phi p.1).symm : ℝ → ℝ)) p.2) := by
    have hc : Continuous (fun p : Z × ℝ =>
        -(m p.1 ^ 2 * v1 p.1 ((phi p.1).symm p.2)) /
          v p.1 ((phi p.1).symm p.2) ^ 3) :=
      ((hmprod.pow 2).mul hcompv1).neg.div
        (hcompv.pow 3) (fun p => pow_ne_zero 3 (hpos p.1 _).ne')
    exact hc.congr (fun p => (hidd p.1 p.2).deriv.symm)
  refine ⟨hmpos, hmc, phi, ?_, hphic, hdc, hddc, hpsic, hidc, hiddc⟩
  intro z
  refine ⟨hform z, ?_, ?_, ?_, ?_, ?_, hd' z, hdd z, hid' z, hidd z, ?_⟩
  · rw [hphi]
    exact hHC2 z
  · rw [hpsi]
    exact hHinvC2 z
  · exact hzero z
  · exact hshift z
  · simpa only [hpsi] using hinvshift z
  · intro x
    exact ⟨(hd' z x).deriv.symm ▸ div_pos (hpos z x) (hmpos z),
      (hid' z x).deriv.symm ▸ div_pos (hmpos z) (hpos z _)⟩

end PoincareConjecture.M63

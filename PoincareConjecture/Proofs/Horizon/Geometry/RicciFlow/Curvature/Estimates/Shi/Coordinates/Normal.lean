import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.ScalarHessian
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.ScalarBracket
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.ScalarChainRule
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Coordinates.Connection
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Tactic

set_option autoImplicit false

open Set Filter Function
open scoped Topology Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option backward.isDefEq.respectTransparency false in
theorem hessian_symm_on (D : LeviCivitaData g) {U : Set M} {f : M → ℝ}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {x : M} (hx : x ∈ U) (a b : TangentSpace (𝓡 n) x) :
    D.hessian f x a b = D.hessian f x b a := by
  let t := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let O := U ∩ t.baseSet
  have hO : IsOpen O := hU.inter t.open_baseSet
  have hxO : x ∈ O := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
  have hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% X) O := (contMDiffOn_extend_baseSet a).mono inter_subset_right
  have hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% Y) O := (contMDiffOn_extend_baseSet b).mono inter_subset_right
  have hbr := mvfderiv_mlieBracket hO (hf.mono inter_subset_left) hX hY hxO
  have hc := congrArg (mvfderiv (𝓡 n) f x)
    (connection_commutator D
      ((hX.contMDiffAt (hO.mem_nhds hxO)).mdifferentiableAt (by simp))
      ((hY.contMDiffAt (hO.mem_nhds hxO)).mdifferentiableAt (by simp)))
  simp only [map_sub, X, Y, FiberBundle.extend_apply_self] at hc hbr
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self]
  linarith only [hc, hbr]

theorem hessian_const (D : LeviCivitaData g) (c : ℝ) (x : M)
    (a b : TangentSpace (𝓡 n) x) : D.hessian (fun _ : M => c) x a b = 0 := by
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    mvfderiv_const, ContinuousLinearMap.zero_apply, sub_zero]

set_option backward.isDefEq.respectTransparency false in
theorem hessian_add_on (D : LeviCivitaData g) {U : Set M} {f h : M → ℝ}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h U) {x : M} (hx : x ∈ U)
    (a b : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => f y + h y) x a b = D.hessian f x a b + D.hessian h x a b := by
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
  let df := fun y => mvfderiv (𝓡 n) f y (Y y)
  let dh := fun y => mvfderiv (𝓡 n) h y (Y y)
  have hfd {y : M} (hy : y ∈ U) :=
    (hf.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hhd {y : M} (hy : y ∈ U) :=
    (hh.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hdf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) df x :=
    (contMDiffAt_directional_derivative (hf.contMDiffAt (hU.mem_nhds hx))
      (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) b)).mdifferentiableAt (by simp)
  have hdh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) dh x :=
    (contMDiffAt_directional_derivative (hh.contMDiffAt (hU.mem_nhds hx))
      (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) b)).mdifferentiableAt (by simp)
  have he : (fun y => mvfderiv (𝓡 n) (fun z => f z + h z) y (Y y)) =ᶠ[𝓝 x]
      (fun y => df y + dh y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simp only [mvfderiv_fun_add (hfd hy) (hhd hy), add_apply, df, dh]
  have he' : mvfderiv (𝓡 n)
      (fun y => mvfderiv (𝓡 n) (fun z => f z + h z) y (Y y)) x =
      mvfderiv (𝓡 n) (fun y => df y + dh y) x := he.mfderiv_eq
  have hd := congrArg (fun A : TangentSpace (𝓡 n) x →L[ℝ] ℝ => A a) he'
  rw [mvfderiv_fun_add hdf hdh] at hd
  simp only [add_apply] at hd
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self, mvfderiv_fun_add (hfd hx) (hhd hx), add_apply]
  change _ - _ =
    (mvfderiv (𝓡 n) df x a - mvfderiv (𝓡 n) f x (D.connection Y x a)) +
    (mvfderiv (𝓡 n) dh x a - mvfderiv (𝓡 n) h x (D.connection Y x a))
  change mvfderiv (𝓡 n)
    (fun y => mvfderiv (𝓡 n) (fun z => f z + h z) y (Y y)) x a = _ at hd
  rw [hd]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem hessian_mul_on (D : LeviCivitaData g) {U : Set M} {f h : M → ℝ}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h U) {x : M} (hx : x ∈ U)
    (a b : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => f y * h y) x a b =
      f x * D.hessian h x a b + h x * D.hessian f x a b +
        mvfderiv (𝓡 n) f x a * mvfderiv (𝓡 n) h x b +
        mvfderiv (𝓡 n) h x a * mvfderiv (𝓡 n) f x b := by
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
  let df := fun y => mvfderiv (𝓡 n) f y (Y y)
  let dh := fun y => mvfderiv (𝓡 n) h y (Y y)
  have hfd {y : M} (hy : y ∈ U) :=
    (hf.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hhd {y : M} (hy : y ∈ U) :=
    (hh.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hdf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) df x :=
    (contMDiffAt_directional_derivative (hf.contMDiffAt (hU.mem_nhds hx))
      (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) b)).mdifferentiableAt (by simp)
  have hdh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) dh x :=
    (contMDiffAt_directional_derivative (hh.contMDiffAt (hU.mem_nhds hx))
      (FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) b)).mdifferentiableAt (by simp)
  have hprod {y : M} (hy : y ∈ U) (v : TangentSpace (𝓡 n) y) :
      mvfderiv (𝓡 n) (fun z => f z * h z) y v =
        f y * mvfderiv (𝓡 n) h y v + h y * mvfderiv (𝓡 n) f y v := by
    simp only [mvfderiv_fun_mul (hfd hy) (hhd hy), add_apply, smul_apply, smul_eq_mul]
  have he : (fun y => mvfderiv (𝓡 n) (fun z => f z * h z) y (Y y)) =ᶠ[𝓝 x]
      (fun y => f y * dh y + h y * df y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hprod hy (Y y)
  have he' : mvfderiv (𝓡 n)
      (fun y => mvfderiv (𝓡 n) (fun z => f z * h z) y (Y y)) x =
      mvfderiv (𝓡 n) (fun y => f y * dh y + h y * df y) x := he.mfderiv_eq
  have hd := congrArg (fun A : TangentSpace (𝓡 n) x →L[ℝ] ℝ => A a) he'
  erw [mvfderiv_fun_add ((hfd hx).mul hdh) ((hhd hx).mul hdf),
    mvfderiv_fun_mul (hfd hx) hdh, mvfderiv_fun_mul (hhd hx) hdf] at hd
  simp only [add_apply, smul_apply, smul_eq_mul, df, dh, Y,
    FiberBundle.extend_apply_self] at hd
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self]
  rw [hd, hprod hx]
  ring

theorem hessian_const_mul_on (D : LeviCivitaData g) {U : Set M} {f : M → ℝ}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {x : M} (hx : x ∈ U) (c : ℝ) (a b : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => c * f y) x a b = c * D.hessian f x a b := by
  simpa only [hessian_const, mvfderiv_const, ContinuousLinearMap.zero_apply,
    mul_zero, zero_mul, add_zero] using
    hessian_mul_on D hU (contMDiffOn_const (c := c)) hf hx a b

theorem hessian_finset_sum_on (D : LeviCivitaData g) {ι : Type*}
    (s : Finset ι) {U : Set M} {f : ι → M → ℝ}
    (hU : IsOpen U) (hf : ∀ i ∈ s, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) U)
    {x : M} (hx : x ∈ U) (a b : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => ∑ i ∈ s, f i y) x a b = ∑ i ∈ s, D.hessian (f i) x a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, hessian_const]
  | @insert i s his ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j) U :=
      fun j hj => hf j (Finset.mem_insert_of_mem hj)
    simp only [Finset.sum_insert his]
    rw [hessian_add_on D hU hfi (contMDiffOn_finsetSum hfs) hx, ih hfs]

set_option backward.isDefEq.respectTransparency false in
theorem exists_hessian_continuous_bilinear_on [T2Space M] (D : LeviCivitaData g)
    {U : Set M} {f : M → ℝ} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) {q : M} (hq : q ∈ U) :
    ∃ B : TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q →L[ℝ] ℝ,
      ∀ a b, D.hessian f q a b = B a b := by
  obtain ⟨A, hA⟩ := exists_hessian_bilinear_of_contMDiffOn D hU hf hq
  let T := TangentSpace (𝓡 n) q
  letI : FiniteDimensional ℝ T :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) q
  let B₀ : T →ₗ[ℝ] T →ₗ[ℝ] ℝ :=
    (MultilinearMap.ofSubsingletonₗ ℝ ℝ T ℝ (0 : Fin 1)).symm.toLinearMap.comp
      A.curryLeft
  let B : T →L[ℝ] T →L[ℝ] ℝ :=
    ((LinearMap.toContinuousLinearMap : (T →ₗ[ℝ] ℝ) ≃ₗ[ℝ] T →L[ℝ] ℝ).toLinearMap.comp
      B₀).toContinuousLinearMap
  refine ⟨B, ?_⟩
  intro a b
  change D.hessian f q a b = A (Fin.cons a (fun _ : Fin 1 => b))
  simpa only [Fin.cons_zero, Fin.cons_one] using hA (Fin.cons a (fun _ : Fin 1 => b))

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem hessian_basis_expansion_on [T2Space M] (D : LeviCivitaData g)
    {U : Set M} {f : M → ℝ} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) {q : M} (hq : q ∈ U)
    (J : E →L[ℝ] TangentSpace (𝓡 n) q) (u v : E) :
    D.hessian f q (J u) (J v) =
      ∑ j : Fin n, ∑ k : Fin n,
        (u j * v k) * D.hessian f q
          (J (EuclideanSpace.basisFun (Fin n) ℝ j))
          (J (EuclideanSpace.basisFun (Fin n) ℝ k)) := by
  classical
  obtain ⟨B, hB⟩ := exists_hessian_continuous_bilinear_on D hU hf hq
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have he (w : E) : J w = ∑ i : Fin n, w i • J (e i) := by
    have hw : (∑ i : Fin n, w i • e i) = w := by
      simpa only [EuclideanSpace.basisFun_repr, e] using e.sum_repr w
    calc
      J w = J (∑ i : Fin n, w i • e i) := congrArg J hw.symm
      _ = ∑ i : Fin n, w i • J (e i) := by simp only [map_sum, map_smul]
  rw [hB]
  calc
    B (J u) (J v) = ∑ j : Fin n, u j * B (J (e j)) (J v) := by
      rw [he u]
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    _ = ∑ j : Fin n, ∑ k : Fin n,
        (u j * v k) * B (J (e j)) (J (e k)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [he v]
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, mul_assoc]
    _ = _ := by simp only [← hB, e]

noncomputable def shiQuadraticCorrection (C : Fin n → Fin n → Fin n → ℝ) (w : E) : E :=
  w + ∑ i : Fin n,
    ((-1 / 2 : ℝ) * ∑ j : Fin n, ∑ k : Fin n, C i j k * (w j * w k)) •
      EuclideanSpace.basisFun (Fin n) ℝ i

theorem shiQuadraticCorrection_apply (C : Fin n → Fin n → Fin n → ℝ)
    (w : E) (i : Fin n) :
    shiQuadraticCorrection C w i =
      w i + (-1 / 2 : ℝ) * ∑ j : Fin n, ∑ k : Fin n, C i j k * (w j * w k) := by
  classical
  let p : E →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i
  change p (shiQuadraticCorrection C w) = _
  simp [shiQuadraticCorrection, map_add, map_sum, map_smul, p,
    EuclideanSpace.basisFun_apply, PiLp.single_apply]

@[simp] theorem shiQuadraticCorrection_zero (C : Fin n → Fin n → Fin n → ℝ) :
    shiQuadraticCorrection C 0 = 0 := by
  simp [shiQuadraticCorrection]

theorem contDiff_shiQuadraticCorrection (C : Fin n → Fin n → Fin n → ℝ) :
    ContDiff ℝ ∞ (shiQuadraticCorrection C) := by
  apply contDiff_id.add
  apply ContDiff.sum
  intro i hi
  apply ContDiff.smul_const
  apply contDiff_const.mul
  apply ContDiff.sum
  intro j hj
  apply ContDiff.sum
  intro k hk
  exact contDiff_const.mul
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).contDiff.mul
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k).contDiff)

theorem hasFDerivAt_shiQuadraticCorrection_zero
    (C : Fin n → Fin n → Fin n → ℝ) :
    HasFDerivAt (shiQuadraticCorrection C) (ContinuousLinearMap.id ℝ E) 0 := by
  have hp (j k : Fin n) :
      HasFDerivAt (fun w : E => w j * w k) (0 : E →L[ℝ] ℝ) 0 := by
    let pj : E →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j
    let pk : E →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) k
    have hj : HasFDerivAt (fun w : E => w j) pj 0 := pj.hasFDerivAt
    have hk : HasFDerivAt (fun w : E => w k) pk 0 := pk.hasFDerivAt
    simpa +instances using! hj.mul hk
  have hs (i : Fin n) : HasFDerivAt
      (fun w : E => ∑ j : Fin n, ∑ k : Fin n, C i j k * (w j * w k))
      (0 : E →L[ℝ] ℝ) 0 := by
    simpa using HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hp j k).const_mul (C i j k)))
  have ht (i : Fin n) : HasFDerivAt
      (fun w : E => ((-1 / 2 : ℝ) * ∑ j : Fin n, ∑ k : Fin n,
          C i j k * (w j * w k)) • EuclideanSpace.basisFun (Fin n) ℝ i)
      (0 : E →L[ℝ] E) 0 := by
    simpa using ((hs i).const_mul (-1 / 2 : ℝ)).smul_const
      (EuclideanSpace.basisFun (Fin n) ℝ i)
  simpa +instances only [shiQuadraticCorrection, Pi.add_apply, id_eq,
    Finset.sum_const_zero, add_zero] using!
    (hasFDerivAt_id (𝕜 := ℝ) (0 : E)).add
      (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ht i))

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem hessian_shiQuadraticCorrection_zero [T2Space M] (D : LeviCivitaData g)
    {U : Set M} {h : M → E} (hU : IsOpen U)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ h U) {q : M} (hq : q ∈ U)
    (hzero : h q = 0) (J : E ≃L[ℝ] TangentSpace (𝓡 n) q)
    (hd : ∀ v, mfderiv (𝓡 n) 𝓘(ℝ, E) h q (J v) = v) (i : Fin n) (u v : E) :
    D.hessian
      (fun y => shiQuadraticCorrection
        (fun i j k => D.hessian (fun x => h x i) q
          (J (EuclideanSpace.basisFun (Fin n) ℝ j))
          (J (EuclideanSpace.basisFun (Fin n) ℝ k))) (h y) i) q (J u) (J v) = 0 := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let f (i : Fin n) : M → ℝ := fun y => h y i
  let C (i j k : Fin n) := D.hessian (f i) q (J (e j)) (J (e k))
  have hf (j : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f j) U :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j).contMDiff.comp_contMDiffOn hh
  have hf0 (j : Fin n) : f j q = 0 := by simp [f, hzero]
  have hfd (j : Fin n) (w : E) : mvfderiv (𝓡 n) (f j) q (J w) = w j := by
    let p : E →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) j
    have hhD := (hh.contMDiffAt (hU.mem_nhds hq)).mdifferentiableAt (by simp)
    calc
      mvfderiv (𝓡 n) (f j) q (J w) = (mvfderiv (𝓡 n) h q (J w)) j := by
        change mvfderiv (𝓡 n) (p ∘ h) q (J w) = _
        rw [mvfderiv_comp_apply q p.differentiableAt.mdifferentiableAt hhD]
        simpa only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] using!
          congrArg (fun K : E →L[ℝ] ℝ => K (mvfderiv (𝓡 n) h q (J w)))
            (p.fderiv (x := h q))
      _ = w j := by
        have hw : mvfderiv (𝓡 n) h q (J w) = w := by
          change (mfderiv (𝓡 n) 𝓘(ℝ, E) h q (J w) : E) = w
          exact hd w
        exact congrArg (fun z : E => z j) hw
  let S : M → ℝ := fun y =>
    ∑ j : Fin n, ∑ k : Fin n, C i j k * (f j y * f k y)
  have hs : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ S U :=
    contMDiffOn_finsetSum (fun j _ => contMDiffOn_finsetSum
      (fun k _ => contMDiffOn_const.mul ((hf j).mul (hf k))))
  have hprod (j k : Fin n) :
      D.hessian (fun y => f j y * f k y) q (J u) (J v) =
        u j * v k + u k * v j := by
    rw [hessian_mul_on D hU (hf j) (hf k) hq, hf0, hf0, hfd, hfd, hfd, hfd]
    ring
  have huv : D.hessian (f i) q (J u) (J v) =
      ∑ j : Fin n, ∑ k : Fin n, (u j * v k) * C i j k :=
    hessian_basis_expansion_on D hU (hf i) hq J.toContinuousLinearMap u v
  have hvu : D.hessian (f i) q (J v) (J u) =
      ∑ j : Fin n, ∑ k : Fin n, (v j * u k) * C i j k :=
    hessian_basis_expansion_on D hU (hf i) hq J.toContinuousLinearMap v u
  have hsum : D.hessian S q (J u) (J v) =
      D.hessian (f i) q (J u) (J v) + D.hessian (f i) q (J v) (J u) := by
    have ht (j k : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => C i j k * (f j y * f k y)) U :=
      contMDiffOn_const.mul ((hf j).mul (hf k))
    calc
      _ = ∑ j : Fin n, D.hessian
          (fun y => ∑ k : Fin n, C i j k * (f j y * f k y)) q (J u) (J v) :=
        hessian_finset_sum_on D Finset.univ hU
          (fun j _ => contMDiffOn_finsetSum (fun k _ => ht j k)) hq (J u) (J v)
      _ = ∑ j : Fin n, ∑ k : Fin n,
          C i j k * (u j * v k + u k * v j) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          _ = ∑ k : Fin n, D.hessian
              (fun y => C i j k * (f j y * f k y)) q (J u) (J v) :=
            hessian_finset_sum_on D Finset.univ hU (fun k _ => ht j k) hq (J u) (J v)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro k hk
            have hm : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
                (fun y => f j y * f k y) U := (hf j).mul (hf k)
            exact (hessian_const_mul_on D hU hm hq (C i j k) (J u) (J v)).trans
              (congrArg (fun r : ℝ => C i j k * r) (hprod j k))
      _ = _ := by
        rw [huv, hvu]
        simp_rw [mul_add, Finset.sum_add_distrib]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj <;>
          apply Finset.sum_congr rfl <;> intro k hk <;> ring
  have he : (fun y => shiQuadraticCorrection C (h y) i) =
      (fun y => f i y + (-1 / 2 : ℝ) * S y) := by
    funext y
    exact shiQuadraticCorrection_apply C (h y) i
  change D.hessian (fun y => shiQuadraticCorrection C (h y) i) q (J u) (J v) = 0
  rw [he]
  have hscale : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (-1 / 2 : ℝ) * S y) U := contMDiffOn_const.mul hs
  calc
    _ = D.hessian (f i) q (J u) (J v) +
        D.hessian (fun y => (-1 / 2 : ℝ) * S y) q (J u) (J v) :=
      hessian_add_on D hU (hf i) hscale hq (J u) (J v)
    _ = D.hessian (f i) q (J u) (J v) +
        (-1 / 2 : ℝ) * D.hessian S q (J u) (J v) :=
      congrArg (fun r : ℝ => D.hessian (f i) q (J u) (J v) + r)
        (hessian_const_mul_on D hU hs hq (-1 / 2 : ℝ) (J u) (J v))
    _ = 0 := by
      rw [hsum]
      have hsym := hessian_symm_on D hU (hf i) hq (J v) (J u)
      linarith only [hsym]

theorem exists_shiQuadraticCorrection_homeomorph
    (C : Fin n → Fin n → Fin n → ℝ) :
    ∃ c : OpenPartialHomeomorph E E,
      (c : E → E) = shiQuadraticCorrection C ∧ 0 ∈ c.source ∧
      ContDiffOn ℝ ∞ c c.source ∧ ContDiffOn ℝ ∞ c.symm c.target := by
  let Q := shiQuadraticCorrection C
  have hQ : ContDiff ℝ ∞ Q := contDiff_shiQuadraticCorrection C
  have hd : HasFDerivAt Q
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 :=
    hasFDerivAt_shiQuadraticCorrection_zero C
  let c₀ := hQ.contDiffAt.toOpenPartialHomeomorph Q hd (by simp)
  let U : Set E := (fderiv ℝ Q) ⁻¹'
    Set.range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E)
  have hU : IsOpen U :=
    ContinuousLinearEquiv.isOpen.preimage
      ((hQ.fderiv_right (m := ∞) (by simp)).continuous)
  have h0U : (0 : E) ∈ U := ⟨ContinuousLinearEquiv.refl ℝ E, hd.fderiv.symm⟩
  let c := c₀.restrOpen U hU
  have hc : (c : E → E) = Q := rfl
  have h0 : (0 : E) ∈ c.source :=
    ⟨hQ.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp), h0U⟩
  refine ⟨c, hc, h0, ?_, ?_⟩
  · rw [hc]
    exact hQ.contDiffOn
  · intro w hw
    have hcw : c.symm w ∈ U := (c.map_target hw).2
    obtain ⟨A, hA⟩ := hcw
    apply ContDiffAt.contDiffWithinAt
    apply c.contDiffAt_symm hw (f₀' := A)
    · rw [hc, hA]
      exact (hQ.differentiable (by simp) (c.symm w)).hasFDerivAt
    · rw [hc]
      exact hQ.contDiffAt

set_option backward.isDefEq.respectTransparency false in
theorem exists_shi_metric_frame (g : RiemannianMetric n M) (q : M) :
    ∃ (J : E ≃L[ℝ] TangentSpace (𝓡 n) q)
      (σ : Fin n ≃ Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q))),
      (∀ i, J (EuclideanSpace.basisFun (Fin n) ℝ i) = g.orthonormalBasis q (σ i)) ∧
      ∀ u v, g.inner q (J u) (J v) = inner ℝ u v := by
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) q) = n := by
    change Module.finrank ℝ E = n
    simp
  let σ : Fin n ≃ Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q)) :=
    finCongr hdim.symm
  let K : E ≃ₗ[ℝ] TangentSpace (𝓡 n) q :=
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ((EuclideanSpace.basisFun (Fin n) ℝ).equiv (g.orthonormalBasis q) σ).toLinearEquiv
  refine ⟨K.toContinuousLinearEquiv, σ, ?_, ?_⟩
  · intro i
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact (EuclideanSpace.basisFun (Fin n) ℝ).equiv_apply_basis (g.orthonormalBasis q) σ i
  · intro u v
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact ((EuclideanSpace.basisFun (Fin n) ℝ).equiv (g.orthonormalBasis q) σ).inner_map_map u v

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_shi_normalized_chart (q : M) (J : E ≃L[ℝ] TangentSpace (𝓡 n) q) :
    ∃ h : OpenPartialHomeomorph M E,
      q ∈ h.source ∧ h q = 0 ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ h h.source ∧
      ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ h.symm h.target ∧
      ∀ v, mfderiv (𝓡 n) 𝓘(ℝ, E) h q (J v) = v := by
  let c := chartAt E q
  have hqc : q ∈ c.source := mem_chart_source E q
  let A : TangentSpace (𝓡 n) q ≃L[ℝ] E :=
    (mdifferentiable_chart (I := 𝓡 n) q).mfderiv hqc
  let L : E ≃L[ℝ] E := J.trans A
  let a : E ≃ₜ E := (Homeomorph.subRight (c q)).trans L.symm.toHomeomorph
  let h := c.trans a.toOpenPartialHomeomorph
  have hs : h.source = c.source := by
    simp [h]
  have hh (y : M) : h y = L.symm (c y - c q) := rfl
  have hi (w : E) : h.symm w = c.symm (L w + c q) := rfl
  have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source :=
    contMDiffOn_chart (I := 𝓡 n)
  have hci : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target :=
    contMDiffOn_chart_symm (I := 𝓡 n)
  have hhSmooth : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ h h.source := by
    rw [hs]
    exact L.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn (hc.sub contMDiffOn_const)
  have hiSmooth : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ h.symm h.target := by
    apply hci.comp (L.toContinuousLinearMap.contMDiff.add contMDiff_const).contMDiffOn
    intro w hw
    exact hw.2
  refine ⟨h, hs.symm ▸ hqc, ?_, hhSmooth, hiSmooth, ?_⟩
  · simp [hh]
  · intro v
    have hcD := (hc.contMDiffAt (c.open_source.mem_nhds hqc)).mdifferentiableAt (by simp)
    have ha : HasFDerivAt (fun w : E => L.symm (w - c q))
        (L.symm : E →L[ℝ] E) (c q) := by
      simpa only [sub_zero, ContinuousLinearMap.comp_id, Function.comp_def, Pi.sub_apply,
        id_eq] using L.symm.hasFDerivAt.comp (c q)
        ((hasFDerivAt_id (𝕜 := ℝ) (c q)).sub (hasFDerivAt_const (c q) (c q)))
    change mfderiv (𝓡 n) 𝓘(ℝ, E) ((fun w : E => L.symm (w - c q)) ∘ c) q (J v) = v
    rw [mfderiv_comp_apply q ha.differentiableAt.mdifferentiableAt hcD,
      mfderiv_eq_fderiv, ha.fderiv]
    change L.symm (L v) = v
    exact L.symm_apply_apply v

set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_shi_normal_chart [T2Space M] (D : LeviCivitaData g) (q : M) :
    ∃ (c : OpenPartialHomeomorph M E) (J : E ≃L[ℝ] TangentSpace (𝓡 n) q)
      (σ : Fin n ≃ Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q))),
      q ∈ c.source ∧ c q = 0 ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target ∧
      (∀ i, J (EuclideanSpace.basisFun (Fin n) ℝ i) = g.orthonormalBasis q (σ i)) ∧
      (∀ u v, g.inner q (J u) (J v) = inner ℝ u v) ∧
      mfderiv (𝓡 n) 𝓘(ℝ, E) c q = (J.symm : TangentSpace (𝓡 n) q →L[ℝ] E) ∧
      ∀ i a b, D.hessian (fun y => c y i) q a b = 0 := by
  classical
  obtain ⟨J, σ, hJ, hJinner⟩ := exists_shi_metric_frame g q
  obtain ⟨h, hq, hzero, hh, hi, hd⟩ := exists_shi_normalized_chart q J
  let C (i j k : Fin n) := D.hessian (fun y => h y i) q
    (J (EuclideanSpace.basisFun (Fin n) ℝ j))
    (J (EuclideanSpace.basisFun (Fin n) ℝ k))
  obtain ⟨Q, hQ, h0Q, hQs, hQi⟩ := exists_shiQuadraticCorrection_homeomorph C
  let c := h.trans Q
  have hqc : q ∈ c.source := by
    change q ∈ h.source ∧ h q ∈ Q.source
    exact ⟨hq, by simpa only [hzero] using h0Q⟩
  have hc0 : c q = 0 := by
    change Q (h q) = 0
    rw [hQ, hzero, shiQuadraticCorrection_zero]
  have hcs : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source :=
    hQs.contMDiffOn.comp (hh.mono inter_subset_left) (fun y hy => hy.2)
  have hcis : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target :=
    hi.comp (hQi.contMDiffOn.mono inter_subset_left) (fun w hw => hw.2)
  refine ⟨c, J, σ, hqc, hc0, hcs, hcis, hJ, hJinner, ?_, ?_⟩
  · ext a
    obtain ⟨v, rfl⟩ := J.surjective a
    have hhd := (hh.contMDiffAt (h.open_source.mem_nhds hq)).mdifferentiableAt (by simp)
    have hhqQ : h q ∈ Q.source := by simpa only [hzero] using h0Q
    have hQd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) Q (h q) :=
      ((hQs.contDiffAt (Q.open_source.mem_nhds hhqQ)).differentiableAt (by simp)).mdifferentiableAt
    change mfderiv (𝓡 n) 𝓘(ℝ, E) (Q ∘ h) q (J v) = J.symm (J v)
    rw [mfderiv_comp_apply q hQd hhd, mfderiv_eq_fderiv, hQ, hzero,
      (hasFDerivAt_shiQuadraticCorrection_zero C).fderiv]
    change (mfderiv (𝓡 n) 𝓘(ℝ, E) h q (J v) : E) = J.symm (J v)
    exact (hd v).trans (J.symm_apply_apply v).symm
  · intro i a b
    have he := hessian_shiQuadraticCorrection_zero D h.open_source hh hq hzero J hd i
      (J.symm a) (J.symm b)
    simpa only [c, OpenPartialHomeomorph.trans_apply, hQ,
      ContinuousLinearEquiv.apply_symm_apply, C] using he

set_option backward.isDefEq.respectTransparency false in
theorem shiNormalChartField_at_base
    {c : OpenPartialHomeomorph M E} {q : M}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hq : q ∈ c.source) (J : E ≃L[ℝ] TangentSpace (𝓡 n) q)
    (hd : mvfderiv (𝓡 n) c q =
      (J.symm : TangentSpace (𝓡 n) q →L[ℝ] E)) (v : E) :
    shiChartField c v q = J v := by
  apply J.symm.injective
  calc
    J.symm (shiChartField c v q) = v := by
      simpa +instances only [hd, ContinuousLinearEquiv.coe_coe] using!
        shiChartField_duality hc hi hq v
    _ = J.symm (J v) := (J.symm_apply_apply v).symm

set_option backward.isDefEq.respectTransparency false in
theorem shiNormalChartField_connection_zero [T2Space M]
    (D : LeviCivitaData g) {c : OpenPartialHomeomorph M E} {q : M}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hq : q ∈ c.source)
    (hH : ∀ i a b, D.hessian (shiChartCoordinate c i) q a b = 0) (v : E) :
    D.connection (shiChartField c v) q = 0 := by
  ext a : 1
  change D.connection (shiChartField c v) q a = 0
  have hInv := shiChart_mfderiv_isInvertible hc hi hq
  apply hInv.injective
  change mvfderiv (𝓡 n) c q (D.connection (shiChartField c v) q a) =
    mvfderiv (𝓡 n) c q 0
  rw [map_zero]
  ext i
  have ha : shiChartField c (mvfderiv (𝓡 n) c q a) q = a :=
    hInv.inverse_apply_self a
  have he := shiChartCoordinate_hessian_fields D hc hi hq i
    (mvfderiv (𝓡 n) c q a) v
  rw [hH, ha] at he
  have hz : mvfderiv (𝓡 n) (shiChartCoordinate c i) q
      (D.connection (shiChartField c v) q a) = 0 := neg_eq_zero.mp he.symm
  rw [shiChartCoordinate_derivative hc hq] at hz
  simpa only [PiLp.zero_apply] using hz

set_option backward.isDefEq.respectTransparency false in
theorem shiNormalChart_mvfderiv_comp_at
    {c : OpenPartialHomeomorph M E} {q : M}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hq : q ∈ c.source) (h0 : c q = 0)
    (J : E ≃L[ℝ] TangentSpace (𝓡 n) q)
    (hd : mvfderiv (𝓡 n) c q =
      (J.symm : TangentSpace (𝓡 n) q →L[ℝ] E))
    {P : E → ℝ} (hP : ContDiff ℝ ∞ P) (u : E) :
    mvfderiv (𝓡 n) (P ∘ c) q (J u) = fderiv ℝ P 0 u := by
  have hcD := (hc.contMDiffAt (c.open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have hpD := (hP.differentiable (by simp) (c q)).mdifferentiableAt
  have hdu : (mfderiv (𝓡 n) 𝓘(ℝ, E) c q (J u) : E) = u := by
    change mvfderiv (𝓡 n) c q (J u) = u
    rw [hd]
    exact J.symm_apply_apply u
  calc
    mvfderiv (𝓡 n) (P ∘ c) q (J u) =
        fderiv ℝ P (c q) (mfderiv (𝓡 n) 𝓘(ℝ, E) c q (J u)) := by
      simpa only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] using!
        mvfderiv_comp_apply q hpD hcD (J u)
    _ = fderiv ℝ P 0 u := by rw [hdu, h0]

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem shiNormalChart_hessian_comp_at [T2Space M]
    (D : LeviCivitaData g) {c : OpenPartialHomeomorph M E} {q : M}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hq : q ∈ c.source) (h0 : c q = 0)
    (J : E ≃L[ℝ] TangentSpace (𝓡 n) q)
    (hd : mvfderiv (𝓡 n) c q =
      (J.symm : TangentSpace (𝓡 n) q →L[ℝ] E))
    (hH : ∀ i a b, D.hessian (shiChartCoordinate c i) q a b = 0)
    {P : E → ℝ} (hP : ContDiff ℝ ∞ P) (u v : E) :
    D.hessian (P ∘ c) q (J u) (J v) =
      fderiv ℝ (fderiv ℝ P) 0 u v := by
  let P1 : E → ℝ := fun w => fderiv ℝ P w v
  have hDP : ContDiff ℝ ∞ (fderiv ℝ P) := hP.fderiv_right (m := ∞) (by simp)
  have hP1 : ContDiff ℝ ∞ P1 := hDP.clm_apply contDiff_const
  have hPc : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (P ∘ c) c.source :=
    hP.contMDiff.comp_contMDiffOn hc
  have hGerm :
      (fun y => mvfderiv (𝓡 n) (P ∘ c) y (shiChartField c v y)) =ᶠ[𝓝 q]
        (P1 ∘ c) := by
    filter_upwards [c.open_source.mem_nhds hq] with y hy
    have hcD := (hc.contMDiffAt (c.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
    have hpD := (hP.differentiable (by simp) (c y)).mdifferentiableAt
    have he : mvfderiv (𝓡 n) (P ∘ c) y (shiChartField c v y) =
        fderiv ℝ P (c y) (mvfderiv (𝓡 n) c y (shiChartField c v y)) := by
      simpa only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] using!
        mvfderiv_comp_apply y hpD hcD (shiChartField c v y)
    rw [shiChartField_duality hc hi hy] at he
    exact he
  have hderiv : mvfderiv (𝓡 n)
      (fun y => mvfderiv (𝓡 n) (P ∘ c) y (shiChartField c v y)) q =
      mvfderiv (𝓡 n) (P1 ∘ c) q := hGerm.mfderiv_eq
  have hu := shiNormalChartField_at_base hc hi hq J hd u
  have hv := shiNormalChartField_at_base hc hi hq J hd v
  have hconn := shiNormalChartField_connection_zero D hc hi hq hH v
  calc
    D.hessian (P ∘ c) q (J u) (J v) =
        D.hessianOnFields (P ∘ c) (shiChartField c u) (shiChartField c v) q := by
      simpa only [hu, hv] using
        (hessianOnFields_eq_hessian_of_contMDiffOn D c.open_source hPc
          (shiChartField_smooth hc hi u) (shiChartField_smooth hc hi v) hq).symm
    _ = mvfderiv (𝓡 n) (P1 ∘ c) q (J u) := by
      simp only [LeviCivitaData.hessianOnFields, hderiv, hconn, zero_apply,
        map_zero, sub_zero, hu]
    _ = fderiv ℝ P1 0 u := shiNormalChart_mvfderiv_comp_at hc hq h0 J hd hP1 u
    _ = fderiv ℝ (fderiv ℝ P) 0 u v := by
      have he := ((hDP.differentiable (by simp) (0 : E)).hasFDerivAt.clm_apply
        (hasFDerivAt_const v (0 : E))).fderiv
      simpa only [P1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.comp_zero, add_apply, zero_apply, map_zero, add_zero,
        zero_add] using! congrArg (fun A : E →L[ℝ] ℝ => A u) he

set_option backward.isDefEq.respectTransparency false in
theorem shiNormalChart_scalar_operators [T2Space M]
    (D : LeviCivitaData g) {c : OpenPartialHomeomorph M E} {q : M}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hq : q ∈ c.source) (h0 : c q = 0)
    (J : E ≃L[ℝ] TangentSpace (𝓡 n) q)
    (σ : Fin n ≃ Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q)))
    (hJ : ∀ i, J (EuclideanSpace.basisFun (Fin n) ℝ i) =
      g.orthonormalBasis q (σ i))
    (hd : mvfderiv (𝓡 n) c q =
      (J.symm : TangentSpace (𝓡 n) q →L[ℝ] E))
    (hH : ∀ i a b, D.hessian (shiChartCoordinate c i) q a b = 0)
    {P : E → ℝ} (hP : ContDiff ℝ ∞ P) :
    scalarGradientSq g (P ∘ c) q = ‖fderiv ℝ P 0‖ ^ 2 ∧
      D.laplacian (P ∘ c) q =
        ∑ i : Fin n, fderiv ℝ (fderiv ℝ P) 0
          (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  constructor
  · unfold scalarGradientSq
    rw [← σ.sum_comp (fun i =>
      (mvfderiv (𝓡 n) (P ∘ c) q (g.orthonormalBasis q i)) ^ 2)]
    simp_rw [← hJ, shiNormalChart_mvfderiv_comp_at hc hq h0 J hd hP]
    exact ((EuclideanSpace.basisFun (Fin n) ℝ).norm_dual (fderiv ℝ P 0)).symm
  · change (∑ i, D.hessian (P ∘ c) q
      (g.orthonormalBasis q i) (g.orthonormalBasis q i)) = _
    rw [← σ.sum_comp (fun i => D.hessian (P ∘ c) q
      (g.orthonormalBasis q i) (g.orthonormalBasis q i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hJ i]
    exact shiNormalChart_hessian_comp_at D hc hi hq h0 J hd hH hP
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i)

end PoincareConjecture.RicciFlowAnalysis

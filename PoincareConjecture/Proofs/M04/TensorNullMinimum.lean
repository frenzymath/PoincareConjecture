import PoincareConjecture.Proofs.M04.FixedExtension
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure
import PoincareConjecture.Proofs.M04.ScalarEstimates
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.SesquilinearForm.Basic








set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
theorem exists_local_field_connection_zero (D : LeviCivitaData g)
    (x : M) (u : TangentSpace (𝓡 n) x) :
    ∃ (U : Set M) (X : (y : M) → TangentSpace (𝓡 n) y),
      IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U ∧
      X x = u ∧ D.connection X x = 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let c := extChartAt (𝓡 n) x
  let U := e.baseSet ∩ c.source
  have hU : IsOpen U := e.open_baseSet.inter (isOpen_extChartAt_source x)
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hx : x ∈ U := ⟨hxe, hxc⟩
  let V := FiberBundle.extend E u
  have hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% V) U :=
    (contMDiffOn_extend_baseSet u).mono inter_subset_left
  let L : TangentSpace (𝓡 n) x →L[ℝ] E := mfderiv (𝓡 n) 𝓘(ℝ, E) c x
  have hL : L.IsInvertible := isInvertible_mfderiv_extChartAt hxc
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let A : E →L[ℝ] E := (e.continuousLinearMapAt ℝ x).comp
    ((D.connection V x).comp L.inverse)
  let C (i : Fin n) : E →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap.comp A
  let φ (i : Fin n) : M → ℝ := fun y ↦ C i (c y - c x)
  let S (i : Fin n) := FiberBundle.extend E (e.symmL ℝ x (b i))
  have hS (i : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (S i)) U :=
    (contMDiffOn_extend_baseSet (e.symmL ℝ x (b i))).mono inter_subset_left
  have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c U := by
    apply ContMDiffOn.mono (t := U) ?_ inter_subset_right
    simpa only [c, extChartAt_source] using!
      (contMDiffOn_extChartAt (I := 𝓡 n) (x := x) (n := ∞))
  have hφ (i : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (φ i) U :=
    (C i).contMDiff.comp_contMDiffOn (hc.sub contMDiffOn_const)
  have hφzero (i : Fin n) : φ i x = 0 := by simp [φ]
  have hcD : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) c x :=
    (hc.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hφD (i : Fin n) : mvfderiv (𝓡 n) (φ i) x = (C i).comp L := by
    have he : φ i = (fun y ↦ C i (c y)) - (fun _ ↦ C i (c x)) := by
      funext y
      exact map_sub (C i) (c y) (c x)
    have hd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ C i (c y)) x :=
      (C i).differentiableAt.mdifferentiableAt.comp x hcD
    ext a
    rw [he, mvfderiv_sub hd mdifferentiableAt_const, mvfderiv_const, sub_zero]
    change mvfderiv (𝓡 n) ((C i) ∘ c) x a = _
    rw [mvfderiv_comp_apply x (C i).differentiableAt.mdifferentiableAt hcD a]
    simpa only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, L] using!
      congrArg (fun K : E →L[ℝ] ℝ ↦ K (L a)) ((C i).fderiv (x := c x))
  have hterm (i : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% (fun y ↦ φ i y • S i y)) U := (hφ i).smul_section (hS i)
  have hsumSmooth (s : Finset (Fin n)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (fun y ↦ ∑ i ∈ s, φ i y • S i y)) U :=
    ContMDiffOn.sum_section (fun i _ ↦ hterm i)
  have htermD (i : Fin n) :
      D.connection (fun y ↦ φ i y • S i y) x =
        (mvfderiv (𝓡 n) (φ i) x).smulRight (S i x) := by
    have hSi := ((hS i).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hφi := ((hφ i).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    change D.connection (φ i • S i) x = _
    rw [D.connection.isCovariantDerivativeOnUniv.leibniz hSi hφi, hφzero]
    simp only [zero_smul, zero_add]
  have hsumD (s : Finset (Fin n)) :
      D.connection (fun y ↦ ∑ i ∈ s, φ i y • S i y) x =
        ∑ i ∈ s, D.connection (fun y ↦ φ i y • S i y) x := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using! D.connection.isCovariantDerivativeOnUniv.zero (x := x)
    | @insert i s his ih =>
      have he : (fun y ↦ ∑ j ∈ insert i s, φ j y • S j y) =
          (fun y ↦ φ i y • S i y) + (fun y ↦ ∑ j ∈ s, φ j y • S j y) := by
        funext y
        simp only [Finset.sum_insert his, Pi.add_apply]
      have hiD := ((hterm i).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
      have hsD := ((hsumSmooth s).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
      rw [he, D.connection.isCovariantDerivativeOnUniv.add hiD hsD, ih,
        Finset.sum_insert his]
  let W := fun y ↦ ∑ i, φ i y • S i y
  have hW := hsumSmooth Finset.univ
  have hWx : W x = 0 := by simp only [W, hφzero, zero_smul, Finset.sum_const_zero]
  have hWD : D.connection W x = D.connection V x := by
    ext a
    have hs := congrArg (fun K : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x ↦ K a)
      (hsumD Finset.univ)
    change D.connection W x a = _ at hs
    rw [hs]
    simp only [sum_apply, htermD, ContinuousLinearMap.smulRight_apply, hφD,
      ContinuousLinearMap.comp_apply]
    have hcoord (i : Fin n) : C i (L a) =
        b.coord i (e.continuousLinearMapAt ℝ x (D.connection V x a)) := by
      change b.coord i (e.continuousLinearMapAt ℝ x
        (D.connection V x (L.inverse (L a)))) = _
      rw [show L.inverse (L a) = a from hL.inverse_apply_eq.mpr rfl]
    simp only [hcoord, S, FiberBundle.extend_apply_self]
    simp only [← map_smul]
    rw [← map_sum]
    change e.symmL ℝ x (∑ i, b.repr (e.continuousLinearMapAt ℝ x
      (D.connection V x a)) i • b i) = _
    rw [b.sum_repr, e.symmL_continuousLinearMapAt hxe]
  let X := V + (-1 : ℝ) • W
  have hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% X) U :=
    hV.add_section (hW.const_smul_section (a := (-1 : ℝ)))
  refine ⟨U, X, hU, hx, hX, ?_, ?_⟩
  · simp only [X, Pi.add_apply, Pi.smul_apply, hWx, smul_zero, add_zero, V,
      FiberBundle.extend_apply_self]
  · have hVD := (hV.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hW'D := ((hW.const_smul_section (a := (-1 : ℝ))).contMDiffAt
      (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hWD' := (hW.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    change D.connection (V + (-1 : ℝ) • W) x = 0
    rw [D.connection.isCovariantDerivativeOnUniv.add hVD hW'D,
      D.connection.isCovariantDerivativeOnUniv.smul_const (-1) hWD', hWD]
    simp

set_option maxHeartbeats 4000000 in

set_option backward.isDefEq.respectTransparency false in
theorem tensorLaplacian_nonneg_at_null (D : LeviCivitaData g)
    {S : CovariantTensorEvaluation n M 2} (hS : IsSmoothCovariantTensor S)
    (hsymm : ∀ (y : M) (a b : TangentSpace (𝓡 n) y), S y ![a, b] = S y ![b, a])
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hpos : ∀ (y : M), y ∈ U → ∀ a : TangentSpace (𝓡 n) y, 0 ≤ S y ![a, a])
    (u : TangentSpace (𝓡 n) x) (hnull : S x ![u, u] = 0) :
    0 ≤ D.tensorLaplacian S x ![u, u] := by
  classical
  obtain ⟨A, hA⟩ := hS.1 x
  have hu0 {y : M} (a b c : TangentSpace (𝓡 n) y) :
      Function.update ![a, b] 0 c = ![c, b] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hu1 {y : M} (a b c : TangentSpace (𝓡 n) y) :
      Function.update ![a, b] 1 c = ![a, c] := by
    funext i
    fin_cases i <;> simp [Function.update]
  let B : LinearMap.BilinForm ℝ (TangentSpace (𝓡 n) x) :=
    { toFun := fun a ↦ A.toLinearMap ![a, 0] 1
      map_add' := by
        intro a b
        ext c
        simpa only [LinearMap.add_apply, MultilinearMap.toLinearMap_apply, hu1, hu0] using
          A.map_update_add ![0, c] 0 a b
      map_smul' := by
        intro s a
        ext b
        simpa only [LinearMap.smul_apply, RingHom.id_apply,
          MultilinearMap.toLinearMap_apply, hu1, hu0] using
          A.map_update_smul ![0, b] 0 s a }
  have hB (a b : TangentSpace (𝓡 n) x) : B a b = S x ![a, b] := by
    change A (Function.update ![a, 0] 1 b) = _
    rw [hu1]
    exact (hA _).symm
  have hBsymm : B.IsSymm := ⟨fun a b ↦ by simpa only [hB] using hsymm x a b⟩
  have hBu : B u = 0 := LinearMap.mem_ker.mp
    ((B.apply_apply_same_eq_zero_iff (fun a ↦ by simpa only [hB] using hpos x hx a)
      (LinearMap.BilinForm.isSymm_iff.mp hBsymm)).mp (by simpa only [hB] using hnull))
  have hkerL (a : TangentSpace (𝓡 n) x) : S x ![u, a] = 0 := by
    rw [← hB, hBu]
    rfl
  have hkerR (a : TangentSpace (𝓡 n) x) : S x ![a, u] = 0 :=
    (hsymm x a u).trans (hkerL a)
  obtain ⟨V, X, hV, hxV, hX, hXu, hDX⟩ := exists_local_field_connection_zero D x u
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let O := (U ∩ V) ∩ e.baseSet
  have hO : IsOpen O := (hU.inter hV).inter e.open_baseSet
  have hxO : x ∈ O := ⟨⟨hx, hxV⟩, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let Smooth (Z : (y : M) → TangentSpace (𝓡 n) y) :=
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) O
  have hXO : Smooth X := hX.mono (fun _ hy ↦ hy.1.2)
  have hE (a : TangentSpace (𝓡 n) x) :
      Smooth (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a) :=
    (contMDiffOn_extend_baseSet a).mono inter_subset_right
  have hCons {k : ℕ} {Z : (y : M) → TangentSpace (𝓡 n) y}
      {W : Fin k → (y : M) → TangentSpace (𝓡 n) y}
      (hZ : Smooth Z) (hW : ∀ i, Smooth (W i)) :
      ∀ i, Smooth ((Fin.cons Z W : Fin (k + 1) →
        (y : M) → TangentSpace (𝓡 n) y) i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact hZ
    | succ i => exact hW i
  have hTwo {Z W : (y : M) → TangentSpace (𝓡 n) y}
      (hZ : Smooth Z) (hW : Smooth W) :
      ∀ i : Fin 2, Smooth ((![Z, W] : Fin 2 →
        (y : M) → TangentSpace (𝓡 n) y) i) := by
    intro i
    fin_cases i
    · exact hZ
    · exact hW
  have hPoint {k : ℕ} (Z : (y : M) → TangentSpace (𝓡 n) y)
      (W : Fin k → (y : M) → TangentSpace (𝓡 n) y) (y : M) :
      (fun i ↦ (Fin.cons Z W : Fin (k + 1) →
        (z : M) → TangentSpace (𝓡 n) z) i y) = Fin.cons (Z y) (fun i ↦ W i y) := by
    funext i
    cases i using Fin.cases <;> rfl
  have hPointTwo (Z W : (y : M) → TangentSpace (𝓡 n) y) (y : M) :
      (fun i ↦ (![Z, W] : Fin 2 → (z : M) → TangentSpace (𝓡 n) z) i y) =
        ![Z y, W y] := by
    funext i
    fin_cases i <;> rfl
  have hDiff {k : ℕ} {T : CovariantTensorEvaluation n M k}
      (hT : IsSmoothCovariantTensor T)
      {Z : (y : M) → TangentSpace (𝓡 n) y}
      {W : Fin k → (y : M) → TangentSpace (𝓡 n) y}
      (hZ : Smooth Z) (hW : ∀ i, Smooth (W i)) {y : M} (hy : y ∈ O) :
      mvfderiv (𝓡 n) (fun z ↦ T z (fun i ↦ W i z)) y (Z y) =
        D.covariantTensorDerivative T y (Fin.cons (Z y) (fun i ↦ W i y)) +
          ∑ i, T y (Function.update (fun j ↦ W j y) i
            (D.connection (W i) y (Z y))) := by
    have he := covariantTensorDerivativeOnFields_eq D hT hO (hCons hZ hW) hy
    rw [hPoint] at he
    simp only [covariantTensorDerivativeOnFields, Fin.cons_zero, Fin.cons_succ] at he
    exact sub_eq_iff_eq_add.mp he
  have hzero {k : ℕ} {T : CovariantTensorEvaluation n M k}
      (hT : IsSmoothCovariantTensor T) (v : Fin k → TangentSpace (𝓡 n) x)
      (i : Fin k) (hi : v i = 0) : T x v = 0 := by
    obtain ⟨Q, hQ⟩ := hT.1 x
    rw [hQ]
    exact Q.map_coord_zero i hi
  let K := D.covariantTensorDerivative S
  have hK : IsSmoothCovariantTensor K := isSmoothCovariantTensor_covariantTensorDerivative D hS
  have hzK1 (a b : TangentSpace (𝓡 n) x) : K x ![a, 0, b] = 0 :=
    hzero hK _ 1 rfl
  have hzK2 (a b : TangentSpace (𝓡 n) x) : K x ![a, b, 0] = 0 :=
    hzero hK _ 2 rfl
  have hzS0 (a : TangentSpace (𝓡 n) x) : S x ![0, a] = 0 := hzero hS _ 0 rfl
  have hzS1 (a : TangentSpace (𝓡 n) x) : S x ![a, 0] = 0 := hzero hS _ 1 rfl
  let f := fun y ↦ S y ![X y, X y]
  have hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f O := by
    simpa only [hPointTwo] using hS.2 O hO ![X, X] (hTwo hXO hXO)
  have hfx : f x = 0 := by simpa only [f, hXu] using hnull
  have hmin : IsLocalMin f x := by
    filter_upwards [hO.mem_nhds hxO] with y hy
    change f x ≤ f y
    rw [hfx]
    exact hpos y hy.1.1 (X y)
  have hdfx (a : TangentSpace (𝓡 n) x) :
      mvfderiv (𝓡 n) f x a = K x ![a, u, u] := by
    have he := hDiff hS (hE a) (hTwo hXO hXO) hxO
    simpa only [hPointTwo, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
      Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      show (Fin.succ 0 : Fin 2) = 1 from rfl, hu0, hu1,
      hDX, zero_apply, hXu, FiberBundle.extend_apply_self,
      hzS0, hzS1, add_zero, Matrix.Fin.cons_vecCons, K, f] using! he
  have hsecond (a : TangentSpace (𝓡 n) x) :
      0 ≤ D.iteratedCovariantTensorDerivative S 2 x ![a, a, u, u] := by
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
    have hY : Smooth Y := hE a
    let C := fun y ↦ D.connection X y (Y y)
    have hC : Smooth C := by
      intro y hy
      apply ContMDiffAt.contMDiffWithinAt
      apply contMDiffAt_section_of_metric_pairings g C
      intro b
      let q := trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) y
      have hyq : y ∈ O ∩ q.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
      exact (contMDiffOn_connection_pairing D (hO.inter q.open_baseSet)
        (hY.mono inter_subset_left) (hXO.mono inter_subset_left)
        ((contMDiffOn_extend_baseSet b).mono inter_subset_right)).contMDiffAt
          ((hO.inter q.open_baseSet).mem_nhds hyq)
    have hCx : C x = 0 := by simp only [C, hDX, zero_apply]
    let p := fun y ↦ K y ![Y y, X y, X y]
    let q := fun y ↦ S y ![C y, X y]
    let r := fun y ↦ S y ![X y, C y]
    have hp : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ p O := by
      apply (hK.2 O hO (Fin.cons Y ![X, X]) (hCons hY (hTwo hXO hXO))).congr
      intro y hy
      apply congrArg (K y)
      funext i
      fin_cases i <;> rfl
    have hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q O := by
      simpa only [hPointTwo] using hS.2 O hO ![C, X] (hTwo hC hXO)
    have hr : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ r O := by
      simpa only [hPointTwo] using hS.2 O hO ![X, C] (hTwo hXO hC)
    have hfirst : (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) =ᶠ[𝓝 x] (p + q + r) := by
      filter_upwards [hO.mem_nhds hxO] with y hy
      have he := hDiff hS hY (hTwo hXO hXO) hy
      simpa only [hPointTwo, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
        Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        show (Fin.succ 0 : Fin 2) = 1 from rfl, hu0, hu1, Matrix.Fin.cons_vecCons,
        add_zero, Pi.add_apply, add_assoc, K, C, f, p, q, r] using! he
    have hdp : mvfderiv (𝓡 n) p x (Y x) =
        D.covariantTensorDerivative K x ![Y x, Y x, u, u] +
          K x ![D.connection Y x (Y x), u, u] := by
      have he := hDiff hK hY (hCons hY (hTwo hXO hXO)) hxO
      simp only [hPoint, hPointTwo, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update] at he
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
        show (Fin.succ 0 : Fin 2) = 1 from rfl, hu0, hu1, Matrix.Fin.cons_vecCons,
        hDX, zero_apply, hXu, hzK1, hzK2, add_zero, zero_add, p] using! he
    have hdq : mvfderiv (𝓡 n) q x (Y x) = 0 := by
      have he := hDiff hS hY (hTwo hC hXO) hxO
      simpa only [hPointTwo, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
        Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        show (Fin.succ 0 : Fin 2) = 1 from rfl, hu0, hu1, Matrix.Fin.cons_vecCons,
        hCx, hXu, hDX, zero_apply, hzK1, hkerR, hzS0, add_zero, zero_add, q, K] using! he
    have hdr : mvfderiv (𝓡 n) r x (Y x) = 0 := by
      have he := hDiff hS hY (hTwo hXO hC) hxO
      simpa only [hPointTwo, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.cons_zero,
        Fin.cons_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        show (Fin.succ 0 : Fin 2) = 1 from rfl, hu0, hu1, Matrix.Fin.cons_vecCons,
        hCx, hXu, hDX, zero_apply, hzK2, hkerL, hzS1, add_zero, zero_add, r, K] using! he
    have hpD := (hp.contMDiffAt (hO.mem_nhds hxO)).mdifferentiableAt (by simp)
    have hqD := (hq.contMDiffAt (hO.mem_nhds hxO)).mdifferentiableAt (by simp)
    have hrD := (hr.contMDiffAt (hO.mem_nhds hxO)).mdifferentiableAt (by simp)
    have hdd : mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) x (Y x) =
        D.covariantTensorDerivative K x ![Y x, Y x, u, u] +
          K x ![D.connection Y x (Y x), u, u] := by
      have he : mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) x =
          mvfderiv (𝓡 n) (p + q + r) x := hfirst.mfderiv_eq
      rw [he, mvfderiv_add (hpD.add hqD) hrD, mvfderiv_add hpD hqD]
      simp only [add_apply, hdp, hdq, hdr, add_zero]
    have hh : D.hessian f x a a = D.iteratedCovariantTensorDerivative S 2 x ![a, a, u, u] := by
      change mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) x (Y x) -
        mvfderiv (𝓡 n) f x (D.connection Y x (Y x)) = _
      rw [hdd, hdfx, add_sub_cancel_right]
      simp only [Y, FiberBundle.extend_apply_self,
        LeviCivitaData.iteratedCovariantTensorDerivative, K]
    rw [← hh]
    exact D.hessian_nonneg_of_isLocalMin (hf.contMDiffAt (hO.mem_nhds hxO)) hmin a
  exact Finset.sum_nonneg fun i _ ↦ hsecond (g.orthonormalBasis x i)

end PoincareConjecture.M04


import PoincareConjecture.Proofs.M03.MetricDifferenceEvolution
import PoincareConjecture.Proofs.M03.CurvatureJoint
import PoincareConjecture.Proofs.M03.MetricInverse
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame












set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Set

universe u v

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem ricci_covariant_derivative_eq_sum_basis
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (A B C : (x : M) → TangentSpace (𝓡 n) x)
    (hA : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
    (hC : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U)
    {x : M} (hx : x ∈ U)
    {ι : Type v} [Fintype ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    let dR := fun
        (A B C E : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection (fun z => D.curvatureOnFields B C E z) y (A y) -
        D.curvatureOnFields
          (fun z => D.connection B z (A z)) C E y -
        D.curvatureOnFields B
          (fun z => D.connection C z (A z)) E y -
        D.curvatureOnFields B C
          (fun z => D.connection E z (A z)) y
    let dRic := fun
        (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      mvfderiv (𝓡 n) (fun z => D.ricci z (B z) (C z)) y (A y) -
        D.ricci y (D.connection B y (A y)) (C y) -
        D.ricci y (B y) (D.connection C y (A y))
    dRic A B C x =
      ∑ i, b.repr
        (dR A (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)) B C x) i := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let b0 := b.map (e.linearEquivAt (R := ℝ) x he)
  let V := U ∩ e.baseSet
  have hV : IsOpen V := hU.inter e.open_baseSet
  have hxV : x ∈ V := ⟨hx, he⟩
  let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let θ := e.localFrameCoeff (𝓡 n) b0
  let q := fun (i : ι) (W : (y : M) → TangentSpace (𝓡 n) y) y => θ i y (W y)
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection B y (A y)
  let L := VectorField.mlieBracket (𝓡 n) (M := M)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let K := fun (A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
    N A (R B C W) y - R (N A B) C W y -
      R B (N A C) W y - R B C (N A W) y
  let H := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    mvfderiv (𝓡 n) (fun z => D.ricci z (B z) (C z)) y (A y) -
      D.ricci y (N A B y) (C y) - D.ricci y (B y) (N A C y)
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) V
  have hAV : S A := hA.mono inter_subset_left
  have hBV : S B := hB.mono inter_subset_left
  have hCV : S C := hC.mono inter_subset_left
  have hmd (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W)
      {y : M} (hy : y ∈ V) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% W) y :=
    (hW.contMDiffAt (hV.mem_nhds hy)).mdifferentiableAt (by simp)
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : S (N A B) :=
    D.contMDiffOn_connection_apply hV A B hA hB
  have hL (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : S (L A B) := by
    intro y hy
    exact ((hA.contMDiffAt (hV.mem_nhds hy)).mlieBracket_vectorField
      (hB.contMDiffAt (hV.mem_nhds hy)) (m := ⊤) (n := ⊤) (by simp)).contMDiffWithinAt
  have hR (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (R A B C) :=
    ((hN A _ hA (hN B C hB hC)).sub_section
      (hN B _ hB (hN A C hA hC))).sub_section
        (hN _ C (hL A B hA hB) hC)
  have hEvalue (i : ι) {y : M} (hy : y ∈ e.baseSet) :
      E i y = e.basisAt b0 hy i := by
    simp only [E, FiberBundle.extend, Bundle.Trivialization.basisAt, b0,
      Module.Basis.map_apply, Bundle.Trivialization.linearEquivAt_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply]
    rfl
  have hE (i : ι) : S (E i) := by
    apply ((e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b0 i).mono
      (inter_subset_right : V ⊆ e.baseSet)).congr
    intro y hy
    change (⟨y, E i y⟩ : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n))) = ⟨y, e.localFrame b0 i y⟩
    rw [hEvalue i hy.2, e.localFrame_apply_of_mem_baseSet b0 hy.2]
  have hθrepr (W : (y : M) → TangentSpace (𝓡 n) y) (i : ι)
      {y : M} (hy : y ∈ e.baseSet) :
      θ i y (W y) = (e.basisAt b0 hy).repr (W y) i :=
    e.localFrameCoeff_apply_of_mem_baseSet b0 hy W i
  have hq (i : ι) (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q i W) V :=
    contMDiffOn_localFrameCoeff b0 hV inter_subset_right hW i
  have hqmd (i : ι) (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (q i W) x :=
    ((hq i W hW).contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
  have hrec (W : (y : M) → TangentSpace (𝓡 n) y)
      {y : M} (hy : y ∈ V) : W y = ∑ i, q i W y • E i y := by
    simpa only [q, hθrepr W _ hy.2, hEvalue _ hy.2] using
      ((e.basisAt b0 hy.2).sum_repr (W y)).symm
  have hθself (i j : ι) : θ i x (E j x) = if j = i then 1 else 0 := by
    rw [hθrepr (E j) i he, hEvalue j he]
    exact Module.Basis.repr_self_apply _ _ _
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hnsum (W : ι → (y : M) → TangentSpace (𝓡 n) y)
      (hW : ∀ i, MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% (W i)) x)
      (v : TangentSpace (𝓡 n) x) :
      D.connection (fun y => ∑ i, W i y) x v = ∑ i, D.connection (W i) x v := by
    have aux (s : Finset ι) :
        D.connection (fun y => ∑ i ∈ s, W i y) x v =
          ∑ i ∈ s, D.connection (W i) x v := by
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        change D.connection 0 x v = 0
        rw [hc.zero, zero_apply]
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        change D.connection (W i + fun y => ∑ j ∈ s, W j y) x v = _
        rw [hc.add (hW i) (MDifferentiableAt.sum_section fun j _ => hW j),
          add_apply, ih]
    exact aux Finset.univ
  have hdsum (f : ι → M → ℝ)
      (hf : ∀ i, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f i) x)
      (v : TangentSpace (𝓡 n) x) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => ∑ i, f i y) x ∧
      mvfderiv (𝓡 n) (fun y => ∑ i, f i y) x v =
        ∑ i, mvfderiv (𝓡 n) (f i) x v := by
    have aux (s : Finset ι) :
        MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, f i y) x ∧
        mvfderiv (𝓡 n) (fun y => ∑ i ∈ s, f i y) x v =
          ∑ i ∈ s, mvfderiv (𝓡 n) (f i) x v := by
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        exact ⟨mdifferentiableAt_const, by rw [mvfderiv_const, zero_apply]⟩
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact ⟨(hf i).add ih.1, by
          rw [mvfderiv_fun_add (hf i) ih.1, add_apply, ih.2]⟩
    exact aux Finset.univ
  have hNW (A W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      N A W x = ∑ j, (q j W x • N A (E j) x +
        mvfderiv (𝓡 n) (q j W) x (A x) • E j x) := by
    have hs (j : ι) : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% ((q j W) • E j)) x :=
      (hqmd j W hW).smul_section (hmd _ (hE j) hxV)
    have heq := hc.congr_of_eventuallyEq (hmd W hW hxV)
      (MDifferentiableAt.sum_section fun j _ => hs j) Filter.univ_mem
      (Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) fun y hy => hrec W hy)
    calc
      _ = D.connection (fun y => ∑ j, q j W y • E j y) x (A x) :=
        congrArg (fun T => T (A x)) heq
      _ = ∑ j, D.connection ((q j W) • E j) x (A x) :=
        hnsum (fun j => (q j W) • E j) hs (A x)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [N, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] using
          congrArg (fun T => T (A x))
            (hc.leibniz (hmd _ (hE j) hxV) (hqmd j W hW))
  have hcoeff (A W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) (i : ι) :
      θ i x (N A W x) = mvfderiv (𝓡 n) (q i W) x (A x) +
        ∑ j, q j W x * θ i x (N A (E j) x) := by
    rw [hNW A W hW]
    simp only [map_sum, map_add, map_smul, smul_eq_mul, hθself,
      Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq']
    rw [if_pos (Finset.mem_univ i)]
    exact add_comm _ _
  have htrace (B C : (y : M) → TangentSpace (𝓡 n) y) (hB : S B) (hC : S C)
      {y : M} (hy : y ∈ V) :
      D.ricci y (B y) (C y) = ∑ i, q i (R (E i) B C) y := by
    rw [ricci_eq_sum_basis_of_curvature_pairing D y (B y) (C y)
      (e.basisAt b0 hy.2)]
    apply Finset.sum_congr rfl
    intro i _
    change _ = θ i y (R (E i) B C y)
    rw [hθrepr _ i hy.2, ← hEvalue i hy.2]
    exact congrArg (fun v => (e.basisAt b0 hy.2).repr v i)
      (curvature_eq_curvatureOnFields D hV (E i) B C (hE i) hB hC hy)
  have hderiv (A B C : (y : M) → TangentSpace (𝓡 n) y) (hB : S B) (hC : S C) :
      mvfderiv (𝓡 n) (fun y => D.ricci y (B y) (C y)) x (A x) =
        ∑ i, mvfderiv (𝓡 n) (q i (R (E i) B C)) x (A x) := by
    have heq : (fun y => D.ricci y (B y) (C y)) =ᶠ[𝓝 x]
        (fun y => ∑ i, q i (R (E i) B C) y) :=
      Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) fun y hy => htrace B C hB hC hy
    calc
      _ = mvfderiv (𝓡 n) (fun y => ∑ i, q i (R (E i) B C) y) x (A x) := by
        dsimp only [mvfderiv]
        rw [heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)), heq.eq_of_nhds]
        rfl
      _ = _ := (hdsum _ (fun i => hqmd i _ (hR _ B C (hE i) hB hC)) (A x)).2
  obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
  have heval (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      R A B C x = T (A x) (B x) (C x) :=
    ((hT (A x) (B x) (C x)).trans
      (curvature_eq_curvatureOnFields D hV A B C hA hB hC hxV)).symm
  have hcorrection (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      (∑ i, θ i x (R (N A (E i)) B C x)) =
        ∑ i, ∑ j, q j (R (E i) B C) x * θ i x (N A (E j) x) := by
    have hrow (i : ι) : θ i x (R (N A (E i)) B C x) =
        ∑ j, θ j x (N A (E i) x) * q i (R (E j) B C) x := by
      conv_lhs => rw [heval _ B C (hN A _ hA (hE i)) hB hC,
        hrec (N A (E i)) hxV]
      simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply,
        LinearMap.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [q]
      rw [heval _ B C (hE j) hB hC]
    simp_rw [hrow]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have htotal (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      (∑ i, θ i x (N A (R (E i) B C) x)) =
        (∑ i, mvfderiv (𝓡 n) (q i (R (E i) B C)) x (A x)) +
          ∑ i, θ i x (R (N A (E i)) B C x) := by
    calc
      _ = ∑ i, (mvfderiv (𝓡 n) (q i (R (E i) B C)) x (A x) +
          ∑ j, q j (R (E i) B C) x * θ i x (N A (E j) x)) :=
        Finset.sum_congr rfl fun i _ => hcoeff A _ (hR _ B C (hE i) hB hC) i
      _ = _ := by rw [Finset.sum_add_distrib, hcorrection A B C hA hB hC]
  have htraceK (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      H A B C x = ∑ i, θ i x (K A (E i) B C x) := by
    dsimp only [H]
    rw [hderiv A B C hB hC, htrace (N A B) C (hN A B hA hB) hC hxV,
      htrace B (N A C) hB (hN A C hA hC) hxV]
    simp only [K, map_sub, Finset.sum_sub_distrib]
    rw [htotal A B C hA hB hC]
    dsimp only [q]
    ring
  have hbx : e.basisAt b0 he = b := by
    ext i
    simp only [Bundle.Trivialization.basisAt, b0, Module.Basis.map_apply,
      LinearEquiv.symm_apply_apply]
  have hθx (v : TangentSpace (𝓡 n) x) (i : ι) :
      θ i x v = b.repr v i := by
    simpa only [FiberBundle.extend_apply_self, hbx] using
      hθrepr (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) i he
  simpa only [hθx, E, K, H, N, R] using htraceK A B C hAV hBV hCV


theorem lower_covariant_derivative_iterated_inner
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) (k : ℕ)
    (P : (y : M) → TangentSpace (𝓡 n) y)
    (X : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y)
    (_hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hX : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X j)) U)
    {x : M} (hx : x ∈ U) :
    let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.connection B y (A y)
    let K := curvatureOnFields_iteratedCovariantDerivative D
    let L := fun (Z : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y
        (K k (fun j : Fin (k + 3) => Z (Fin.castSucc j)) y)
        (Z (Fin.last (k + 3)) y)
    mvfderiv (𝓡 n) (L X) x (P x) -
        ∑ j : Fin (k + 4), L (Function.update X j (N P (X j))) x =
      g.inner x
        (K (k + 1) (Fin.cons P
          (fun j : Fin (k + 3) => X (Fin.castSucc j))) x)
        (X (Fin.last (k + 3)) x) := by
  classical
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y => D.connection B y (A y)
  let K := curvatureOnFields_iteratedCovariantDerivative D
  let Y := fun j : Fin (k + 3) => X j.castSucc
  let z := X (Fin.last (k + 3))
  let L := fun (Z : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (K k (Fin.init Z) y) (Z (Fin.last (k + 3)) y)
  let S := fun Q : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U
  have hmd (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Q) x :=
    (hQ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hKY : S (K k Y) := contMDiffOn_curvatureOnFields_iteratedCovariantDerivative
    D hU k Y (fun j => hX j.castSucc)
  have hd := D.mvfderiv_inner P (K k Y) z (hmd _ hKY) (hmd _ (hX (Fin.last (k + 3))))
  have hcast (j : Fin (k + 3)) :
      L (Function.update X j.castSucc (N P (X j.castSucc))) x =
        g.inner x (K k (Function.update Y j (N P (Y j))) x) (z x) := by
    dsimp only [L]
    rw [Fin.init_update_castSucc, Function.update_of_ne (Fin.castSucc_ne_last j).symm]
    rfl
  have hlast : L (Function.update X (Fin.last (k + 3)) (N P z)) x =
      g.inner x (K k Y x) (N P z x) := by
    dsimp only [L]
    rw [Fin.init_update_last, Function.update_self]
    rfl
  have hstep : K (k + 1) (Fin.cons P Y) x =
      N P (K k Y) x - ∑ j, K k (Function.update Y j (N P (Y j))) x := by
    rfl
  change mvfderiv (𝓡 n) (L X) x (P x) -
    (∑ j : Fin (k + 4), L (Function.update X j (N P (X j))) x) =
    g.inner x (K (k + 1) (Fin.cons P Y) x) (z x)
  rw [Fin.sum_univ_castSucc, hlast]
  simp only [hcast]
  change mvfderiv (𝓡 n) (fun y => g.inner y (K k Y y) (z y)) x (P x) - _ = _
  rw [hd, hstep]
  simp only [map_sub, sub_apply, map_sum, sum_apply]
  change g.inner x (N P (K k Y) x) (z x) + g.inner x (K k Y x) (N P z x) -
    ((∑ j, g.inner x (K k (Function.update Y j (N P (Y j))) x) (z x)) +
      g.inner x (K k Y x) (N P z x)) =
    g.inner x (N P (K k Y) x) (z x) -
      ∑ j, g.inner x (K k (Function.update Y j (N P (Y j))) x) (z x)
  ring

open Bundle Manifold

theorem two_contraction_slot_swap {n : ℕ} (r : Fin 4)
    (f : (Fin 4 → Fin n) → Fin n → ℝ) :
    (∑ γ, ∑ m, f γ m) =
      ∑ γ, ∑ m, f (Function.update γ r m) (γ r) := by
  classical
  let swap := fun z : (Fin 4 → Fin n) × Fin n =>
    (Function.update z.1 r z.2, z.1 r)
  have hs : Function.Involutive swap := by
    intro z
    apply Prod.ext
    · funext j
      by_cases hj : j = r
      · subst j
        simp [swap]
      · simp [swap, Function.update_of_ne hj]
    · simp [swap]
  let e : ((Fin 4 → Fin n) × Fin n) ≃ ((Fin 4 → Fin n) × Fin n) :=
    { toFun := swap, invFun := swap, left_inv := hs, right_inv := hs }
  have hh := (e.sum_comp (fun z => f z.1 z.2)).symm
  change (∑ z : (Fin 4 → Fin n) × Fin n, f z.1 z.2) =
    ∑ z : (Fin 4 → Fin n) × Fin n, f (Function.update z.1 r z.2) (z.1 r) at hh
  simpa only [Fintype.sum_prod_type] using hh

theorem two_contraction_metric_cancellation {n : ℕ}
    (a G : Fin n → Fin n → ℝ) (f : (Fin 4 → Fin n) → ℝ) :
    (∑ γ : Fin 4 → Fin n,
      ((-(∑ m, (G m (γ 0) * a m (γ 1) + G m (γ 1) * a (γ 0) m))) *
          a (γ 2) (γ 3) + a (γ 0) (γ 1) *
          (-(∑ m, (G m (γ 2) * a m (γ 3) + G m (γ 3) * a (γ 2) m)))) * f γ) +
      (∑ γ : Fin 4 → Fin n, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (∑ r : Fin 4, ∑ m, G (γ r) m * f (Function.update γ r m))) = 0 := by
  classical
  let w := fun γ : Fin 4 → Fin n => a (γ 0) (γ 1) * a (γ 2) (γ 3)
  have hslot (r : Fin 4) :
      (∑ γ, w γ * (∑ m, G (γ r) m * f (Function.update γ r m))) =
        ∑ γ, ∑ m, w (Function.update γ r m) * G m (γ r) * f γ := by
    simp only [Finset.mul_sum]
    rw [two_contraction_slot_swap r]
    apply Finset.sum_congr rfl
    intro γ _
    apply Finset.sum_congr rfl
    intro m _
    simp [mul_assoc]
  have hslots :
      (∑ γ, w γ * (∑ r : Fin 4, ∑ m, G (γ r) m * f (Function.update γ r m))) =
        ∑ γ, ∑ m,
          (((G m (γ 0) * a m (γ 1) + G m (γ 1) * a (γ 0) m) *
              a (γ 2) (γ 3) + a (γ 0) (γ 1) *
              (G m (γ 2) * a m (γ 3) + G m (γ 3) * a (γ 2) m)) * f γ) := by
    simp only [Fin.sum_univ_four, mul_add, Finset.sum_add_distrib]
    rw [hslot 0, hslot 1, hslot 2, hslot 3]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro γ _
    apply Finset.sum_congr rfl
    intro m _
    simp only [w]
    norm_num [Function.update_apply, Fin.ext_iff]
    ring
  change _ + (∑ γ, w γ * (∑ r : Fin 4, ∑ m, G (γ r) m * f (Function.update γ r m))) = 0
  rw [hslots, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro γ _
  simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_add, add_mul,
    mul_neg, neg_mul, mul_assoc]
  ring

set_option maxHeartbeats 5000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem curvature_two_factor_contraction_derivative
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (p q : ℕ)
    {σ : Type v} [Fintype σ]
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (σ ⊕ Fin 4)) (x0 : M) :
    letI : DecidableEq σ := Classical.decEq σ
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y => D.connection B y (A y)
    let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (curvatureOnFields_iteratedCovariantDerivative D r (Fin.init Z) y)
        (Z (Fin.last (r + 3)) y)
    let fill := fun (X : σ → (y : M) → TangentSpace (𝓡 n) y)
      (γ : Fin 4 → Fin n) s => Sum.elim X (fun j => E (γ j)) (slots s)
    let Q := fun (X : σ → (y : M) → TangentSpace (𝓡 n) y) y =>
      ∑ γ : Fin 4 → Fin n, (a y (γ 0) (γ 1) * a y (γ 2) (γ 3)) *
        (low p (fun j => fill X γ (Sum.inl j)) y *
          low q (fun j => fill X γ (Sum.inr j)) y)
    ∀ (P : (y : M) → TangentSpace (𝓡 n) y)
      (X : σ → (y : M) → TangentSpace (𝓡 n) y),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) e.baseSet →
      (∀ s, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X s)) e.baseSet) →
      ∀ {x : M}, x ∈ e.baseSet →
      mvfderiv (𝓡 n) (Q X) x (P x) -
          ∑ s : σ, Q (Function.update X s (N P (X s))) x =
        ∑ γ : Fin 4 → Fin n, (a x (γ 0) (γ 1) * a x (γ 2) (γ 3)) *
          (low (p + 1) (Fin.cons P (fun j => fill X γ (Sum.inl j))) x *
              low q (fun j => fill X γ (Sum.inr j)) x +
            low p (fun j => fill X γ (Sum.inl j)) x *
              low (q + 1) (Fin.cons P (fun j => fill X γ (Sum.inr j))) x) := by
  classical
  dsimp only
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ :=
    { contMDiff_mul := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact contDiff_mul.contMDiff }
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let theta := e.localFrameCoeff (𝓡 n) b
  let G := fun y : M => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y => D.connection B y (A y)
  let K := curvatureOnFields_iteratedCovariantDerivative D
  let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (K r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) e.baseSet
  let C := fun f : M → ℝ => ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet
  let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
    mvfderiv (𝓡 n) f y (P y)
  let Gamma := fun y i j m => theta m y (N (E i) (E j) y)
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) (hB : S B) :
      S (N A B) := D.contMDiffOn_connection_apply e.open_baseSet A B hA hB
  have hK (r : ℕ) (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) : S (K r Z) :=
    contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D e.open_baseSet r Z hZ
  have hlow (r : ℕ) (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) : C (low r Z) :=
    (hK r (Fin.init Z) (fun j => hZ j.castSucc)).inner_bundle (hZ (Fin.last (r + 3)))
  have hcmd (f : M → ℝ) (hf : C f) {y : M} (hy : y ∈ e.baseSet) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f y :=
    (hf.contMDiffAt (e.open_baseSet.mem_nhds hy)).mdifferentiableAt (by simp)
  have ha (i j : Fin n) : C (fun y => a y i j) := by
    have hf : RiemannianMetric.IsSmoothFamilyOn (fun _ : ℝ => g) univ :=
      (g.contMDiff.comp contMDiff_snd).contMDiffOn
    have hi := (contMDiffOn_family_metric_frame_inverse hf x0).2.2
    have hs := hi.comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨mem_univ (0 : ℝ), hy⟩)
    exact (contMDiffOn_const (c := EuclideanSpace.proj i)).clm_apply
      (hs.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j)))
  have hchart (f : M → ℝ) (hf : C f) {z : V} (hz : z ∈ c.target) (i : Fin n) :
      d (E i) f (c.symm z) =
        fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) := by
    let x := c.symm z
    have hx : x ∈ e.baseSet := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
    have hcs : MDifferentiableAt 𝓘(ℝ, V) (𝓡 n) c.symm z :=
      ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).contMDiffAt
        (c.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
    have he : e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm z := by
      have hh := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x0)
        (c.map_target hz)
      simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
        mfderivWithin_univ] at hh
      change e.symmL ℝ x = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (c x) at hh
      rwa [c.right_inv hz] at hh
    have hframe : E i x = e.symmL ℝ x (EuclideanSpace.single i 1) := by
      calc
        E i x = e.basisAt b hx i := e.localFrame_apply_of_mem_baseSet b hx
        _ = e.symm x (EuclideanSpace.single i 1) := by
          simp only [Trivialization.basisAt, Module.Basis.map_apply, b,
            OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
            Trivialization.linearEquivAt_symm_apply]
        _ = e.symmL ℝ x (EuclideanSpace.single i 1) := (e.symmL_apply hx _).symm
    have hfd : fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) =
        mvfderiv (𝓡 n) f x (e.symmL ℝ x (EuclideanSpace.single i 1)) := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, V) (f ∘ c.symm) z (EuclideanSpace.single i 1) = _
      erw [mvfderiv_comp_apply z (hcmd f hf hx) hcs (EuclideanSpace.single i 1), ← he]
      rfl
    exact (congrArg (mvfderiv (𝓡 n) f x) hframe).trans hfd.symm
  have hda {x : M} (hx : x ∈ e.baseSet) (i j k : Fin n) :
      d (E i) (fun y => a y j k) x =
        -(∑ m, (Gamma x i m j * a x m k + Gamma x i m k * a x j m)) := by
    have hxc : x ∈ c.source := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using hx
    have hh := metric_inverse_covariant_derivative_coordinates D x0 (c x) (c.map_source hxc) i j k
    have he := hchart (fun y => a y j k) (ha j k) (c.map_source hxc) i
    rw [c.left_inv hxc] at hh he
    exact he.trans hh
  have hrec (W : (y : M) → TangentSpace (𝓡 n) y) {y : M} (hy : y ∈ e.baseSet) :
      W y = ∑ i, theta i y (W y) • E i y :=
    e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) hy
  let GP := fun (P : (y : M) → TangentSpace (𝓡 n) y) y i m => theta m y (N P (E i) y)
  have hGP {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (i m : Fin n) :
      GP P x i m = ∑ k, theta k x (P x) * Gamma x k i m := by
    have hh := congrArg (fun v => theta m x (D.connection (E i) x v)) (hrec P hx)
    simpa only [GP, N, Gamma, map_sum, map_smul, smul_eq_mul] using hh
  have hdir {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) :
      d P f x = ∑ k, theta k x (P x) * d (E k) f x := by
    have hh := congrArg (mvfderiv (𝓡 n) f x) (hrec P hx)
    simpa only [d, map_sum, map_smul, smul_eq_mul] using hh
  have hdaP {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (i j : Fin n) :
      d P (fun y => a y i j) x =
        -(∑ m, (GP P x m i * a x m j + GP P x m j * a x i m)) := by
    rw [hdir hx P]
    simp_rw [hda hx, hGP hx P]
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul,
      mul_add, Finset.sum_add_distrib]
    congr 1
    congr 1
    all_goals
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro k _
      ring
  have hslot (r : ℕ) {x : M} (hx : x ∈ e.baseSet)
      (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) (hZ : ∀ j, S (Z j))
      (j : Fin (r + 3)) (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      K r (Function.update Z j W) x =
        ∑ m, theta m x (W x) • K r (Function.update Z j (E m)) x := by
    obtain ⟨T, hT⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D r x
    have hev (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) :
        T (Function.update (fun l => Z l x) j (A x)) = K r (Function.update Z j A) x := by
      have he : (fun l => Function.update Z j A l x) =
          Function.update (fun l => Z l x) j (A x) := by
        funext l
        by_cases hl : l = j
        · subst l
          simp only [Function.update_self]
        · simp only [Function.update_of_ne hl]
      rw [← he]
      apply hT e.open_baseSet _ _ hx
      intro l
      by_cases hl : l = j
      · subst l
        simpa only [Function.update_self] using hA
      · simpa only [Function.update_of_ne hl] using hZ l
    calc
      _ = T (Function.update (fun l => Z l x) j (W x)) := (hev W hW).symm
      _ = T (Function.update (fun l => Z l x) j (∑ m, theta m x (W x) • E m x)) :=
        congrArg (fun z => T (Function.update (fun l => Z l x) j z)) (hrec W hx)
      _ = ∑ m, theta m x (W x) • T (Function.update (fun l => Z l x) j (E m x)) := by
        rw [T.map_update_sum]
        simp only [T.map_update_smul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m _
        rw [hev (E m) (hE m)]
  have hlowSlot (r : ℕ) {x : M} (hx : x ∈ e.baseSet)
      (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) (hZ : ∀ j, S (Z j))
      (j : Fin (r + 4)) (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      low r (Function.update Z j W) x =
        ∑ m, theta m x (W x) * low r (Function.update Z j (E m)) x := by
    refine Fin.lastCases ?_ (fun l => ?_) j
    · simp only [low, Fin.init_update_last, Function.update_self]
      have hh := congrArg (g.inner x (K r (Fin.init Z) x)) (hrec W hx)
      simpa only [map_sum, map_smul, smul_eq_mul] using hh
    · simp only [low, Fin.init_update_castSucc,
        Function.update_of_ne (Fin.castSucc_ne_last l).symm]
      rw [hslot r hx (Fin.init Z) (fun s => hZ s.castSucc) l W hW]
      simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  have hlowDeriv (r : ℕ) {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (hP : S P)
      (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) (hZ : ∀ j, S (Z j)) :
      d P (low r Z) x = low (r + 1) (Fin.cons P Z) x +
        ∑ j, low r (Function.update Z j (N P (Z j))) x := by
    have hh := lower_covariant_derivative_iterated_inner D e.open_baseSet r P Z hP hZ hx
    have hinit : Fin.init (Fin.cons (α := fun _ : Fin (r + 5) =>
        (y : M) → TangentSpace (𝓡 n) y) P Z) =
        Fin.cons (α := fun _ : Fin (r + 4) => (y : M) → TangentSpace (𝓡 n) y)
          P (Fin.init Z) := by
      funext j
      refine Fin.cases ?_ (fun l => ?_) j
      · rfl
      · simp only [Fin.init, Fin.castSucc_succ, Fin.cons_succ]
    have hnext : low (r + 1) (Fin.cons P Z) x =
        g.inner x (K (r + 1) (Fin.cons P (Fin.init Z)) x) (Z (Fin.last (r + 3)) x) := by
      simp only [low, hinit, Fin.cons_last]
    change d P (low r Z) x - (∑ j, low r (Function.update Z j (N P (Z j))) x) =
      g.inner x (K (r + 1) (Fin.cons P (Fin.init Z)) x) (Z (Fin.last (r + 3)) x) at hh
    rw [← hnext] at hh
    exact sub_eq_iff_eq_add.mp hh
  have hdsum {ι : Type} [Fintype ι] {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (f : ι → M → ℝ) (hf : ∀ i, C (f i)) :
      d P (fun y => ∑ i, f i y) x = ∑ i, d P (f i) x := by
    have aux (s : Finset ι) :
        d P (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, d P (f i) x := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty, d, mvfderiv_const, zero_apply]
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        dsimp only [d] at ih ⊢
        rw [mvfderiv_fun_add (hcmd _ (hf i) hx)
          (hcmd _ (contMDiffOn_finsetSum fun j _ => hf j) hx), add_apply, ih]
    exact aux Finset.univ
  have hdmul {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (f h : M → ℝ) (hf : C f) (hh : C h) :
      d P (fun y => f y * h y) x = d P f x * h x + f x * d P h x := by
    have hd := congrArg (fun L => L (P x)) (mvfderiv_fun_mul (hcmd f hf hx) (hcmd h hh hx))
    simpa only [d, add_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
      smul_eq_mul, mul_comm, add_comm] using hd
  let T := fun (Z : (σ ⊕ Fin 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    low p (fun j => Z (slots (Sum.inl j))) y * low q (fun j => Z (slots (Sum.inr j))) y
  have hT (Z : (σ ⊕ Fin 4) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) : C (T Z) :=
    (hlow p _ (fun j => hZ _)).mul (hlow q _ (fun j => hZ _))
  have hleftUpdate (Z : (σ ⊕ Fin 4) → (y : M) → TangentSpace (𝓡 n) y)
      (j : Fin (p + 4)) (W : (y : M) → TangentSpace (𝓡 n) y) :
      T (Function.update Z (slots (Sum.inl j)) W) =
        fun y => low p (Function.update (fun l => Z (slots (Sum.inl l))) j W) y *
          low q (fun l => Z (slots (Sum.inr l))) y := by
    have hl : (fun l => Function.update Z (slots (Sum.inl j)) W (slots (Sum.inl l))) =
        Function.update (fun l => Z (slots (Sum.inl l))) j W := by
      funext l
      simp [Function.update_apply, slots.injective.eq_iff]
    have hr : (fun l => Function.update Z (slots (Sum.inl j)) W (slots (Sum.inr l))) =
        (fun l => Z (slots (Sum.inr l))) := by
      funext l
      simp [slots.injective.eq_iff]
    simp only [T, hl, hr]
  have hrightUpdate (Z : (σ ⊕ Fin 4) → (y : M) → TangentSpace (𝓡 n) y)
      (j : Fin (q + 4)) (W : (y : M) → TangentSpace (𝓡 n) y) :
      T (Function.update Z (slots (Sum.inr j)) W) =
        fun y => low p (fun l => Z (slots (Sum.inl l))) y *
          low q (Function.update (fun l => Z (slots (Sum.inr l))) j W) y := by
    have hl : (fun l => Function.update Z (slots (Sum.inr j)) W (slots (Sum.inl l))) =
        (fun l => Z (slots (Sum.inl l))) := by
      funext l
      simp [slots.injective.eq_iff]
    have hr : (fun l => Function.update Z (slots (Sum.inr j)) W (slots (Sum.inr l))) =
        Function.update (fun l => Z (slots (Sum.inr l))) j W := by
      funext l
      simp [Function.update_apply, slots.injective.eq_iff]
    simp only [T, hl, hr]
  have hTslot {x : M} (hx : x ∈ e.baseSet)
      (Z : (σ ⊕ Fin 4) → (y : M) → TangentSpace (𝓡 n) y) (hZ : ∀ j, S (Z j))
      (s : σ ⊕ Fin 4) (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      T (Function.update Z s W) x =
        ∑ m, theta m x (W x) * T (Function.update Z s (E m)) x := by
    obtain ⟨j, rfl⟩ := slots.surjective s
    cases j with
    | inl j =>
      simp only [hleftUpdate]
      rw [hlowSlot p hx _ (fun l => hZ _) j W hW]
      simp only [Finset.sum_mul, mul_assoc]
    | inr j =>
      simp only [hrightUpdate]
      rw [hlowSlot q hx _ (fun l => hZ _) j W hW]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
  intro P X hP hX x hx
  let Z := fun (X : σ → (y : M) → TangentSpace (𝓡 n) y) (γ : Fin 4 → Fin n) =>
    Sum.elim X (fun j => E (γ j))
  let w := fun (γ : Fin 4 → Fin n) y => a y (γ 0) (γ 1) * a y (γ 2) (γ 3)
  let Q := fun (X : σ → (y : M) → TangentSpace (𝓡 n) y) y =>
    ∑ γ : Fin 4 → Fin n, w γ y * T (Z X γ) y
  let next := fun (γ : Fin 4 → Fin n) =>
    low (p + 1) (Fin.cons P (fun j => Z X γ (slots (Sum.inl j)))) x *
        low q (fun j => Z X γ (slots (Sum.inr j))) x +
      low p (fun j => Z X γ (slots (Sum.inl j))) x *
        low (q + 1) (Fin.cons P (fun j => Z X γ (slots (Sum.inr j)))) x
  have hZ (γ : Fin 4 → Fin n) : ∀ s, S (Z X γ s) := by
    intro s
    cases s with
    | inl s => exact hX s
    | inr j => exact hE (γ j)
  have hZfree (γ : Fin 4 → Fin n) (s : σ)
      (W : (y : M) → TangentSpace (𝓡 n) y) :
      Function.update (Z X γ) (Sum.inl s) W = Z (Function.update X s W) γ := by
    funext j
    cases j with
    | inl j => simp [Z, Function.update_apply]
    | inr j => simp [Z]
  have hZend (γ : Fin 4 → Fin n) (r : Fin 4) (m : Fin n) :
      Function.update (Z X γ) (Sum.inr r) (E m) = Z X (Function.update γ r m) := by
    funext j
    cases j with
    | inl j => simp [Z]
    | inr j =>
      by_cases hj : j = r
      · subst j
        simp [Z]
      · simp [Z, hj]
  have hfactor (γ : Fin 4 → Fin n) :
      d P (T (Z X γ)) x = next γ +
        ∑ s : σ ⊕ Fin 4, T (Function.update (Z X γ) s (N P (Z X γ s))) x := by
    have hsum : (∑ s : σ ⊕ Fin 4,
        T (Function.update (Z X γ) s (N P (Z X γ s))) x) =
        (∑ j : Fin (p + 4),
          low p (Function.update (fun l => Z X γ (slots (Sum.inl l))) j
            (N P (Z X γ (slots (Sum.inl j))))) x *
              low q (fun l => Z X γ (slots (Sum.inr l))) x) +
        ∑ j : Fin (q + 4), low p (fun l => Z X γ (slots (Sum.inl l))) x *
          low q (Function.update (fun l => Z X γ (slots (Sum.inr l))) j
            (N P (Z X γ (slots (Sum.inr j))))) x := by
      rw [← slots.sum_comp (fun s => T (Function.update (Z X γ) s (N P (Z X γ s))) x),
        Fintype.sum_sum_type]
      simp only [hleftUpdate, hrightUpdate]
    change d P (fun y => low p (fun j => Z X γ (slots (Sum.inl j))) y *
      low q (fun j => Z X γ (slots (Sum.inr j))) y) x = _
    rw [hdmul hx P _ _ (hlow p _ (fun j => hZ γ _)) (hlow q _ (fun j => hZ γ _)),
      hlowDeriv p hx P hP _ (fun j => hZ γ _),
      hlowDeriv q hx P hP _ (fun j => hZ γ _), hsum]
    dsimp only [next]
    simp only [add_mul, mul_add, Finset.mul_sum, Finset.sum_mul]
    ring
  have hend (γ : Fin 4 → Fin n) (r : Fin 4) :
      T (Function.update (Z X γ) (Sum.inr r) (N P (Z X γ (Sum.inr r)))) x =
        ∑ m, GP P x (γ r) m * T (Z X (Function.update γ r m)) x := by
    change T (Function.update (Z X γ) (Sum.inr r) (N P (E (γ r)))) x = _
    rw [hTslot hx (Z X γ) (hZ γ) (Sum.inr r) (N P (E (γ r))) (hN _ _ hP (hE _))]
    simp only [hZend, GP]
  have hfree (γ : Fin 4 → Fin n) (s : σ) :
      T (Function.update (Z X γ) (Sum.inl s) (N P (Z X γ (Sum.inl s)))) x =
        T (Z (Function.update X s (N P (X s))) γ) x := by
    change T (Function.update (Z X γ) (Sum.inl s) (N P (X s))) x = _
    rw [hZfree]
  have hfactor' (γ : Fin 4 → Fin n) :
      d P (T (Z X γ)) x = next γ +
        (∑ s : σ, T (Z (Function.update X s (N P (X s))) γ) x) +
        ∑ r : Fin 4, ∑ m, GP P x (γ r) m * T (Z X (Function.update γ r m)) x := by
    rw [hfactor, Fintype.sum_sum_type]
    simp only [hfree, hend]
    ring
  have hw (γ : Fin 4 → Fin n) : C (w γ) := (ha _ _).mul (ha _ _)
  have hdw (γ : Fin 4 → Fin n) : d P (w γ) x =
      (-(∑ m, (GP P x m (γ 0) * a x m (γ 1) + GP P x m (γ 1) * a x (γ 0) m))) *
        a x (γ 2) (γ 3) + a x (γ 0) (γ 1) *
        (-(∑ m, (GP P x m (γ 2) * a x m (γ 3) + GP P x m (γ 3) * a x (γ 2) m))) := by
    rw [hdmul hx P _ _ (ha _ _) (ha _ _), hdaP hx P, hdaP hx P]
  have hcancel : (∑ γ, d P (w γ) x * T (Z X γ) x) +
      (∑ γ, w γ x *
        (∑ r : Fin 4, ∑ m, GP P x (γ r) m * T (Z X (Function.update γ r m)) x)) = 0 := by
    simp only [hdw, w]
    exact two_contraction_metric_cancellation (a x) (GP P x) (fun γ => T (Z X γ) x)
  have hdQ : d P (Q X) x =
      (∑ γ, d P (w γ) x * T (Z X γ) x) +
        ∑ γ, w γ x * d P (T (Z X γ)) x := by
    change d P (fun y => ∑ γ : Fin 4 → Fin n, w γ y * T (Z X γ) y) x = _
    rw [hdsum (ι := Fin 4 → Fin n) hx P (fun γ y => w γ y * T (Z X γ) y)
      (fun γ => (hw γ).mul (hT _ (hZ γ)))]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro γ _
    exact hdmul hx P _ _ (hw γ) (hT _ (hZ γ))
  have hfreeSum : (∑ γ, w γ x *
      (∑ s : σ, T (Z (Function.update X s (N P (X s))) γ) x)) =
      ∑ s : σ, Q (Function.update X s (N P (X s))) x := by
    simp only [Q, Finset.mul_sum]
    exact Finset.sum_comm
  have htotal : d P (Q X) x = (∑ γ, w γ x * next γ) +
      ∑ s : σ, Q (Function.update X s (N P (X s))) x := by
    rw [hdQ]
    simp only [hfactor', mul_add, Finset.sum_add_distrib]
    rw [hfreeSum]
    linarith [hcancel]
  change d P (Q X) x - (∑ s : σ, Q (Function.update X s (N P (X s))) x) =
    ∑ γ, w γ x * next γ
  rw [htotal]
  ring

end PoincareConjecture.Proofs.M03

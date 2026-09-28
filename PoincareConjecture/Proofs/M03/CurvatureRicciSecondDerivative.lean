import PoincareConjecture.Proofs.M03.CurvatureRicciDerivative
import PoincareConjecture.Proofs.M03.CurvatureDerivativeTensoriality
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Set

universe u v

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem ricci_second_covariant_derivative_eq_sum_basis
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (P Q B C : (x : M) → TangentSpace (𝓡 n) x)
    (hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hQ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U)
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
    let ddR := fun
        (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection (fun z => dR Q A B C z) y (P y) -
        dR (fun z => D.connection Q z (P z)) A B C y -
        dR Q (fun z => D.connection A z (P z)) B C y -
        dR Q A (fun z => D.connection B z (P z)) C y -
        dR Q A B (fun z => D.connection C z (P z)) y
    let ddRic := fun
        (P Q A B : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      mvfderiv (𝓡 n) (fun z => dRic Q A B z) y (P y) -
        dRic (fun z => D.connection Q z (P z)) A B y -
        dRic Q (fun z => D.connection A z (P z)) B y -
        dRic Q A (fun z => D.connection B z (P z)) y
    ddRic P Q B C x =
      ∑ i, b.repr
        (ddR P Q (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)) B C x) i := by
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
  let J := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (K Q A B C) y - K (N P Q) A B C y -
      K Q (N P A) B C y - K Q A (N P B) C y - K Q A B (N P C) y
  let I2 := fun (P Q A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    mvfderiv (𝓡 n) (H Q A B) y (P y) -
      H (N P Q) A B y - H Q (N P A) B y - H Q A (N P B) y
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) V
  have hPV : S P := hP.mono inter_subset_left
  have hQV : S Q := hQ.mono inter_subset_left
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
  have hK (A B C W : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hW : S W) : S (K A B C W) :=
    (((hN A _ hA (hR B C W hB hC hW)).sub_section
      (hR _ C W (hN A B hA hB) hC hW)).sub_section
      (hR B _ W hB (hN A C hA hC) hW)).sub_section
      (hR B C _ hB hC (hN A W hA hW))
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
  have hreplace (A E' B C : (z : M) → TangentSpace (𝓡 n) z)
      (hA : S A) (hE' : S E') (hB : S B) (hC : S C)
      {y : M} (hy : y ∈ V) :
      K A (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E' y)) B C y =
        K A E' B C y := by
    obtain ⟨T, hT⟩ := exists_curvatureOnFields_derivative_quadrilinearMap D y
    obtain ⟨s, hs, hExt⟩ := FiberBundle.exists_contMDiffOn_extend
      (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (E' y)
    obtain ⟨W, hW, hWo, hyW⟩ := mem_nhds_iff.mp
      (Filter.inter_mem (hV.mem_nhds hy) hs)
    have hWV : W ⊆ V := fun _ hz => (hW hz).1
    have hWs : W ⊆ s := fun _ hz => (hW hz).2
    have hext := hT hWo A
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E' y)) B C
      (hA.mono hWV) (hExt.mono hWs) (hB.mono hWV) (hC.mono hWV) hyW
    have hfixed := hT hV A E' B C hA hE' hB hC hy
    simp only [FiberBundle.extend_apply_self] at hext
    simpa only [K, N, R] using hext.symm.trans hfixed
  have htrace (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) {y : M} (hy : y ∈ V) :
      H A B C y = ∑ i, q i (K A (E i) B C) y := by
    have ht := ricci_covariant_derivative_eq_sum_basis
      D hV A B C hA hB hC hy (e.basisAt b0 hy.2)
    change H A B C y = ∑ i, (e.basisAt b0 hy.2).repr
      (K A (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
        (e.basisAt b0 hy.2 i)) B C y) i at ht
    rw [ht]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hEvalue i hy.2,
      hreplace A (E i) B C hA (hE i) hB hC hy]
    exact (hθrepr (K A (E i) B C) i hy.2).symm
  have hderiv (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      mvfderiv (𝓡 n) (H A B C) x (P x) =
        ∑ i, mvfderiv (𝓡 n) (q i (K A (E i) B C)) x (P x) := by
    have heq : H A B C =ᶠ[𝓝 x] (fun y => ∑ i, q i (K A (E i) B C) y) :=
      Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) fun y hy =>
        htrace A B C hA hB hC hy
    calc
      _ = mvfderiv (𝓡 n) (fun y => ∑ i, q i (K A (E i) B C) y) x (P x) := by
        dsimp only [mvfderiv]
        rw [heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)), heq.eq_of_nhds]
      _ = _ := (hdsum _
        (fun i => hqmd i _ (hK A _ B C hA (hE i) hB hC)) (P x)).2
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_derivative_quadrilinearMap D x
  have heval (A B C W : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hW : S W) :
      K A B C W x = T (A x) (B x) (C x) (W x) := by
    simpa only [K, N, R] using (hT hV A B C W hA hB hC hW hxV).symm
  have hcorrection (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) :
      (∑ i, θ i x (K A (N P (E i)) B C x)) =
        ∑ i, ∑ j, q j (K A (E i) B C) x * θ i x (N P (E j) x) := by
    have hrow (i : ι) : θ i x (K A (N P (E i)) B C x) =
        ∑ j, θ j x (N P (E i) x) * q i (K A (E j) B C) x := by
      conv_lhs => rw [heval A _ B C hA (hN P _ hP (hE i)) hB hC,
        hrec (N P (E i)) hxV]
      simp only [map_sum, map_smul, LinearMap.coe_sum, Finset.sum_apply,
        LinearMap.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [q]
      rw [heval A _ B C hA (hE j) hB hC]
    simp_rw [hrow]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have htotal (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) :
      (∑ i, θ i x (N P (K A (E i) B C) x)) =
        (∑ i, mvfderiv (𝓡 n) (q i (K A (E i) B C)) x (P x)) +
          ∑ i, θ i x (K A (N P (E i)) B C x) := by
    calc
      _ = ∑ i, (mvfderiv (𝓡 n) (q i (K A (E i) B C)) x (P x) +
          ∑ j, q j (K A (E i) B C) x * θ i x (N P (E j) x)) :=
        Finset.sum_congr rfl fun i _ => hcoeff P _ (hK A _ B C hA (hE i) hB hC) i
      _ = _ := by rw [Finset.sum_add_distrib, hcorrection P A B C hP hA hB hC]
  have htraceJ (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) :
      I2 P A B C x = ∑ i, θ i x (J P A (E i) B C x) := by
    dsimp only [I2]
    rw [hderiv P A B C hA hB hC,
      htrace (N P A) B C (hN P A hP hA) hB hC hxV,
      htrace A (N P B) C hA (hN P B hP hB) hC hxV,
      htrace A B (N P C) hA hB (hN P C hP hC) hxV]
    simp only [J, map_sub, Finset.sum_sub_distrib]
    rw [htotal P A B C hP hA hB hC]
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
  simpa only [hθx, E, J, I2, K, H, N, R] using htraceJ P Q B C hPV hQV hBV hCV

abbrev CurvatureResidualPattern (k : ℕ) :=
  Σ (p : ℕ) (q : ℕ),
    ℤ × ((Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4))

namespace CurvatureResidualPattern

theorem orders {k : ℕ} (r : CurvatureResidualPattern k) : r.1 + r.2.1 = k := by
  have h := Fintype.card_congr r.2.2.2
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

def optionSumLeft {α β : Type*} : (Option α ⊕ β) ≃ Option (α ⊕ β) where
  toFun
    | .inl none => none
    | .inl (some a) => some (.inl a)
    | .inr b => some (.inr b)
  invFun
    | none => .inl none
    | some (.inl a) => .inl (some a)
    | some (.inr b) => .inr b
  left_inv := by
    intro s
    rcases s with s | s
    · cases s <;> rfl
    · rfl
  right_inv := by
    intro s
    cases s with
    | none => rfl
    | some s => cases s <;> rfl

def optionSumRight {α β : Type*} : (α ⊕ Option β) ≃ Option (α ⊕ β) where
  toFun
    | .inl a => some (.inl a)
    | .inr none => none
    | .inr (some b) => some (.inr b)
  invFun
    | none => .inr none
    | some (.inl a) => .inl a
    | some (.inr b) => .inr (some b)
  left_inv := by
    intro s
    rcases s with s | s
    · rfl
    · cases s <;> rfl
  right_inv := by
    intro s
    cases s with
    | none => rfl
    | some s => cases s <;> rfl

def oldSlot {k : ℕ} : (Fin (k + 4) ⊕ Fin 4) → (Fin (k + 1 + 4) ⊕ Fin 4) :=
  Sum.map Fin.succ id

def slotsLeft {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4)) :
    (Fin (p + 1 + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 1 + 4) ⊕ Fin 4) :=
  (Equiv.sumCongr (finSuccEquiv (p + 4)) (Equiv.refl _)).trans
    (optionSumLeft.trans ((Equiv.optionCongr slots).trans
      (optionSumLeft.symm.trans
        (Equiv.sumCongr (finSuccEquiv (k + 4)).symm (Equiv.refl _)))))

def slotsRight {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4)) :
    (Fin (p + 4) ⊕ Fin (q + 1 + 4)) ≃ (Fin (k + 1 + 4) ⊕ Fin 4) :=
  (Equiv.sumCongr (Equiv.refl _) (finSuccEquiv (q + 4))).trans
    (optionSumRight.trans ((Equiv.optionCongr slots).trans
      (optionSumLeft.symm.trans
        (Equiv.sumCongr (finSuccEquiv (k + 4)).symm (Equiv.refl _)))))

theorem slotsLeft_zero {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4)) :
    slotsLeft slots (.inl 0) = .inl 0 := by
  simp [slotsLeft, optionSumLeft, Equiv.optionCongr]

theorem slotsLeft_inl_succ {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4))
    (i : Fin (p + 4)) :
    slotsLeft slots (.inl i.succ) = oldSlot (slots (.inl i)) := by
  cases h : slots (.inl i) <;>
    simp [slotsLeft, optionSumLeft, Equiv.optionCongr, oldSlot, h]

theorem slotsLeft_inr {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4))
    (i : Fin (q + 4)) :
    slotsLeft slots (.inr i) = oldSlot (slots (.inr i)) := by
  cases h : slots (.inr i) <;>
    simp [slotsLeft, optionSumLeft, Equiv.optionCongr, oldSlot, h]

theorem slotsRight_zero {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4)) :
    slotsRight slots (.inr 0) = .inl 0 := by
  simp [slotsRight, optionSumLeft, optionSumRight, Equiv.optionCongr]

theorem slotsRight_inl {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4))
    (i : Fin (p + 4)) :
    slotsRight slots (.inl i) = oldSlot (slots (.inl i)) := by
  cases h : slots (.inl i) <;>
    simp [slotsRight, optionSumLeft, optionSumRight, Equiv.optionCongr, oldSlot, h]

theorem slotsRight_inr_succ {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4))
    (i : Fin (q + 4)) :
    slotsRight slots (.inr i.succ) = oldSlot (slots (.inr i)) := by
  cases h : slots (.inr i) <;>
    simp [slotsRight, optionSumLeft, optionSumRight, Equiv.optionCongr, oldSlot, h]

theorem oldSlot_endpoint {k : ℕ} (j : Fin 4) :
    oldSlot (k := k) (.inr j) = .inr j := rfl

theorem oldSlot_last (k : ℕ) :
    oldSlot (k := k) (.inl (Fin.last (k + 3))) = .inl (Fin.last (k + 4)) := rfl

def differentiateLeft {k : ℕ} (r : CurvatureResidualPattern k) :
    CurvatureResidualPattern (k + 1) :=
  ⟨r.1 + 1, r.2.1, r.2.2.1, slotsLeft r.2.2.2⟩

def differentiateRight {k : ℕ} (r : CurvatureResidualPattern k) :
    CurvatureResidualPattern (k + 1) :=
  ⟨r.1, r.2.1 + 1, r.2.2.1, slotsRight r.2.2.2⟩

theorem coefficient_differentiateLeft {k : ℕ} (r : CurvatureResidualPattern k) :
    (differentiateLeft r).2.2.1 = r.2.2.1 := rfl

theorem coefficient_differentiateRight {k : ℕ} (r : CurvatureResidualPattern k) :
    (differentiateRight r).2.2.1 = r.2.2.1 := rfl

theorem fill_oldSlot {V : Type*} {k : ℕ}
    (P : V) (X : Fin (k + 4) → V) (ends : Fin 4 → V)
    (s : Fin (k + 4) ⊕ Fin 4) :
    Sum.elim (Fin.cons P X) ends (oldSlot s) = Sum.elim X ends s := by
  cases s <;> simp [oldSlot]

theorem fill_slotsLeft_left {V : Type*} {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4))
    (P : V) (X : Fin (k + 4) → V) (ends : Fin 4 → V) :
    (fun j => Sum.elim (Fin.cons P X) ends (slotsLeft slots (.inl j))) =
      Fin.cons P (fun j => Sum.elim X ends (slots (.inl j))) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [slotsLeft_zero]
    rfl
  · rw [slotsLeft_inl_succ, fill_oldSlot]
    rfl

theorem fill_slotsLeft_right {V : Type*} {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4))
    (P : V) (X : Fin (k + 4) → V) (ends : Fin 4 → V) :
    (fun j => Sum.elim (Fin.cons P X) ends (slotsLeft slots (.inr j))) =
      (fun j => Sum.elim X ends (slots (.inr j))) := by
  funext j
  rw [slotsLeft_inr, fill_oldSlot]

theorem fill_slotsRight_left {V : Type*} {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4))
    (P : V) (X : Fin (k + 4) → V) (ends : Fin 4 → V) :
    (fun j => Sum.elim (Fin.cons P X) ends (slotsRight slots (.inl j))) =
      (fun j => Sum.elim X ends (slots (.inl j))) := by
  funext j
  rw [slotsRight_inl, fill_oldSlot]

theorem fill_slotsRight_right {V : Type*} {p q k : ℕ}
    (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4))
    (P : V) (X : Fin (k + 4) → V) (ends : Fin 4 → V) :
    (fun j => Sum.elim (Fin.cons P X) ends (slotsRight slots (.inr j))) =
      Fin.cons P (fun j => Sum.elim X ends (slots (.inr j))) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [slotsRight_zero]
    rfl
  · rw [slotsRight_inr_succ, fill_oldSlot]
    rfl

noncomputable def evaluate {ι V : Type*} [Fintype ι] {k : ℕ}
    (r : CurvatureResidualPattern k) (a : ι → ι → ℝ)
    (low : (m : ℕ) → (Fin (m + 4) → V) → ℝ)
    (E : ι → V) (X : Fin (k + 4) → V) : ℝ :=
  (r.2.2.1 : ℝ) * ∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
    (low r.1 (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inl j))) *
      low r.2.1 (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inr j))))

theorem evaluate_differentiateLeft {ι V : Type*} [Fintype ι] {k : ℕ}
    (r : CurvatureResidualPattern k) (a : ι → ι → ℝ)
    (low : (m : ℕ) → (Fin (m + 4) → V) → ℝ)
    (E : ι → V) (P : V) (X : Fin (k + 4) → V) :
    evaluate (differentiateLeft r) a low E (Fin.cons P X) =
      (r.2.2.1 : ℝ) * ∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low (r.1 + 1)
            (Fin.cons P (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inl j)))) *
          low r.2.1 (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inr j)))) := by
  dsimp only [evaluate, differentiateLeft]
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  rw [fill_slotsLeft_left r.2.2.2 P X (fun s => E (γ s)),
    fill_slotsLeft_right r.2.2.2 P X (fun s => E (γ s))]

theorem evaluate_differentiateRight {ι V : Type*} [Fintype ι] {k : ℕ}
    (r : CurvatureResidualPattern k) (a : ι → ι → ℝ)
    (low : (m : ℕ) → (Fin (m + 4) → V) → ℝ)
    (E : ι → V) (P : V) (X : Fin (k + 4) → V) :
    evaluate (differentiateRight r) a low E (Fin.cons P X) =
      (r.2.2.1 : ℝ) * ∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low r.1 (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inl j))) *
          low (r.2.1 + 1)
            (Fin.cons P (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inr j))))) := by
  dsimp only [evaluate, differentiateRight]
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  rw [fill_slotsRight_left r.2.2.2 P X (fun s => E (γ s)),
    fill_slotsRight_right r.2.2.2 P X (fun s => E (γ s))]

theorem evaluate_differentiation_pair {ι V : Type*} [Fintype ι] {k : ℕ}
    (r : CurvatureResidualPattern k) (a : ι → ι → ℝ)
    (low : (m : ℕ) → (Fin (m + 4) → V) → ℝ)
    (E : ι → V) (P : V) (X : Fin (k + 4) → V) :
    evaluate (differentiateLeft r) a low E (Fin.cons P X) +
        evaluate (differentiateRight r) a low E (Fin.cons P X) =
      (r.2.2.1 : ℝ) * ∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low (r.1 + 1)
            (Fin.cons P (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inl j)))) *
            low r.2.1 (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inr j))) +
          low r.1 (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inl j))) *
            low (r.2.1 + 1)
              (Fin.cons P (fun j => Sum.elim X (fun s => E (γ s)) (r.2.2.2 (.inr j))))) := by
  rw [evaluate_differentiateLeft, evaluate_differentiateRight]
  simp only [mul_add, Finset.sum_add_distrib]

end CurvatureResidualPattern

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem curvature_iterated_insert_lowered_inverse_frame
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (p q : ℕ) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let K := curvatureOnFields_iteratedCovariantDerivative D
    let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (K r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
    ∀ (X : Fin (p + 4) → (y : M) → TangentSpace (𝓡 n) y)
      (Y : Fin (q + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (s : Fin (p + 3)),
      (∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X j)) e.baseSet) →
      (∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (Y j)) e.baseSet) →
      ∀ {x : M}, x ∈ e.baseSet →
      low p (Function.update X s.castSucc (K q Y)) x =
        ∑ i, ∑ j, a x i j *
          (low q (Fin.snoc Y (E j)) x *
            low p (Function.update X s.castSucc (E i)) x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
    x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let K := curvatureOnFields_iteratedCovariantDerivative D
  let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (K r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
  intro X Y s hX hY x hx
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let theta := e.localFrameCoeff (𝓡 n) cb
  let b := g.orthonormalBasis x
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ _ i
  have hW : S (K q Y) :=
    contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D e.open_baseSet q Y hY
  have hframe (W : TangentSpace (𝓡 n) x) :
      W = ∑ i : Fin n, theta i x W • E i x := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V W) hx
  have hgram (i j : Fin n) :
      a x i j = ∑ r, theta i x (b r) * theta j x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hinner (W : TangentSpace (𝓡 n) x) (r) :
      (∑ j : Fin n, theta j x (b r) * g.inner x W (E j x)) = g.inner x W (b r) := by
    nth_rw 2 [hframe (b r)]
    simp only [map_sum, map_smul, smul_eq_mul]
  have horth (W : TangentSpace (𝓡 n) x) :
      (∑ r, g.inner x W (b r) • b r) = W := by
    have hh := b.sum_repr' W
    change (∑ r, g.inner x (b r) W • b r) = W at hh
    simpa only [g.symm x W] using hh
  have hcoeff (i : Fin n) (W : TangentSpace (𝓡 n) x) :
      (∑ j : Fin n, a x i j * g.inner x W (E j x)) = theta i x W := by
    simp only [hgram, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ r, theta i x (b r) *
          (∑ j : Fin n, theta j x (b r) * g.inner x W (E j x)) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ r, theta i x (b r) * g.inner x W (b r) := by simp only [hinner]
      _ = theta i x (∑ r, g.inner x W (b r) • b r) := by
        simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
      _ = _ := by rw [horth]
  have hrec (W : TangentSpace (𝓡 n) x) :
      W = ∑ i : Fin n, ∑ j : Fin n,
        (a x i j * g.inner x W (E j x)) • E i x := by
    nth_rw 1 [hframe W]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_smul, hcoeff]
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D p x
  let v := fun j : Fin (p + 3) => X j.castSucc x
  let z := X (Fin.last (p + 3)) x
  have heval (W : (y : M) → TangentSpace (𝓡 n) y) (hWs : S W) :
      K p (Function.update (Fin.init X) s W) x = T (Function.update v s (W x)) := by
    have hs : ∀ j, S (Function.update (Fin.init X) s W j) := by
      intro j
      by_cases hj : j = s
      · subst j
        simpa only [Function.update_self] using hWs
      · simpa only [Function.update_of_ne hj, Fin.init] using hX j.castSucc
    have hh := hT e.open_baseSet (Function.update (Fin.init X) s W) hs hx
    have htup : (fun j => Function.update (Fin.init X) s W j x) =
        Function.update v s (W x) := by
      funext j
      by_cases hj : j = s
      · subst j
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hj, v, Fin.init]
    rw [htup] at hh
    exact hh.symm
  have hlow (W : (y : M) → TangentSpace (𝓡 n) y) (hWs : S W) :
      low p (Function.update X s.castSucc W) x =
        g.inner x (T (Function.update v s (W x))) z := by
    dsimp only [low]
    rw [Fin.init_update_castSucc, Function.update_of_ne (Fin.castSucc_ne_last s).symm,
      heval W hWs]
  have hlowq (j : Fin n) :
      low q (Fin.snoc Y (E j)) x = g.inner x (K q Y x) (E j x) := by
    simp only [low, Fin.init_snoc, Fin.snoc_last]
  change low p (Function.update X s.castSucc (K q Y)) x =
    ∑ i, ∑ j, a x i j *
      (low q (Fin.snoc Y (E j)) x * low p (Function.update X s.castSucc (E i)) x)
  rw [hlow (K q Y) hW]
  calc
    _ = g.inner x (T (Function.update v s
        (∑ i : Fin n, ∑ j : Fin n,
          (a x i j * g.inner x (K q Y x) (E j x)) • E i x))) z :=
      congrArg (fun W => g.inner x (T (Function.update v s W)) z) (hrec (K q Y x))
    _ = ∑ i : Fin n, ∑ j : Fin n,
        a x i j * (g.inner x (K q Y x) (E j x) *
          g.inner x (T (Function.update v s (E i x))) z) := by
      rw [T.map_update_sum]
      simp only [T.map_update_sum, T.map_update_smul, map_sum, map_smul,
        sum_apply, smul_apply, smul_eq_mul, mul_assoc]
    _ = _ := by
      simp only [hlowq, hlow _ (hE _)]

theorem CurvatureResidualPattern.contMDiffOn_evaluate
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {k : ℕ}
    (r : CurvatureResidualPattern k) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let low := fun m (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (curvatureOnFields_iteratedCovariantDerivative D m (Fin.init Z) y)
        (Z (Fin.last (m + 3)) y)
    ∀ (X : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y),
      (∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X j)) e.baseSet) →
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => CurvatureResidualPattern.evaluate r (a y)
          (fun m Z => low m Z y) E X) e.baseSet := by
  classical
  dsimp only
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ :=
    { contMDiff_mul := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact contDiff_mul.contMDiff }
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun y : M => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let low := fun m (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (curvatureOnFields_iteratedCovariantDerivative D m (Fin.init Z) y)
      (Z (Fin.last (m + 3)) y)
  let Q := fun (Z : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    ∑ γ : Fin 4 → Fin n, (a y (γ 0) (γ 1) * a y (γ 2) (γ 3)) *
      (low r.1 (fun j => Sum.elim Z (fun s => E (γ s)) (r.2.2.2 (.inl j))) y *
        low r.2.1 (fun j => Sum.elim Z (fun s => E (γ s)) (r.2.2.2 (.inr j))) y)
  intro X hX
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) e.baseSet
  let C := fun f : M → ℝ => ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ _ i
  have hlow (m : ℕ) (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) : C (low m Z) :=
    (contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D e.open_baseSet m
      (Fin.init Z) (fun j => hZ j.castSucc)).inner_bundle (hZ (Fin.last (m + 3)))
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
  have hfill (γ : Fin 4 → Fin n) (s : Fin (r.1 + 4) ⊕ Fin (r.2.1 + 4)) :
      S (Sum.elim X (fun j => E (γ j)) (r.2.2.2 s)) := by
    cases r.2.2.2 s with
    | inl i => exact hX i
    | inr j => exact hE (γ j)
  have hQ : C (Q X) := by
    apply contMDiffOn_finsetSum
    intro γ _
    exact ((ha _ _).mul (ha _ _)).mul
      ((hlow r.1 _ (fun j => hfill γ (.inl j))).mul
        (hlow r.2.1 _ (fun j => hfill γ (.inr j))))
  change C (fun y => (r.2.2.1 : ℝ) * Q X y)
  exact contMDiffOn_const.mul hQ

theorem CurvatureResidualPattern.covariant_derivative_evaluate
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {k : ℕ}
    (r : CurvatureResidualPattern k) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
    let low := fun m (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (curvatureOnFields_iteratedCovariantDerivative D m (Fin.init Z) y)
        (Z (Fin.last (m + 3)) y)
    let ev := fun (m : ℕ) (s : CurvatureResidualPattern m)
      (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      CurvatureResidualPattern.evaluate s (a y) (fun j W => low j W y) E Z
    ∀ (P : (y : M) → TangentSpace (𝓡 n) y)
      (X : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) e.baseSet →
      (∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X j)) e.baseSet) →
      ∀ {x : M}, x ∈ e.baseSet →
      mvfderiv (𝓡 n) (ev k r X) x (P x) -
          ∑ j, ev k r (Function.update X j (N P (X j))) x =
        ev (k + 1) (CurvatureResidualPattern.differentiateLeft r) (Fin.cons P X) x +
          ev (k + 1) (CurvatureResidualPattern.differentiateRight r) (Fin.cons P X) x := by
  classical
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun y : M => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
  let low := fun m (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (curvatureOnFields_iteratedCovariantDerivative D m (Fin.init Z) y)
      (Z (Fin.last (m + 3)) y)
  let Q := fun (Z : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    ∑ γ : Fin 4 → Fin n, (a y (γ 0) (γ 1) * a y (γ 2) (γ 3)) *
      (low r.1 (fun j => Sum.elim Z (fun s => E (γ s)) (r.2.2.2 (.inl j))) y *
        low r.2.1 (fun j => Sum.elim Z (fun s => E (γ s)) (r.2.2.2 (.inr j))) y)
  let ev := fun (m : ℕ) (s : CurvatureResidualPattern m)
    (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    CurvatureResidualPattern.evaluate s (a y) (fun j W => low j W y) E Z
  intro P X hP hX x hx
  change mvfderiv (𝓡 n) (ev k r X) x (P x) -
      ∑ j, ev k r (Function.update X j (N P (X j))) x =
    ev (k + 1) (CurvatureResidualPattern.differentiateLeft r) (Fin.cons P X) x +
      ev (k + 1) (CurvatureResidualPattern.differentiateRight r) (Fin.cons P X) x
  have hQ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (Q X) e.baseSet := by
    have hh := CurvatureResidualPattern.contMDiffOn_evaluate D
      (⟨r.1, r.2.1, 1, r.2.2.2⟩ : CurvatureResidualPattern k) x0 X hX
    simpa only [CurvatureResidualPattern.evaluate, Int.cast_one, one_mul] using hh
  have hmdQ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (Q X) x :=
    (hQ.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hderiv : mvfderiv (𝓡 n) (ev k r X) x (P x) =
      (r.2.2.1 : ℝ) * mvfderiv (𝓡 n) (Q X) x (P x) := by
    change mvfderiv (𝓡 n) (fun y => (r.2.2.1 : ℝ) * Q X y) x (P x) = _
    have hh := congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (P x))
      (mvfderiv_fun_mul (mdifferentiableAt_const (c := (r.2.2.1 : ℝ))) hmdQ)
    simpa only [mvfderiv_const, smul_zero, add_zero, smul_apply, smul_eq_mul] using hh
  have hraw := curvature_two_factor_contraction_derivative D r.1 r.2.1 r.2.2.2
    x0 P X hP hX hx
  rw [show Classical.decEq (Fin (k + 4)) =
    (inferInstance : DecidableEq (Fin (k + 4))) from Subsingleton.elim _ _] at hraw
  change mvfderiv (𝓡 n) (Q X) x (P x) -
    (∑ j, Q (Function.update X j (N P (X j))) x) = _ at hraw
  rw [hderiv]
  change (r.2.2.1 : ℝ) * mvfderiv (𝓡 n) (Q X) x (P x) -
    (∑ j, (r.2.2.1 : ℝ) * Q (Function.update X j (N P (X j))) x) = _
  rw [← Finset.mul_sum, ← mul_sub, hraw]
  exact (CurvatureResidualPattern.evaluate_differentiation_pair r (a x)
    (fun m Z => low m Z x) E P X).symm

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem CurvatureResidualPattern.covariant_derivative_evaluate_list
    {g : RiemannianMetric n M} (D : LeviCivitaData g) {k : ℕ}
    (ps : List (CurvatureResidualPattern k)) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
    let low := fun m (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (curvatureOnFields_iteratedCovariantDerivative D m (Fin.init Z) y)
        (Z (Fin.last (m + 3)) y)
    let ev := fun (m : ℕ) (s : CurvatureResidualPattern m)
      (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      CurvatureResidualPattern.evaluate s (a y) (fun j W => low j W y) E Z
    let total := fun (m : ℕ) (qs : List (CurvatureResidualPattern m))
      (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      (qs.map (fun s => ev m s Z y)).sum
    let next := ps.flatMap (fun s =>
      [CurvatureResidualPattern.differentiateLeft s,
        CurvatureResidualPattern.differentiateRight s])
    ∀ (P : (y : M) → TangentSpace (𝓡 n) y)
      (X : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) e.baseSet →
      (∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X j)) e.baseSet) →
      ∀ {x : M}, x ∈ e.baseSet →
      mvfderiv (𝓡 n) (total k ps X) x (P x) -
          ∑ j, total k ps (Function.update X j (N P (X j))) x =
        total (k + 1) next (Fin.cons P X) x := by
  classical
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun y : M => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
  let low := fun m (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (curvatureOnFields_iteratedCovariantDerivative D m (Fin.init Z) y)
      (Z (Fin.last (m + 3)) y)
  let ev := fun (m : ℕ) (s : CurvatureResidualPattern m)
    (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    CurvatureResidualPattern.evaluate s (a y) (fun j W => low j W y) E Z
  let total := fun (m : ℕ) (qs : List (CurvatureResidualPattern m))
    (Z : Fin (m + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    (qs.map (fun s => ev m s Z y)).sum
  intro P X hP hX x hx
  have hs (r : CurvatureResidualPattern k) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (ev k r X) e.baseSet :=
    CurvatureResidualPattern.contMDiffOn_evaluate D r x0 X hX
  have htotal (qs : List (CurvatureResidualPattern k)) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (total k qs X) e.baseSet := by
    induction qs with
    | nil => exact contMDiffOn_const
    | cons r rs ih => exact (hs r).add ih
  change mvfderiv (𝓡 n) (total k ps X) x (P x) -
      ∑ j, total k ps (Function.update X j (N P (X j))) x =
    total (k + 1) (ps.flatMap (fun r =>
      [CurvatureResidualPattern.differentiateLeft r,
        CurvatureResidualPattern.differentiateRight r])) (Fin.cons P X) x
  induction ps with
  | nil => simp [total, mvfderiv_const]
  | cons r rs ih =>
    have hr := CurvatureResidualPattern.covariant_derivative_evaluate D r x0 P X hP hX hx
    change mvfderiv (𝓡 n) (ev k r X) x (P x) -
        ∑ j, ev k r (Function.update X j (N P (X j))) x =
      ev (k + 1) (CurvatureResidualPattern.differentiateLeft r) (Fin.cons P X) x +
        ev (k + 1) (CurvatureResidualPattern.differentiateRight r) (Fin.cons P X) x at hr
    have hmdr := ((hs r).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
      (by simp)
    have hmdrs := ((htotal rs).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
      (by simp)
    change mvfderiv (𝓡 n) (fun y => ev k r X y + total k rs X y) x (P x) -
        ∑ j, (ev k r (Function.update X j (N P (X j))) x +
          total k rs (Function.update X j (N P (X j))) x) =
      ev (k + 1) (CurvatureResidualPattern.differentiateLeft r) (Fin.cons P X) x +
        (ev (k + 1) (CurvatureResidualPattern.differentiateRight r) (Fin.cons P X) x +
          total (k + 1) (rs.flatMap (fun s =>
            [CurvatureResidualPattern.differentiateLeft s,
              CurvatureResidualPattern.differentiateRight s])) (Fin.cons P X) x)
    rw [mvfderiv_fun_add hmdr hmdrs, add_apply, Finset.sum_add_distrib]
    linarith

end PoincareConjecture.Proofs.M03

import PoincareConjecture.Proofs.M03.CurvatureTrilinear
import PoincareConjecture.Proofs.M03.MetricInverse
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_curvatureOnFields_derivative_quadrilinearMap
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) :
    let dR := fun
        (A B C E : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection (fun z => D.curvatureOnFields B C E z) y (A y) -
        D.curvatureOnFields
          (fun z => D.connection B z (A z)) C E y -
        D.curvatureOnFields B
          (fun z => D.connection C z (A z)) E y -
        D.curvatureOnFields B C
          (fun z => D.connection E z (A z)) y
    ∃ K : TangentSpace (𝓡 n) x →ₗ[ℝ]
        TangentSpace (𝓡 n) x →ₗ[ℝ]
        TangentSpace (𝓡 n) x →ₗ[ℝ]
        TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x,
      ∀ {U : Set M}, IsOpen U →
      ∀ (A B C E : (y : M) → TangentSpace (𝓡 n) y),
        ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U →
        ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U →
        ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U →
        ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% E) U →
        x ∈ U → K (A x) (B x) (C x) (E x) = dR A B C E x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection B y (A y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let K := fun (A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
    N A (R B C W) y - R (N A B) C W y -
      R B (N A C) W y - R B C (N A W) y
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let b0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let b := e.basisAt b0 he
  let E := e.localFrame b0
  let J3 (i j k : Fin n) :
      TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
    b.constr ℝ fun l => K (E i) (E j) (E k) (E l) x
  let J2 (i j : Fin n) : TangentSpace (𝓡 n) x →ₗ[ℝ]
      TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
    b.constr ℝ (J3 i j)
  let J1 (i : Fin n) : TangentSpace (𝓡 n) x →ₗ[ℝ]
      TangentSpace (𝓡 n) x →ₗ[ℝ]
      TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
    b.constr ℝ (J2 i)
  let J0 : TangentSpace (𝓡 n) x →ₗ[ℝ]
      TangentSpace (𝓡 n) x →ₗ[ℝ]
      TangentSpace (𝓡 n) x →ₗ[ℝ]
      TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
    b.constr ℝ J1
  refine ⟨J0, ?_⟩
  intro U hU A B C W hA hB hC hW hx
  change J0 (A x) (B x) (C x) (W x) = K A B C W x
  let V := U ∩ e.baseSet
  have hV : IsOpen V := hU.inter e.open_baseSet
  have hxV : x ∈ V := ⟨hx, he⟩
  let S := fun Q : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) V
  have hAV : S A := hA.mono inter_subset_left
  have hBV : S B := hB.mono inter_subset_left
  have hCV : S C := hC.mono inter_subset_left
  have hWV : S W := hW.mono inter_subset_left
  have hE (i : Fin n) : S (E i) :=
    (e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b0 i).mono inter_subset_right
  have hmd (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q)
      {y : M} (hy : y ∈ V) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Q) y :=
    (hQ.contMDiffAt (hV.mem_nhds hy)).mdifferentiableAt (by simp)
  have hN (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) : S (N P Q) :=
    D.contMDiffOn_connection_apply hV P Q hP hQ
  have hR (P Q T : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hT : S T) : S (R P Q T) := by
    have hL : S (VectorField.mlieBracket (𝓡 n) P Q) := by
      intro y hy
      exact ((hP.contMDiffAt (hV.mem_nhds hy)).mlieBracket_vectorField
        (hQ.contMDiffAt (hV.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hN P _ hP (hN Q T hQ hT)).sub_section
      (hN Q _ hQ (hN P T hP hT))).sub_section (hN _ T hL hT)
  choose T hT using fun y : M => exists_curvature_trilinearMap D y
  have heval (P Q W : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hW : S W) {y : M} (hy : y ∈ V) :
      R P Q W y = T y (P y) (Q y) (W y) :=
    ((hT y (P y) (Q y) (W y)).trans
      (curvature_eq_curvatureOnFields D hV P Q W hP hQ hW hy)).symm
  let q := fun (i : Fin n) (Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    e.localFrameCoeff (𝓡 n) b0 i y (Q y)
  have hq (i : Fin n) (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q i Q) V :=
    contMDiffOn_localFrameCoeff b0 hV inter_subset_right hQ i
  have hqmd (i : Fin n) (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (q i Q) x :=
    ((hq i Q hQ).contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
  have hqrepr (Q : (y : M) → TangentSpace (𝓡 n) y) (i : Fin n)
      {y : M} (hy : y ∈ e.baseSet) :
      q i Q y = (e.basisAt b0 hy).repr (Q y) i :=
    e.localFrameCoeff_apply_of_mem_baseSet b0 hy Q i
  have hEvalue (i : Fin n) {y : M} (hy : y ∈ e.baseSet) :
      E i y = e.basisAt b0 hy i := e.localFrame_apply_of_mem_baseSet b0 hy
  have hrec (Q : (y : M) → TangentSpace (𝓡 n) y)
      {y : M} (hy : y ∈ V) : Q y = ∑ i, q i Q y • E i y := by
    simpa only [hqrepr Q _ hy.2, hEvalue _ hy.2] using
      ((e.basisAt b0 hy.2).sum_repr (Q y)).symm
  have hqx (Q : (y : M) → TangentSpace (𝓡 n) y) (i : Fin n) :
      b.equivFun (Q x) i = q i Q x := by
    simpa only [Module.Basis.equivFun_apply] using (hqrepr Q i he).symm
  have hlin (L : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x)
      (Q : (y : M) → TangentSpace (𝓡 n) y) :
      L (Q x) = ∑ i, q i Q x • L (E i x) := by
    rw [hrec Q hxV, map_sum]
    simp only [map_smul]
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hnsum (Q : Fin n → (y : M) → TangentSpace (𝓡 n) y)
      (hQ : ∀ i, MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% (Q i)) x)
      (v : TangentSpace (𝓡 n) x) :
      D.connection (fun y => ∑ i, Q i y) x v = ∑ i, D.connection (Q i) x v := by
    have aux (s : Finset (Fin n)) :
        D.connection (fun y => ∑ i ∈ s, Q i y) x v =
          ∑ i ∈ s, D.connection (Q i) x v := by
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        change D.connection 0 x v = 0
        rw [hc.zero, zero_apply]
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        change D.connection (Q i + fun y => ∑ j ∈ s, Q j y) x v = _
        rw [hc.add (hQ i) (MDifferentiableAt.sum_section fun j _ => hQ j),
          add_apply, ih]
    exact aux Finset.univ
  have hframe (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (Z : Fin n → (y : M) → TangentSpace (𝓡 n) y)
      (f : Fin n → M → ℝ) (hQ : S Q) (hZ : ∀ i, S (Z i))
      (hf : ∀ i, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f i) x)
      (heq : ∀ y ∈ V, Q y = ∑ i, f i y • Z i y) :
      N P Q x = ∑ i, (f i x • N P (Z i) x +
        mvfderiv (𝓡 n) (f i) x (P x) • Z i x) := by
    have hs (i : Fin n) : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (T% ((f i) • Z i)) x := (hf i).smul_section (hmd _ (hZ i) hxV)
    have hloc := hc.congr_of_eventuallyEq (hmd Q hQ hxV)
      (MDifferentiableAt.sum_section fun i _ => hs i) Filter.univ_mem
      (Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) heq)
    calc
      _ = D.connection (fun y => ∑ i, f i y • Z i y) x (P x) :=
        congrArg (fun L => L (P x)) hloc
      _ = ∑ i, D.connection ((f i) • Z i) x (P x) :=
        hnsum (fun i => (f i) • Z i) hs (P x)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [N, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] using
          congrArg (fun L => L (P x)) (hc.leibniz (hmd _ (hZ i) hxV) (hf i))
  have hdiff
      (F : ((y : M) → TangentSpace (𝓡 n) y) → (y : M) → TangentSpace (𝓡 n) y)
      (L : (y : M) → TangentSpace (𝓡 n) y →ₗ[ℝ] TangentSpace (𝓡 n) y)
      (hF : ∀ Q, S Q → S (F Q))
      (hFL : ∀ Q, S Q → ∀ y ∈ V, F Q y = L y (Q y))
      (P Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
      N P (F Q) x - L x (N P Q x) =
        ∑ i, q i Q x • (N P (F (E i)) x - L x (N P (E i) x)) := by
    have hFeq (y : M) (hy : y ∈ V) :
        F Q y = ∑ i, q i Q y • F (E i) y := by
      rw [hFL Q hQ y hy, hrec Q hy, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, hFL (E i) (hE i) y hy]
    rw [hframe P (F Q) (fun i => F (E i)) (fun i => q i Q)
      (hF Q hQ) (fun i => hF (E i) (hE i)) (fun i => hqmd i Q hQ) hFeq,
      hframe P Q E (fun i => q i Q) hQ hE (fun i => hqmd i Q hQ)
        (fun y hy => hrec Q hy), map_sum]
    simp only [map_add, map_smul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hFL (E i) (hE i) x hxV, smul_sub]
    module
  have hKA (A B C W : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hW : S W) :
      K A B C W x = ∑ i, q i A x • K (E i) B C W x := by
    let L : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
      (D.connection (R B C W) x).toLinearMap -
        (((T x).flip (C x)).flip (W x)).comp (D.connection B x).toLinearMap -
        ((T x (B x)).flip (W x)).comp (D.connection C x).toLinearMap -
        (T x (B x) (C x)).comp (D.connection W x).toLinearMap
    have hform (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
        K Q B C W x = L (Q x) := by
      dsimp only [K]
      rw [heval (N Q B) C W (hN Q B hQ hB) hC hW hxV,
        heval B (N Q C) W hB (hN Q C hQ hC) hW hxV,
        heval B C (N Q W) hB hC (hN Q W hQ hW) hxV]
      rfl
    rw [hform A hA, hlin L A]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
  have hKB (A B C W : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hW : S W) :
      K A B C W x = ∑ i, q i B x • K A (E i) C W x := by
    let L := fun y => ((T y).flip (C y)).flip (W y)
    let Lc := ((T x).flip (N A C x)).flip (W x)
    let Lw := ((T x).flip (C x)).flip (N A W x)
    have hform (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
        K A Q C W x =
          (N A (R Q C W) x - L x (N A Q x)) - Lc (Q x) - Lw (Q x) := by
      dsimp only [K]
      rw [heval (N A Q) C W (hN A Q hA hQ) hC hW hxV,
        heval Q (N A C) W hQ (hN A C hA hC) hW hxV,
        heval Q C (N A W) hQ hC (hN A W hA hW) hxV]
      rfl
    rw [hform B hB,
      hdiff (fun Q => R Q C W) L (fun Q hQ => hR Q C W hQ hC hW)
        (fun Q hQ y hy => heval Q C W hQ hC hW hy) A B hB,
      hlin Lc B, hlin Lw B, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
    simp only [smul_sub]
  have hKC (A B C W : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hW : S W) :
      K A B C W x = ∑ i, q i C x • K A B (E i) W x := by
    let L := fun y => (T y (B y)).flip (W y)
    let Lb := (T x (N A B x)).flip (W x)
    let Lw := (T x (B x)).flip (N A W x)
    have hform (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
        K A B Q W x =
          (N A (R B Q W) x - L x (N A Q x)) - Lb (Q x) - Lw (Q x) := by
      dsimp only [K]
      rw [heval (N A B) Q W (hN A B hA hB) hQ hW hxV,
        heval B (N A Q) W hB (hN A Q hA hQ) hW hxV,
        heval B Q (N A W) hB hQ (hN A W hA hW) hxV]
      dsimp only [L, Lb, Lw, LinearMap.flip_apply]
      module
    rw [hform C hC,
      hdiff (fun Q => R B Q W) L (fun Q hQ => hR B Q W hB hQ hW)
        (fun Q hQ y hy => heval B Q W hB hQ hW hy) A C hC,
      hlin Lb C, hlin Lw C, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
    simp only [smul_sub]
  have hKW (A B C W : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hW : S W) :
      K A B C W x = ∑ i, q i W x • K A B C (E i) x := by
    let L := fun y => T y (B y) (C y)
    let Lb := T x (N A B x) (C x)
    let Lc := T x (B x) (N A C x)
    have hform (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
        K A B C Q x =
          (N A (R B C Q) x - L x (N A Q x)) - Lb (Q x) - Lc (Q x) := by
      dsimp only [K]
      rw [heval (N A B) C Q (hN A B hA hB) hC hQ hxV,
        heval B (N A C) Q hB (hN A C hA hC) hQ hxV,
        heval B C (N A Q) hB hC (hN A Q hA hQ) hxV]
      dsimp only [L, Lb, Lc]
      module
    rw [hform W hW,
      hdiff (fun Q => R B C Q) L (fun Q hQ => hR B C Q hB hC hQ)
        (fun Q hQ y hy => heval B C Q hB hC hQ hy) A W hW,
      hlin Lb W, hlin Lc W, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hform (E i) (hE i)]
    simp only [smul_sub]
  have hJ3 (i j k : Fin n)
      (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      J3 i j k (W x) = K (E i) (E j) (E k) W x := by
    dsimp only [J3]
    rw [Module.Basis.constr_apply_fintype]
    simp only [hqx W]
    exact (hKW (E i) (E j) (E k) W (hE i) (hE j) (hE k) hW).symm
  have hJ2 (i j : Fin n)
      (C W : (y : M) → TangentSpace (𝓡 n) y) (hC : S C) (hW : S W) :
      J2 i j (C x) (W x) = K (E i) (E j) C W x := by
    calc
      _ = ∑ k, q k C x • J3 i j k (W x) := by
        dsimp only [J2]
        rw [Module.Basis.constr_apply_fintype]
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, hqx C]
      _ = ∑ k, q k C x • K (E i) (E j) (E k) W x := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hJ3 i j k W hW]
      _ = _ := (hKC (E i) (E j) C W (hE i) (hE j) hC hW).symm
  have hJ1 (i : Fin n)
      (B C W : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) (hC : S C) (hW : S W) :
      J1 i (B x) (C x) (W x) = K (E i) B C W x := by
    calc
      _ = ∑ j, q j B x • J2 i j (C x) (W x) := by
        dsimp only [J1]
        rw [Module.Basis.constr_apply_fintype]
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, hqx B]
      _ = ∑ j, q j B x • K (E i) (E j) C W x := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hJ2 i j C W hC hW]
      _ = _ := (hKB (E i) B C W (hE i) hB hC hW).symm
  calc
    _ = ∑ i, q i A x • J1 i (B x) (C x) (W x) := by
      dsimp only [J0]
      rw [Module.Basis.constr_apply_fintype]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hqx A]
    _ = ∑ i, q i A x • K (E i) B C W x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hJ1 i B C W hBV hCV hWV]
    _ = _ := (hKA A B C W hAV hBV hCV hWV).symm

end PoincareConjecture.Proofs.M03

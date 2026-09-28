import PoincareConjecture.Proofs.M03.CurvatureRicciDerivative
import PoincareConjecture.Proofs.M03.CurvatureSecondBianchi
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Set

universe u v

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureOnFields_contracted_bianchi
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
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
    (∑ i, b.repr
      (dR (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)) X Y Z x) i) =
      dRic X Y Z x - dRic Y X Z x := by
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
  have hXV : S X := hX.mono inter_subset_left
  have hYV : S Y := hY.mono inter_subset_left
  have hZV : S Z := hZ.mono inter_subset_left
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
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hbx : e.basisAt b0 he = b := by
    ext i
    simp only [Bundle.Trivialization.basisAt, b0, Module.Basis.map_apply,
      LinearEquiv.symm_apply_apply]
  have hθx (v : TangentSpace (𝓡 n) x) (i : ι) :
      θ i x v = b.repr v i := by
    simpa only [FiberBundle.extend_apply_self, hbx] using
      hθrepr (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) i he
  have htraceK (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      H A B C x = ∑ i, θ i x (K A (E i) B C x) := by
    simpa only [hθx, E, K, H, N, R] using
      ricci_covariant_derivative_eq_sum_basis D hV A B C hA hB hC hxV b
  have hswapK (A B C W : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) (hC : S C) (hW : S W) :
      K A B C W x = -K A C B W x := by
    have hwhole : R B C W = -R C B W :=
      funext fun y => curvatureOnFields_swap D B C W y
    have hneg : N A (-R C B W) x = -N A (R C B W) x := by
      simpa only [N, neg_one_smul, neg_apply] using
        congrArg (fun T => T (A x))
          (hc.smul_const (-1 : ℝ) (hmd _ (hR C B W hC hB hW) hxV))
    dsimp only [K]
    rw [hwhole, hneg]
    dsimp only [R]
    rw [curvatureOnFields_swap D (N A B) C W x,
      curvatureOnFields_swap D B (N A C) W x,
      curvatureOnFields_swap D B C (N A W) x]
    module
  have hbianchi (i : ι) :
      θ i x (K (E i) X Y Z x) - θ i x (K X (E i) Y Z x) +
        θ i x (K Y (E i) X Z x) = 0 := by
    have hb := curvatureOnFields_second_bianchi D hV (E i) X Y Z
      (hE i) hXV hYV hZV hxV
    change K (E i) X Y Z x + K X Y (E i) Z x + K Y (E i) X Z x = 0 at hb
    rw [hswapK X Y (E i) Z hYV (hE i) hZV] at hb
    simpa only [map_add, map_neg, map_zero, sub_eq_add_neg] using
      congrArg (θ i x) hb
  have hsum : (∑ i, θ i x (K (E i) X Y Z x)) - H X Y Z x + H Y X Z x = 0 := by
    have hz : (∑ i, (θ i x (K (E i) X Y Z x) -
        θ i x (K X (E i) Y Z x) + θ i x (K Y (E i) X Z x))) = 0 :=
      Finset.sum_eq_zero fun i _ => hbianchi i
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← htraceK X Y Z hXV hYV hZV, ← htraceK Y X Z hYV hXV hZV] at hz
    exact hz
  have hfinal : (∑ i, θ i x (K (E i) X Y Z x)) = H X Y Z x - H Y X Z x := by
    linarith only [hsum]
  simpa only [hθx, E, K, H, N, R] using hfinal

end PoincareConjecture.Proofs.M03

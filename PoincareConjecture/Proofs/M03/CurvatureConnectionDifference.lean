import PoincareConjecture.Proofs.M03.CurvatureTrilinear
import PoincareConjecture.Proofs.M03.ConnectionNativeTime
import PoincareConjecture.Proofs.M03.RicciHessianCommutator

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem curvature_covariant_derivative_connection_change
    {g g' : RiemannianMetric n M}
    (D : LeviCivitaData g) (D' : LeviCivitaData g')
    {U : Set M} (hU : IsOpen U)
    (P X Y Z : (y : M) → TangentSpace (𝓡 n) y)
    (hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    let R := D'.curvatureOnFields
    let N := fun (V : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection V y (P y)
    let N' := fun (V : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D'.connection V y (P y)
    let C := CovariantDerivative.difference D.connection D'.connection x
    (N (R X Y Z) x - R (N X) Y Z x - R X (N Y) Z x - R X Y (N Z) x) -
      (N' (R X Y Z) x - R (N' X) Y Z x - R X (N' Y) Z x - R X Y (N' Z) x) =
      C (D'.curvature x (X x) (Y x) (Z x)) (P x) -
        D'.curvature x (C (X x) (P x)) (Y x) (Z x) -
        D'.curvature x (X x) (C (Y x) (P x)) (Z x) -
        D'.curvature x (X x) (Y x) (C (Z x) (P x)) := by
  classical
  dsimp only
  let R := D'.curvatureOnFields
  let N := fun (V : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.connection V y (P y)
  let N' := fun (V : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D'.connection V y (P y)
  let C := CovariantDerivative.difference D.connection D'.connection x
  have hmd (V : (y : M) → TangentSpace (𝓡 n) y)
      (hV : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U)
      {y : M} (hy : y ∈ U) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% V) y :=
    (hV.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hConn (Q V : (y : M) → TangentSpace (𝓡 n) y)
      (hQ : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U)
      (hV : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U) :
      ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (fun y => D.connection V y (Q y))) U := by
    exact D.contMDiffOn_connection_apply hU Q V hQ hV
  have hConn' (Q V : (y : M) → TangentSpace (𝓡 n) y)
      (hQ : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U)
      (hV : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U) :
      ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (fun y => D'.connection V y (Q y))) U := by
    exact D'.contMDiffOn_connection_apply hU Q V hQ hV
  have hN (V : (y : M) → TangentSpace (𝓡 n) y)
      (hV : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U) :
      ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (N V)) U := by
    simpa only [N] using hConn P V hP hV
  have hN' (V : (y : M) → TangentSpace (𝓡 n) y)
      (hV : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U) :
      ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (N' V)) U := by
    simpa only [N'] using hConn' P V hP hV
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  have hR (A B E : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
      (hE : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% E) U) :
      ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (R A B E)) U := by
    have hbr : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (VectorField.mlieBracket (𝓡 n) A B)) U := by
      intro y hy
      exact ((hA.contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
        (hB.contMDiffAt (hU.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hConn' A (fun y => D'.connection E y (B y)) hA
      (hConn' B E hB hE)).sub_section
      (hConn' B (fun y => D'.connection E y (A y)) hB
        (hConn' A E hA hE))).sub_section
      (hConn' (VectorField.mlieBracket (𝓡 n) A B) E hbr hE)
  have hRXYZ := hR X Y Z hX hY hZ
  have hNX := hN X hX
  have hNY := hN Y hY
  have hNZ := hN Z hZ
  have hN'X := hN' X hX
  have hN'Y := hN' Y hY
  have hN'Z := hN' Z hZ
  have hdiff (V : (y : M) → TangentSpace (𝓡 n) y)
      (hV : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U) :
      C (V x) (P x) = D.connection V x (P x) - D'.connection V x (P x) := by
    have h := IsCovariantDerivativeOn.difference_apply
      D.connection.isCovariantDerivativeOnUniv
      D'.connection.isCovariantDerivativeOnUniv (Set.mem_univ x)
      (hmd V hV hx)
    exact congrArg (fun L => L (P x)) h
  have hcurv (A B E : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
      (hE : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% E) U) :
      D'.curvature x (A x) (B x) (E x) = R A B E x := by
    exact curvature_eq_curvatureOnFields D' hU A B E hA hB hE hx
  obtain ⟨TR, hTR⟩ := exists_curvature_trilinearMap D' x
  have hlin (a b c : TangentSpace (𝓡 n) x) :
      TR a b c = D'.curvature x a b c := hTR a b c
  have hRsub (a b b' c : TangentSpace (𝓡 n) x) :
      D'.curvature x a (b - b') c =
        D'.curvature x a b c - D'.curvature x a b' c := by
    calc
      D'.curvature x a (b - b') c = TR a (b - b') c :=
        (hlin a (b - b') c).symm
      _ = TR a b c - TR a b' c := by
        simp only [map_sub]
        rfl
      _ = D'.curvature x a b c - D'.curvature x a b' c := by
        simp only [hlin]
  have hRsubFirst (a a' b c : TangentSpace (𝓡 n) x) :
      D'.curvature x (a - a') b c =
        D'.curvature x a b c - D'.curvature x a' b c := by
    calc
      D'.curvature x (a - a') b c = TR (a - a') b c :=
        (hlin (a - a') b c).symm
      _ = TR a b c - TR a' b c := by
        simp only [map_sub]
        rfl
      _ = D'.curvature x a b c - D'.curvature x a' b c := by
        simp only [hlin]
  have hRsub' (a b c c' : TangentSpace (𝓡 n) x) :
      D'.curvature x a b (c - c') =
        D'.curvature x a b c - D'.curvature x a b c' := by
    calc
      D'.curvature x a b (c - c') = TR a b (c - c') :=
        (hlin a b (c - c')).symm
      _ = TR a b c - TR a b c' := by
        simp only [map_sub]
      _ = D'.curvature x a b c - D'.curvature x a b c' := by
        simp only [hlin]
  have hout :
      C (R X Y Z x) (P x) =
        D.connection (D'.curvatureOnFields X Y Z) x (P x) -
          D'.connection (D'.curvatureOnFields X Y Z) x (P x) := by
    simpa only [R] using (hdiff (R X Y Z) hRXYZ)
  have hinX :
      C (X x) (P x) = N X x - N' X x := by
    exact hdiff X hX
  have hinY :
      C (Y x) (P x) = N Y x - N' Y x := by
    exact hdiff Y hY
  have hinZ :
      C (Z x) (P x) = N Z x - N' Z x := by
    exact hdiff Z hZ
  have hRout : R X Y Z x = D'.curvature x (X x) (Y x) (Z x) :=
    (hcurv X Y Z hX hY hZ).symm
  have hRNX : R (N X) Y Z x = D'.curvature x (N X x) (Y x) (Z x) :=
    (hcurv (N X) Y Z hNX hY hZ).symm
  have hRNY : R X (N Y) Z x = D'.curvature x (X x) (N Y x) (Z x) :=
    (hcurv X (N Y) Z hX hNY hZ).symm
  have hRNZ : R X Y (N Z) x = D'.curvature x (X x) (Y x) (N Z x) :=
    (hcurv X Y (N Z) hX hY hNZ).symm
  have hRN'X : R (N' X) Y Z x = D'.curvature x (N' X x) (Y x) (Z x) :=
    (hcurv (N' X) Y Z hN'X hY hZ).symm
  have hRN'Y : R X (N' Y) Z x = D'.curvature x (X x) (N' Y x) (Z x) :=
    (hcurv X (N' Y) Z hX hN'Y hZ).symm
  have hRN'Z : R X Y (N' Z) x = D'.curvature x (X x) (Y x) (N' Z x) :=
    (hcurv X Y (N' Z) hX hY hN'Z).symm
  have hRNXc : D'.curvatureOnFields (fun y => D.connection X y (P y)) Y Z x =
      D'.curvature x (N X x) (Y x) (Z x) := by
    simpa only [R, N] using hRNX
  have hRNYc : D'.curvatureOnFields X (fun y => D.connection Y y (P y)) Z x =
      D'.curvature x (X x) (N Y x) (Z x) := by
    simpa only [R, N] using hRNY
  have hRNZc : D'.curvatureOnFields X Y (fun y => D.connection Z y (P y)) x =
      D'.curvature x (X x) (Y x) (N Z x) := by
    simpa only [R, N] using hRNZ
  have hRN'Xc : D'.curvatureOnFields (fun y => D'.connection X y (P y)) Y Z x =
      D'.curvature x (N' X x) (Y x) (Z x) := by
    simpa only [R, N'] using hRN'X
  have hRN'Yc : D'.curvatureOnFields X (fun y => D'.connection Y y (P y)) Z x =
      D'.curvature x (X x) (N' Y x) (Z x) := by
    simpa only [R, N'] using hRN'Y
  have hRN'Zc : D'.curvatureOnFields X Y (fun y => D'.connection Z y (P y)) x =
      D'.curvature x (X x) (Y x) (N' Z x) := by
    simpa only [R, N'] using hRN'Z
  rw [← hRout, hout, hRNXc, hRNYc, hRNZc, hRN'Xc, hRN'Yc, hRN'Zc]
  rw [hinX, hinY, hinZ]
  rw [hRsubFirst, hRsub, hRsub']
  module

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ricciFlow_iteratedCurvature_connection_correction_two_contractions
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) (k : ℕ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let g := F.metric t
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let K := curvatureOnFields_iteratedCovariantDerivative (F.connection t)
    let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (K r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
    let B := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      deriv (fun s => (F.connection s).connection Q y (P y)) t
    let rho := fun i j P Q z y =>
      -low 1 ![P, E i, Q, z, E j] y - low 1 ![Q, E i, z, P, E j] y +
        low 1 ![z, E i, P, Q, E j] y
    ∀ (P z : (y : M) → TangentSpace (𝓡 n) y)
      (Y : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) e.baseSet →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% z) e.baseSet →
      (∀ l, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (Y l)) e.baseSet) →
      ∀ {x : M}, x ∈ e.baseSet →
      g.inner x (B P (K k Y) x - ∑ l, K k (Function.update Y l (B P (Y l))) x) (z x) =
        ∑ i, ∑ j, ∑ u, ∑ v, (a x i j * a x u v) *
          (rho i j P (E u) z x * low k (Fin.snoc Y (E v)) x -
            ∑ l, rho i j P (Y l) (E v) x *
              low k (Fin.snoc (Function.update Y l (E u)) z) x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  dsimp only
  let g := F.metric t
  let D := F.connection t
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
    x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let K := curvatureOnFields_iteratedCovariantDerivative D
  let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (K r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
  let B := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    deriv (fun s => (F.connection s).connection Q y (P y)) t
  let rho := fun i j P Q z y =>
    -low 1 ![P, E i, Q, z, E j] y - low 1 ![Q, E i, z, P, E j] y +
      low 1 ![z, E i, P, Q, E j] y
  intro P z Y hP hz hY x hx
  let S := fun Q : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Q) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hKY : S (K k Y) :=
    contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D e.open_baseSet k Y hY
  have hB (l : Fin (k + 3)) : S (B P (Y l)) :=
    (family_tangent_time_derivative (F.metric 0) e.open_baseSet
      (fun s y => (F.connection s).connection (Y l) y (P y))
      (contMDiffOn_connection_family_apply F.smooth F.connection e.open_baseSet
        (Y l) P (hY l) hP) ht).2
  let b := g.orthonormalBasis x
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
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
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
  have hpair (A C Z : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hC : S C) (hZ : S Z) :
      g.inner x (B A C x) (Z x) = ∑ i, ∑ j, a x i j * rho i j A C Z x := by
    have hh := ricciFlow_connection_variation_pairing_eq_inverse_frame
      F ht x0 A C Z hA hC hZ hx
    change g.inner x (B A C x) (Z x) =
      -(∑ i, ∑ j, a x i j * low 1 ![A, E i, C, Z, E j] x) -
        (∑ i, ∑ j, a x i j * low 1 ![C, E i, Z, A, E j] x) +
        ∑ i, ∑ j, a x i j * low 1 ![Z, E i, A, C, E j] x at hh
    rw [hh]
    simp only [rho, mul_add, mul_sub, mul_neg, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hlow (r : ℕ) (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (w : (y : M) → TangentSpace (𝓡 n) y) :
      low r (Fin.snoc Z w) x = g.inner x (K r Z x) (w x) := by
    simp only [low, Fin.init_snoc, Fin.snoc_last]
  obtain ⟨BT, hBT⟩ := exists_ricciFlow_connection_variation_bilinearMap F ht x
  have hBTe (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
      B P Q x = BT (P x) (Q x) :=
    (hBT e.open_baseSet P Q hP hQ hx).symm
  have hout : g.inner x (B P (K k Y) x) (z x) =
      ∑ u, ∑ v, a x u v *
        ((∑ i, ∑ j, a x i j * rho i j P (E u) z x) * low k (Fin.snoc Y (E v)) x) := by
    rw [hBTe _ hKY]
    nth_rw 1 [hrec (K k Y x)]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [← hBTe (E u) (hE u), hpair P (E u) z hP (hE u) hz, hlow]
    ac_rfl
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D k x
  let vals := fun l => Y l x
  have hup (l : Fin (k + 3)) (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      K k (Function.update Y l W) x = T (Function.update vals l (W x)) := by
    have hh := hT e.open_baseSet (Function.update Y l W)
      (fun j => by
        by_cases hj : j = l
        · subst j; simpa only [Function.update_self] using hW
        · simpa only [Function.update_of_ne hj] using hY j) hx
    change T (fun j => Function.update Y l W j x) =
      K k (Function.update Y l W) x at hh
    refine hh.symm.trans (congrArg T ?_)
    funext j
    by_cases hj : j = l
    · subst j; simp only [Function.update_self]
    · simp only [Function.update_of_ne hj, vals]
  have hin (l : Fin (k + 3)) :
      g.inner x (K k (Function.update Y l (B P (Y l))) x) (z x) =
        ∑ u, ∑ v, a x u v *
          ((∑ i, ∑ j, a x i j * rho i j P (Y l) (E v) x) *
            low k (Fin.snoc (Function.update Y l (E u)) z) x) := by
    rw [hup l _ (hB l)]
    nth_rw 1 [hrec (B P (Y l) x)]
    rw [T.map_update_sum]
    simp only [T.map_update_sum, T.map_update_smul, map_sum, map_smul,
      sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [hpair P (Y l) (E v) hP (hY l) (hE v), hlow, hup l _ (hE u)]
    ac_rfl
  have hfour (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
      (∑ u, ∑ v, ∑ i, ∑ j, f i j u v) = ∑ i, ∑ j, ∑ u, ∑ v, f i j u v := by
    conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  have hfive (f : Fin (k + 3) → Fin n → Fin n → Fin n → Fin n → ℝ) :
      (∑ l, ∑ u, ∑ v, ∑ i, ∑ j, f l i j u v) =
        ∑ i, ∑ j, ∑ u, ∑ v, ∑ l, f l i j u v := by
    conv_lhs => arg 2; ext l; rw [hfour]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
  change g.inner x (B P (K k Y) x - ∑ l, K k (Function.update Y l (B P (Y l))) x) (z x) =
    ∑ i, ∑ j, ∑ u, ∑ v, (a x i j * a x u v) *
      (rho i j P (E u) z x * low k (Fin.snoc Y (E v)) x -
        ∑ l, rho i j P (Y l) (E v) x *
          low k (Fin.snoc (Function.update Y l (E u)) z) x)
  rw [map_sub, sub_apply, map_sum, sum_apply, hout]
  simp only [hin, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  apply congrArg₂ (fun A B : ℝ => A - B)
  · rw [hfour]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ac_rfl
  · rw [hfive]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro l _
    ac_rfl

end PoincareConjecture.Proofs.M03

section CollectedSuccessorEvaluations

set_option maxHeartbeats 4000000

namespace PoincareConjecture.Proofs.M03.CurvatureResidualPattern

theorem sum_spatialPatterns_evaluate {ι V : Type*} [Fintype ι]
    (k : ℕ) (a : ι → ι → ℝ)
    (low : (m : ℕ) → (Fin (m + 4) → V) → ℝ)
    (E : ι → V) (P : V) (Z : Fin (k + 3) → V) (z : V) :
    ((spatialPatterns k).map (fun r =>
      evaluate r a low E (Fin.cons P (Fin.snoc Z z)))).sum =
      ∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 0 ![P, E (γ 0), E (γ 2), z] *
            low (k + 1) (Fin.cons (E (γ 1)) (Fin.snoc Z (E (γ 3)))) -
          low 0 ![P, E (γ 0), E (γ 1), E (γ 3)] *
            low (k + 1) (Fin.cons (E (γ 2)) (Fin.snoc Z z)) -
          (∑ l, low 0 ![P, E (γ 0), Z l, E (γ 3)] *
            low (k + 1) (Fin.cons (E (γ 1))
              (Fin.snoc (Function.update Z l (E (γ 2))) z))) +
          low 1 ![E (γ 0), P, E (γ 1), E (γ 2), z] *
            low k (Fin.snoc Z (E (γ 3))) +
          low 0 ![P, E (γ 1), E (γ 2), z] *
            low (k + 1) (Fin.cons (E (γ 0)) (Fin.snoc Z (E (γ 3)))) -
          (∑ l, low 0 ![P, E (γ 1), Z l, E (γ 3)] *
            low (k + 1) (Fin.cons (E (γ 0))
              (Fin.snoc (Function.update Z l (E (γ 2))) z))) -
          ∑ l, low 1 ![E (γ 0), P, E (γ 1), Z l, E (γ 3)] *
            low k (Fin.snoc (Function.update Z l (E (γ 2))) z)) := by
  classical
  rw [sum_spatialPatterns]
  simp only [evaluate_co1, evaluate_co2, evaluate_co3, evaluate_co4,
    evaluate_co5, evaluate_co6, evaluate_co7]
  have hswap (f : Fin (k + 3) → (Fin 4 → ι) → ℝ) :
      (∑ l, ∑ γ, f l γ) = ∑ γ, ∑ l, f l γ := Finset.sum_comm
  simp only [mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, hswap, mul_assoc]
  ring

theorem sum_connectionPatterns_evaluate {ι V : Type*} [Fintype ι]
    (k : ℕ) (a : ι → ι → ℝ)
    (low : (m : ℕ) → (Fin (m + 4) → V) → ℝ)
    (E : ι → V) (P : V) (Z : Fin (k + 3) → V) (z : V) :
    let rho := fun (γ : Fin 4 → ι) (A Q w : V) =>
      -low 1 ![A, E (γ 0), Q, w, E (γ 1)] -
        low 1 ![Q, E (γ 0), w, A, E (γ 1)] +
        low 1 ![w, E (γ 0), A, Q, E (γ 1)]
    ((connectionPatterns k).map (fun r =>
      evaluate r a low E (Fin.cons P (Fin.snoc Z z)))).sum =
      ∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (rho γ P (E (γ 2)) z * low k (Fin.snoc Z (E (γ 3))) -
          ∑ l, rho γ P (Z l) (E (γ 3)) *
            low k (Fin.snoc (Function.update Z l (E (γ 2))) z)) := by
  classical
  dsimp only
  rw [sum_connectionPatterns]
  simp only [evaluate_bOut1, evaluate_bOut2, evaluate_bOut3,
    evaluate_bIn1, evaluate_bIn2, evaluate_bIn3]
  have hswap (f : Fin (k + 3) → (Fin 4 → ι) → ℝ) :
      (∑ l, ∑ γ, f l γ) = ∑ γ, ∑ l, f l γ := Finset.sum_comm
  simp only [sub_mul, add_mul, neg_mul, mul_add, mul_sub, mul_neg,
    Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, hswap, mul_assoc]
  ring

end PoincareConjecture.Proofs.M03.CurvatureResidualPattern

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace CurvatureResidualPattern

noncomputable def residualPatterns :
    (k : ℕ) → List (CurvatureResidualPattern k)
  | 0 => [basePattern1, basePattern2, basePattern3, basePattern4,
      basePattern5, basePattern6, basePattern7]
  | k + 1 => nextPatterns k (residualPatterns k)

end CurvatureResidualPattern

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ricciFlow_iteratedCurvature_lowered_residual_patterns
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) (k : ℕ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let g := F.metric t
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
    let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (K t r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
    ∀ (X : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y),
      (∀ j, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X j)) e.baseSet) →
      ∀ {x : M}, x ∈ e.baseSet →
      g.inner x (deriv (fun s => K s k (Fin.init X) x) t -
        ∑ i, ∑ j, a x i j • K t (k + 2)
          (Fin.cons (E i) (Fin.cons (E j) (Fin.init X))) x)
          (X (Fin.last (k + 3)) x) =
        ((CurvatureResidualPattern.residualPatterns k).map (fun r =>
          CurvatureResidualPattern.evaluate r (a x) (fun m Z => low m Z x) E X)).sum := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  dsimp only
  let g := F.metric t
  let D := F.connection t
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
    x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
  let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (K t r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
  let lowErr := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (deriv (fun s => K s r (Fin.init Z) y) t -
      ∑ i, ∑ j, a y i j • K t (r + 2)
        (Fin.cons (E i) (Fin.cons (E j) (Fin.init Z))) y) (Z (Fin.last (r + 3)) y)
  let ev := fun (r : ℕ) (p : CurvatureResidualPattern r)
    (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    CurvatureResidualPattern.evaluate p (a y) (fun m W => low m W y) E Z
  let total := fun (r : ℕ) (ps : List (CurvatureResidualPattern r))
    (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    (ps.map (fun p => ev r p Z y)).sum
  let S := fun Q : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Q) e.baseSet
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection Q y (P y)
  change ∀ X, (∀ j, S (X j)) → ∀ {x}, x ∈ e.baseSet →
    lowErr k X x = total k (CurvatureResidualPattern.residualPatterns k) X x
  induction k with
  | zero =>
    intro X hX x hx
    have h0 := ricciFlow_iteratedCurvature_lowered_residual_zero_patterns F ht x0 X hX hx
    change lowErr 0 X x =
      ev 0 CurvatureResidualPattern.basePattern1 X x +
      ev 0 CurvatureResidualPattern.basePattern2 X x +
      ev 0 CurvatureResidualPattern.basePattern3 X x +
      ev 0 CurvatureResidualPattern.basePattern4 X x +
      ev 0 CurvatureResidualPattern.basePattern5 X x +
      ev 0 CurvatureResidualPattern.basePattern6 X x +
      ev 0 CurvatureResidualPattern.basePattern7 X x at h0
    simpa only [total, CurvatureResidualPattern.residualPatterns,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      add_assoc] using h0
  | succ k ih =>
    intro W hW x hx
    let P := W 0
    let X := Fin.tail W
    have hP : S P := hW 0
    have hX (j : Fin (k + 4)) : S (X j) := hW j.succ
    have hWcons : Fin.cons P X = W := Fin.cons_self_tail W
    rw [← hWcons]
    let ps := CurvatureResidualPattern.residualPatterns k
    have hpoint {y : M} (hy : y ∈ e.baseSet) :
        lowErr k X y = total k ps X y := ih X hX hy
    have hgerm : lowErr k X =ᶠ[𝓝 x] total k ps X :=
      Filter.eventuallyEq_of_mem (e.open_baseSet.mem_nhds hx) (fun _ hy => hpoint hy)
    have hderiv : mvfderiv (𝓡 n) (lowErr k X) x (P x) =
        mvfderiv (𝓡 n) (total k ps X) x (P x) := by
      exact congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (P x)) hgerm.mfderiv_eq
    have hN (l : Fin (k + 4)) : S (N P (X l)) :=
      D.contMDiffOn_connection_apply e.open_baseSet P (X l) hP (hX l)
    have hupdate (l : Fin (k + 4)) :
        lowErr k (Function.update X l (N P (X l))) x =
          total k ps (Function.update X l (N P (X l))) x := by
      apply ih _ _ hx
      intro j
      by_cases h : j = l
      · subst j
        simpa only [Function.update_self] using hN l
      · simpa only [Function.update_of_ne h] using hX j
    have hlist := CurvatureResidualPattern.covariant_derivative_evaluate_list
      D ps x0 P X hP hX hx
    change mvfderiv (𝓡 n) (total k ps X) x (P x) -
      (∑ l, total k ps (Function.update X l (N P (X l))) x) =
      total (k + 1) (CurvatureResidualPattern.derivativePatterns ps) (Fin.cons P X) x at hlist
    let Y := Fin.init X
    let z := X (Fin.last (k + 3))
    have hY (l : Fin (k + 3)) : S (Y l) := hX l.castSucc
    have hz : S z := hX (Fin.last (k + 3))
    have hsnoc : Fin.snoc Y z = X := Fin.snoc_init_self X
    let B := fun (A Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      deriv (fun s => (F.connection s).connection Q y (A y)) t
    let R := fun (A Q Z : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.curvatureOnFields A Q Z y
    let Co := fun (A C : (y : M) → TangentSpace (𝓡 n) y) y =>
      R P A (K t (k + 1) (Fin.cons C Y)) y -
      K t (k + 1) (Fin.cons (R P A C) Y) y -
      (∑ l, K t (k + 1) (Fin.cons C (Function.update Y l (R P A (Y l)))) y) +
      K t 1 ![A, P, C, K t k Y] y +
      R P C (K t (k + 1) (Fin.cons A Y)) y -
      (∑ l, K t (k + 1) (Fin.cons A (Function.update Y l (R P C (Y l)))) y) -
      ∑ l, K t k (Function.update Y l (K t 1 ![A, P, C, Y l])) y
    have hB := ricciFlow_iteratedCurvature_connection_correction_two_contractions
      F ht x0 k P z Y hP hz hY hx
    have hBev := CurvatureResidualPattern.sum_connectionPatterns_evaluate
      k (a x) (fun m Z => low m Z x) E P Y z
    dsimp only at hBev
    rw [CurvatureResidualPattern.sum_fin_four] at hBev
    rw [hsnoc] at hBev
    have hBlist : g.inner x
        (B P (K t k Y) x - ∑ l, K t k (Function.update Y l (B P (Y l))) x) (z x) =
        total (k + 1) (CurvatureResidualPattern.connectionPatterns k) (Fin.cons P X) x :=
      hB.trans hBev.symm
    have hCo := curvature_iterated_spatial_correction_two_contractions
      D x0 k P Y z hP hY hz hx
    have hCoev := CurvatureResidualPattern.sum_spatialPatterns_evaluate
      k (a x) (fun m Z => low m Z x) E P Y z
    rw [CurvatureResidualPattern.sum_fin_four] at hCoev
    conv_lhs at hCoev => rw [hsnoc]
    simp only [Fin.cons_snoc_eq_snoc_cons] at hCoev
    have hColist : g.inner x (∑ i, ∑ j, a x i j • Co (E i) (E j) x) (z x) =
        total (k + 1) (CurvatureResidualPattern.spatialPatterns k) (Fin.cons P X) x :=
      hCo.trans hCoev.symm
    have hs := ricciFlow_iteratedCurvature_lowered_residual_succ
      F ht x0 k hx P X hP hX
    change lowErr (k + 1) (Fin.cons P X) x =
      mvfderiv (𝓡 n) (lowErr k X) x (P x) -
        (∑ l, lowErr k (Function.update X l (N P (X l))) x) +
      g.inner x ((B P (K t k Y) x -
        ∑ l, K t k (Function.update Y l (B P (Y l))) x) +
        ∑ i, ∑ j, a x i j • Co (E i) (E j) x) (z x) at hs
    rw [hs, hderiv]
    simp only [hupdate]
    rw [hlist, map_add, add_apply, hBlist, hColist]
    simp only [CurvatureResidualPattern.residualPatterns,
      CurvatureResidualPattern.nextPatterns, CurvatureResidualPattern.correctionPatterns,
      total, List.map_append, List.sum_append]
    rfl

end PoincareConjecture.Proofs.M03

end CollectedSuccessorEvaluations

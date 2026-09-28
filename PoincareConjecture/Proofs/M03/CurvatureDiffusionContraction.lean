import PoincareConjecture.Proofs.M03.CurvaturePairExchange
import PoincareConjecture.Proofs.M03.CurvatureSecondBianchi
import PoincareConjecture.Proofs.M03.CurvatureJoint
import PoincareConjecture.Proofs.M03.MetricInverse
import PoincareConjecture.Proofs.M03.CurvatureTimeVariation
import PoincareConjecture.Proofs.M03.CurvatureDerivativeCommutator










set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureOnFields_hessian_bianchi_pairing
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (P L X Y Z W : (x : M) → TangentSpace (𝓡 n) x)
    (hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hL : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% L) U)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (hW : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U)
    {x : M} (hx : x ∈ U) :
    let dR := fun
        (A B C E : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection (fun z => D.curvatureOnFields B C E z) y (A y) -
        D.curvatureOnFields
          (fun z => D.connection B z (A z)) C E y -
        D.curvatureOnFields B
          (fun z => D.connection C z (A z)) E y -
        D.curvatureOnFields B C
          (fun z => D.connection E z (A z)) y
    let ddR := fun
        (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection (fun z => dR Q A B C z) y (P y) -
        dR (fun z => D.connection Q z (P z)) A B C y -
        dR Q (fun z => D.connection A z (P z)) B C y -
        dR Q A (fun z => D.connection B z (P z)) C y -
        dR Q A B (fun z => D.connection C z (P z)) y
    g.inner x (ddR P L X Y Z x) (W x) -
      g.inner x (ddR P Z X Y L x) (W x) =
        g.inner x (ddR P W X Y Z x) (L x) := by
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
  let K := fun (A B C E : (y : M) → TangentSpace (𝓡 n) y) y =>
    N A (R B C E) y - R (N A B) C E y -
      R B (N A C) E y - R B C (N A E) y
  let H := fun (A B C E F : (y : M) → TangentSpace (𝓡 n) y) y =>
    N A (K B C E F) y - K (N A B) C E F y -
      K B (N A C) E F y - K B C (N A E) F y - K B C E (N A F) y
  let T := fun (A B C E : (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (R A B C y) (E y)
  let J := fun (A B C E F : (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (K A B C E y) (F y)
  let d := fun (A : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
    mvfderiv (𝓡 n) f y (A y)
  let S := fun A : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U
  have hmd (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A)
      {y : M} (hy : y ∈ U) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) y :=
    (hA.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : S (N A B) :=
    D.contMDiffOn_connection_apply hU A B hA hB
  have hR (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (R A B C) := by
    have hbr : S (VectorField.mlieBracket (𝓡 n) A B) := by
      intro y hy
      exact ((hA.contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
        (hB.contMDiffAt (hU.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hN A _ hA (hN B C hB hC)).sub_section
      (hN B _ hB (hN A C hA hC))).sub_section (hN _ C hbr hC)
  have hK (A B C E : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hE : S E) : S (K A B C E) :=
    (((hN A _ hA (hR B C E hB hC hE)).sub_section
      (hR _ C E (hN A B hA hB) hC hE)).sub_section
      (hR B _ E hB (hN A C hA hC) hE)).sub_section
      (hR B C _ hB hC (hN A E hA hE))
  have hJsmooth (A B C E F : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hE : S E) (hF : S F) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (J A B C E F) U :=
    (hK A B C E hA hB hC hE).inner_bundle hF
  have hJmd (A B C E F : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hE : S E) (hF : S F) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (J A B C E F) x :=
    ((hJsmooth A B C E F hA hB hC hE hF).contMDiffAt
      (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdcongr (A : (y : M) → TangentSpace (𝓡 n) y) (f f' : M → ℝ)
      (heq : ∀ y ∈ U, f y = f' y) {y : M} (hy : y ∈ U) :
      d A f y = d A f' y := by
    have hg : f =ᶠ[𝓝 y] f' := Filter.eventuallyEq_of_mem (hU.mem_nhds hy) heq
    dsimp only [d, mvfderiv]
    rw [hg.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)), hg.eq_of_nhds]
  have hTswap₁ (A B C E : (y : M) → TangentSpace (𝓡 n) y) (y : M) :
      T A B C E y = -T B A C E y := by
    simpa only [T, R, map_neg, neg_apply] using
      congrArg (fun v => g.inner y v (E y)) (curvatureOnFields_swap D A B C y)
  have hTswap₂ (A B C E : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hE : S E)
      {y : M} (hy : y ∈ U) : T A B C E y = -T A B E C y := by
    have h := curvatureOnFields_pair_skew D hU A B C E hA hB hC hE hy
    rw [g.symm y (C y) (D.curvatureOnFields A B E y)] at h
    exact h
  have hTbridge (A B C E : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) {y : M} (hy : y ∈ U) :
      D.curvatureTensor y (A y) (B y) (E y) (C y) = T A B C E y := by
    change g.inner y (D.curvature y (A y) (B y) (C y)) (E y) = _
    rw [curvature_eq_curvatureOnFields D hU A B C hA hB hC hy]
  have hTpair (A B C E : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hE : S E)
      {y : M} (hy : y ∈ U) : T A B C E y = T C E A B y := by
    have h := curvatureTensor_pair_exchange D y (A y) (B y) (E y) (C y)
    rw [hTbridge A B C E hA hB hC hy,
      hTbridge E C B A hE hC hB hy,
      hTswap₁ E C B A y, hTswap₂ C E B A hC hE hB hA hy, neg_neg] at h
    exact h
  have hJformula (A B C E F : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) (hC : S C) (hE : S E) (hF : S F)
      {y : M} (hy : y ∈ U) :
      J A B C E F y = d A (T B C E F) y -
        T (N A B) C E F y - T B (N A C) E F y -
        T B C (N A E) F y - T B C E (N A F) y := by
    dsimp only [J, K, T, d]
    rw [D.mvfderiv_inner A (R B C E) F (hmd _ (hR B C E hB hC hE) hy)
      (hmd F hF hy)]
    simp only [map_sub, sub_apply]
    dsimp only [N]
    ring
  have hJswap (A B C E F : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hE : S E) (hF : S F)
      {y : M} (hy : y ∈ U) : J A B C E F y = -J A B C F E y := by
    have hd : d A (T B C E F) y = -d A (T B C F E) y := by
      calc
        _ = d A (fun z => -T B C F E z) y :=
          hdcongr A _ _ (fun z hz => hTswap₂ B C E F hB hC hE hF hz) hy
        _ = _ := by simp only [d, mvfderiv_fun_neg, neg_apply]
    rw [hJformula A B C E F hB hC hE hF hy,
      hJformula A B C F E hB hC hF hE hy, hd,
      hTswap₂ (N A B) C E F (hN A B hA hB) hC hE hF hy,
      hTswap₂ B (N A C) E F hB (hN A C hA hC) hE hF hy,
      hTswap₂ B C (N A E) F hB hC (hN A E hA hE) hF hy,
      hTswap₂ B C E (N A F) hB hC hE (hN A F hA hF) hy]
    ring
  have hJpair (A B C E F : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hE : S E) (hF : S F)
      {y : M} (hy : y ∈ U) : J A B C E F y = J A E F B C y := by
    have hd : d A (T B C E F) y = d A (T E F B C) y :=
      hdcongr A _ _ (fun z hz => hTpair B C E F hB hC hE hF hz) hy
    rw [hJformula A B C E F hB hC hE hF hy,
      hJformula A E F B C hE hF hB hC hy, hd,
      hTpair (N A B) C E F (hN A B hA hB) hC hE hF hy,
      hTpair B (N A C) E F hB (hN A C hA hC) hE hF hy,
      hTpair B C (N A E) F hB hC (hN A E hA hE) hF hy,
      hTpair B C E (N A F) hB hC hE (hN A F hA hF) hy]
    ring
  let F := fun (A B C E G : (y : M) → TangentSpace (𝓡 n) y) y =>
    J A B C E G y - J E B C A G y - J G B C E A y
  have hF (A B C E G : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hE : S E) (hG : S G)
      {y : M} (hy : y ∈ U) : F A B C E G y = 0 := by
    have hb := congrArg (fun v => g.inner y v (C y))
      (curvatureOnFields_second_bianchi D hU A E G B hA hE hG hB hy)
    change g.inner y (K A E G B y + K E G A B y + K G A E B y) (C y) =
      g.inner y 0 (C y) at hb
    simp only [map_add, add_apply, map_zero, zero_apply] at hb
    change J A E G B C y + J E G A B C y + J G A E B C y = 0 at hb
    rw [hJpair A E G B C hA hE hG hB hC hy,
      hJpair E G A B C hE hG hA hB hC hy,
      hJpair G A E B C hG hA hE hB hC hy,
      hJswap E B C G A hE hB hC hG hA hy,
      hJswap G B C A E hG hB hC hA hE hy] at hb
    simpa only [F, sub_eq_add_neg] using hb
  have hJderiv (A B C E F G : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) (hC : S C) (hE : S E) (hF : S F) (hG : S G) :
      d A (J B C E F G) x = g.inner x (H A B C E F x) (G x) +
        J (N A B) C E F G x + J B (N A C) E F G x +
        J B C (N A E) F G x + J B C E (N A F) G x +
        J B C E F (N A G) x := by
    dsimp only [d, J, H]
    rw [D.mvfderiv_inner A (K B C E F) G
      (hmd _ (hK B C E F hB hC hE hF) hx) (hmd G hG hx)]
    simp only [map_sub, sub_apply]
    dsimp only [N]
    ring
  have hFD : d P (F L X Y Z W) x = 0 := by
    have heq := hdcongr P (F L X Y Z W) (fun _ => 0)
      (fun y hy => hF L X Y Z W hL hX hY hZ hW hy) hx
    simpa only [d, mvfderiv_const, zero_apply] using heq
  have hj₁ := hJmd L X Y Z W hL hX hY hZ hW
  have hj₂ := hJmd Z X Y L W hZ hX hY hL hW
  have hj₃ := hJmd W X Y Z L hW hX hY hZ hL
  change mvfderiv (𝓡 n)
    (J L X Y Z W - J Z X Y L W - J W X Y Z L) x (P x) = 0 at hFD
  rw [mvfderiv_sub (hj₁.sub hj₂) hj₃, sub_apply,
    mvfderiv_sub hj₁ hj₂, sub_apply] at hFD
  change d P (J L X Y Z W) x - d P (J Z X Y L W) x -
    d P (J W X Y Z L) x = 0 at hFD
  rw [hJderiv P L X Y Z W hL hX hY hZ hW,
    hJderiv P Z X Y L W hZ hX hY hL hW,
    hJderiv P W X Y Z L hW hX hY hZ hL] at hFD
  have hFL := hF (N P L) X Y Z W (hN P L hP hL) hX hY hZ hW hx
  have hFX := hF L (N P X) Y Z W hL (hN P X hP hX) hY hZ hW hx
  have hFY := hF L X (N P Y) Z W hL hX (hN P Y hP hY) hZ hW hx
  have hFZ := hF L X Y (N P Z) W hL hX hY (hN P Z hP hZ) hW hx
  have hFW := hF L X Y Z (N P W) hL hX hY hZ (hN P W hP hW) hx
  dsimp only [F] at hFL hFX hFY hFZ hFW
  change g.inner x (H P L X Y Z x) (W x) - g.inner x (H P Z X Y L x) (W x) =
    g.inner x (H P W X Y Z x) (L x)
  linarith only [hFD, hFL, hFX, hFY, hFZ, hFW]

set_option maxHeartbeats 2400000 in
theorem curvatureOnFields_iteratedCovariantDerivative_trace_derivative
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) (k : ℕ) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
    let K := curvatureOnFields_iteratedCovariantDerivative D
    let L := fun (X : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
      ∑ i, ∑ j, a y i j • K (k + 2) (Fin.cons (E i) (Fin.cons (E j) X)) y
    ∀ {x : M}, x ∈ e.baseSet →
      ∀ (P : (y : M) → TangentSpace (𝓡 n) y)
        (X : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) e.baseSet →
      (∀ l, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X l)) e.baseSet) →
      N P (L X) x - ∑ l, L (Function.update X l (N P (X l))) x =
        ∑ i, ∑ j, a x i j • K (k + 3) (Fin.cons P (Fin.cons (E i) (Fin.cons (E j) X))) x := by
  classical
  dsimp only
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
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
  let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y (g.inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
  let K := curvatureOnFields_iteratedCovariantDerivative D
  let Gamma := fun y i j p => theta p y (N (E i) (E j) y)
  let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
    mvfderiv (𝓡 n) f y (P y)
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) e.baseSet
  let C := fun f : M → ℝ => ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet
  have hmd (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W)
      {y : M} (hy : y ∈ e.baseSet) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% W) y :=
    (hW.contMDiffAt (e.open_baseSet.mem_nhds hy)).mdifferentiableAt (by simp)
  have hcmd (f : M → ℝ) (hf : C f) {y : M} (hy : y ∈ e.baseSet) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f y :=
    (hf.contMDiffAt (e.open_baseSet.mem_nhds hy)).mdifferentiableAt (by simp)
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b i
  have hN (P Q : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) : S (N P Q) :=
    D.contMDiffOn_connection_apply e.open_baseSet P Q hP hQ
  have hK (r : ℕ) (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) : S (K r Z) :=
    contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D e.open_baseSet r Z hZ
  have hcons {r : ℕ} (A : (y : M) → TangentSpace (𝓡 n) y)
      (Z : Fin r → (y : M) → TangentSpace (𝓡 n) y) (hA : S A) (hZ : ∀ j, S (Z j)) :
      ∀ j, S ((Fin.cons A Z : Fin (r + 1) → (y : M) → TangentSpace (𝓡 n) y) j) := by
    intro j
    refine Fin.cases ?_ (fun l => ?_) j
    · simpa only [Fin.cons_zero] using hA
    · simpa only [Fin.cons_succ] using hZ l
  have hup {r : ℕ} (Z : Fin r → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) (i : Fin r)
      (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) : ∀ j, S (Function.update Z i A j) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hA
    · simpa only [Function.update_of_ne hji] using hZ j
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
        -(∑ p, (Gamma x i p j * a x p k + Gamma x i p k * a x j p)) := by
    have hxc : x ∈ c.source := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using hx
    have hh := metric_inverse_covariant_derivative_coordinates D x0 (c x) (c.map_source hxc) i j k
    have he := hchart (fun y => a y j k) (ha j k) (c.map_source hxc) i
    rw [c.left_inv hxc] at hh he
    exact he.trans hh
  let coeff := fun (i : Fin n) (W : (y : M) → TangentSpace (𝓡 n) y) y =>
    theta i y (W y)
  have hrec (W : (y : M) → TangentSpace (𝓡 n) y)
      {y : M} (hy : y ∈ e.baseSet) : W y = ∑ i, coeff i W y • E i y :=
    e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) hy
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hnsum {y : M} (hy : y ∈ e.baseSet)
      (W : Fin n → (y : M) → TangentSpace (𝓡 n) y)
      (hW : ∀ i, S (W i)) (v : TangentSpace (𝓡 n) y) :
      D.connection (fun y => ∑ i, W i y) y v = ∑ i, D.connection (W i) y v := by
    have aux (s : Finset (Fin n)) :
        D.connection (fun y => ∑ i ∈ s, W i y) y v =
          ∑ i ∈ s, D.connection (W i) y v := by
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        change D.connection 0 y v = 0
        rw [hc.zero, zero_apply]
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        change D.connection (W i + fun y => ∑ j ∈ s, W j y) y v = _
        rw [hc.add (hmd _ (hW i) hy)
          (MDifferentiableAt.sum_section fun j _ => hmd _ (hW j) hy), add_apply, ih]
    exact aux Finset.univ
  let GP := fun (P : (y : M) → TangentSpace (𝓡 n) y) y i p => coeff p (N P (E i)) y
  have hGP {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (i p : Fin n) :
      GP P x i p = ∑ k, coeff k P x * Gamma x k i p := by
    have hh := congrArg (fun v => theta p x (D.connection (E i) x v)) (hrec P hx)
    simpa only [GP, coeff, N, Gamma, map_sum, map_smul, smul_eq_mul] using hh
  have hdir {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) :
      d P f x = ∑ k, coeff k P x * d (E k) f x := by
    have hh := congrArg (mvfderiv (𝓡 n) f x) (hrec P hx)
    simpa only [d, map_sum, map_smul, smul_eq_mul] using hh
  have hdaP {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y) (i j : Fin n) :
      d P (fun y => a y i j) x =
        -(∑ p, (GP P x p i * a x p j + GP P x p j * a x i p)) := by
    rw [hdir hx P]
    simp_rw [hda hx, hGP hx P]
    simp only [mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul,
      mul_add, Finset.sum_add_distrib]
    congr 1
    congr 1
    all_goals
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro k _
      ring
  let Tr := fun (T : ((y : M) → TangentSpace (𝓡 n) y) →
      ((y : M) → TangentSpace (𝓡 n) y) → (y : M) → TangentSpace (𝓡 n) y) y =>
    ∑ i, ∑ j, a y i j • T (E i) (E j) y
  have htrace {x : M} (hx : x ∈ e.baseSet)
      (P : (y : M) → TangentSpace (𝓡 n) y)
      (T : ((y : M) → TangentSpace (𝓡 n) y) →
        ((y : M) → TangentSpace (𝓡 n) y) → (y : M) → TangentSpace (𝓡 n) y)
      (hT : ∀ i j, S (T (E i) (E j)))
      (hL : ∀ i j, T (N P (E i)) (E j) x = ∑ p, GP P x i p • T (E p) (E j) x)
      (hR : ∀ i j, T (E i) (N P (E j)) x = ∑ p, GP P x j p • T (E i) (E p) x) :
      N P (Tr T) x = ∑ i, ∑ j, a x i j •
        (N P (T (E i) (E j)) x - T (N P (E i)) (E j) x - T (E i) (N P (E j)) x) := by
    have hd : N P (Tr T) x = ∑ i, ∑ j,
        (a x i j • N P (T (E i) (E j)) x +
          d P (fun y => a y i j) x • T (E i) (E j) x) := by
      dsimp only [N, Tr]
      rw [hnsum hx (fun i y => ∑ j, a y i j • T (E i) (E j) y)
        (fun i => ContMDiffOn.sum_section fun j _ => (ha i j).smul_section (hT i j)) (P x)]
      apply Finset.sum_congr rfl
      intro i _
      rw [hnsum hx (fun j y => a y i j • T (E i) (E j) y)
        (fun j => (ha i j).smul_section (hT i j)) (P x)]
      apply Finset.sum_congr rfl
      intro j _
      simpa only [d, Pi.smul_def', add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply] using
        congrArg (fun L => L (P x)) (hc.leibniz (hmd _ (hT i j) hx) (hcmd _ (ha i j) hx))
    have hneg : (∑ i, ∑ j, d P (fun y => a y i j) x • T (E i) (E j) x) =
        -((∑ i, ∑ j, a x i j • T (N P (E i)) (E j) x) +
          ∑ i, ∑ j, a x i j • T (E i) (N P (E j)) x) := by
      simp_rw [hdaP hx P, hL, hR]
      simp only [neg_smul, Finset.sum_neg_distrib, Finset.sum_smul, add_smul,
        Finset.smul_sum, Finset.sum_add_distrib, mul_smul]
      congr 1
      congr 1
      · calc
          _ = ∑ j, ∑ i, ∑ p, GP P x p i • a x p j • T (E i) (E j) x :=
            Finset.sum_comm
          _ = ∑ j, ∑ p, ∑ i, GP P x p i • a x p j • T (E i) (E j) x := by
            apply Finset.sum_congr rfl
            intro j _
            exact Finset.sum_comm
          _ = ∑ p, ∑ j, ∑ i, GP P x p i • a x p j • T (E i) (E j) x :=
            Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            exact smul_comm _ _ _
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro j _
        exact smul_comm _ _ _
    rw [hd]
    simp only [Finset.sum_add_distrib]
    rw [hneg]
    simp only [smul_sub, Finset.sum_sub_distrib]
    module
  intro x hx P X hP hX
  let L := fun (Z : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y) =>
    Tr (fun A B => K (k + 2) (Fin.cons A (Fin.cons B Z)))
  change N P (L X) x - ∑ l, L (Function.update X l (N P (X l))) x =
    ∑ i, ∑ j, a x i j • K (k + 3) (Fin.cons P (Fin.cons (E i) (Fin.cons (E j) X))) x
  have hslot (r : ℕ) (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) (l : Fin (r + 3))
      (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) :
      K r (Function.update Z l A) x =
        ∑ p, coeff p A x • K r (Function.update Z l (E p)) x := by
    obtain ⟨T, hT⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D r x
    have hev (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
        K r (Function.update Z l W) x =
          T (Function.update (fun j => Z j x) l (W x)) := by
      change curvatureOnFields_iteratedCovariantDerivative D r (Function.update Z l W) x = _
      rw [← hT e.open_baseSet _ (hup Z hZ l W hW) hx]
      congr 1
      funext j
      by_cases hjl : j = l
      · subst j
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hjl]
    rw [hev A hA, hrec A hx, T.map_update_sum]
    simp only [T.map_update_smul]
    exact Finset.sum_congr rfl fun p _ => congrArg (fun v => coeff p A x • v) (hev (E p) (hE p)).symm
  have hleft (i j : Fin n) :
      K (k + 2) (Fin.cons (N P (E i)) (Fin.cons (E j) X)) x =
        ∑ p, GP P x i p • K (k + 2) (Fin.cons (E p) (Fin.cons (E j) X)) x := by
    simpa only [Fin.update_cons_zero] using hslot (k + 2)
      (Fin.cons (E i) (Fin.cons (E j) X)) (hcons _ _ (hE i) (hcons _ _ (hE j) hX))
      0 (N P (E i)) (hN P (E i) hP (hE i))
  have hright (i j : Fin n) :
      K (k + 2) (Fin.cons (E i) (Fin.cons (N P (E j)) X)) x =
        ∑ p, GP P x j p • K (k + 2) (Fin.cons (E i) (Fin.cons (E p) X)) x := by
    simpa only [← Fin.cons_update, Fin.update_cons_zero] using hslot (k + 2)
      (Fin.cons (E i) (Fin.cons (E j) X)) (hcons _ _ (hE i) (hcons _ _ (hE j) hX))
      (0 : Fin (k + 4)).succ (N P (E j)) (hN P (E j) hP (hE j))
  have hbase := htrace hx P (fun A B => K (k + 2) (Fin.cons A (Fin.cons B X)))
    (fun i j => hK (k + 2) _ (hcons _ _ (hE i) (hcons _ _ (hE j) hX)))
    hleft hright
  have hstep (r : ℕ) (A : (y : M) → TangentSpace (𝓡 n) y)
      (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) :
      K (r + 1) (Fin.cons A Z) x = N A (K r Z) x -
        ∑ l, K r (Function.update Z l (N A (Z l))) x := by
    rfl
  have hsucc (i j : Fin n) :
      K (k + 3) (Fin.cons P (Fin.cons (E i) (Fin.cons (E j) X))) x =
        N P (K (k + 2) (Fin.cons (E i) (Fin.cons (E j) X))) x -
        K (k + 2) (Fin.cons (N P (E i)) (Fin.cons (E j) X)) x -
        K (k + 2) (Fin.cons (E i) (Fin.cons (N P (E j)) X)) x -
        ∑ l, K (k + 2) (Fin.cons (E i) (Fin.cons (E j)
          (Function.update X l (N P (X l))))) x := by
    rw [hstep (k + 2) P (Fin.cons (E i) (Fin.cons (E j) X))]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update]
    abel
  have hsum :
      (∑ l, L (Function.update X l (N P (X l))) x) =
        ∑ i, ∑ j, ∑ l, a x i j • K (k + 2)
          (Fin.cons (E i) (Fin.cons (E j) (Function.update X l (N P (X l))))) x := by
    dsimp only [L, Tr]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  rw [hsum]
  change N P (Tr (fun A B => K (k + 2) (Fin.cons A (Fin.cons B X)))) x - _ = _
  rw [hbase]
  simp only [hsucc, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]

set_option maxHeartbeats 2400000 in

theorem ricciFlow_iteratedCurvature_residual_succ
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) (k : ℕ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y ((F.metric t).inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection t).connection Q y (P y)
    let R := fun (P Q Z : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection t).curvatureOnFields P Q Z y
    let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
    let dotK := fun r (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
      deriv (fun s => K s r Z y) t
    let L := fun r (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
      ∑ i, ∑ j, a y i j • K t (r + 2) (Fin.cons (E i) (Fin.cons (E j) Z)) y
    let Err := fun r Z y => dotK r Z y - L r Z y
    let B := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      deriv (fun s => (F.connection s).connection Q y (P y)) t
    let Co := fun (P A C : (y : M) → TangentSpace (𝓡 n) y)
      (X : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
      R P A (K t (k + 1) (Fin.cons C X)) y -
      K t (k + 1) (Fin.cons (R P A C) X) y -
      (∑ l, K t (k + 1) (Fin.cons C (Function.update X l (R P A (X l)))) y) +
      K t 1 ![A, P, C, K t k X] y +
      R P C (K t (k + 1) (Fin.cons A X)) y -
      (∑ l, K t (k + 1) (Fin.cons A (Function.update X l (R P C (X l)))) y) -
      ∑ l, K t k (Function.update X l (K t 1 ![A, P, C, X l])) y
    ∀ {x : M}, x ∈ e.baseSet →
      ∀ (P : (y : M) → TangentSpace (𝓡 n) y)
        (X : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) e.baseSet →
      (∀ l, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X l)) e.baseSet) →
      Err (k + 1) (Fin.cons P X) x =
        N P (Err k X) x - (∑ l, Err k (Function.update X l (N P (X l))) x) +
        B P (K t k X) x - (∑ l, K t k (Function.update X l (B P (X l))) x) +
        ∑ i, ∑ j, a x i j • Co P (E i) (E j) X x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y ((F.metric t).inner y)
  let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection t).connection Q y (P y)
  let R := fun (P Q Z : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection t).curvatureOnFields P Q Z y
  let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
  let dotK := fun r (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
    deriv (fun s => K s r Z y) t
  let L := fun r (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
    ∑ i, ∑ j, a y i j • K t (r + 2) (Fin.cons (E i) (Fin.cons (E j) Z)) y
  let Err := fun r Z y => dotK r Z y - L r Z y
  let B := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    deriv (fun s => (F.connection s).connection Q y (P y)) t
  let Co := fun (P A C : (y : M) → TangentSpace (𝓡 n) y)
    (X : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
    R P A (K t (k + 1) (Fin.cons C X)) y -
    K t (k + 1) (Fin.cons (R P A C) X) y -
    (∑ l, K t (k + 1) (Fin.cons C (Function.update X l (R P A (X l)))) y) +
    K t 1 ![A, P, C, K t k X] y +
    R P C (K t (k + 1) (Fin.cons A X)) y -
    (∑ l, K t (k + 1) (Fin.cons A (Function.update X l (R P C (X l)))) y) -
    ∑ l, K t k (Function.update X l (K t 1 ![A, P, C, X l])) y
  intro x hx P X hP hX
  change Err (k + 1) (Fin.cons P X) x =
    N P (Err k X) x - (∑ l, Err k (Function.update X l (N P (X l))) x) +
    B P (K t k X) x - (∑ l, K t k (Function.update X l (B P (X l))) x) +
    ∑ i, ∑ j, a x i j • Co P (E i) (E j) X x
  let S := fun Q : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Q) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ _ i
  have hcons {r : ℕ} (A : (y : M) → TangentSpace (𝓡 n) y)
      (Z : Fin r → (y : M) → TangentSpace (𝓡 n) y) (hA : S A) (hZ : ∀ l, S (Z l)) :
      ∀ l, S ((Fin.cons A Z : Fin (r + 1) → (y : M) → TangentSpace (𝓡 n) y) l) := by
    intro l
    refine Fin.cases ?_ (fun j => ?_) l
    · simpa only [Fin.cons_zero] using hA
    · simpa only [Fin.cons_succ] using hZ j
  have hco (i j : Fin n) :
      K t (k + 3) (Fin.cons P (Fin.cons (E i) (Fin.cons (E j) X))) x -
        K t (k + 3) (Fin.cons (E i) (Fin.cons (E j) (Fin.cons P X))) x =
        Co P (E i) (E j) X x := by
    have ho := curvatureOnFields_iteratedCovariantDerivative_outer_commutator
      (F.connection t) e.open_baseSet (k + 1) P (E i) (Fin.cons (E j) X)
      hP (hE i) (hcons _ _ (hE j) hX) hx
    have hi := curvatureOnFields_iteratedCovariantDerivative_inner_commutator
      (F.connection t) e.open_baseSet k (E i) P (E j) X (hE i) hP (hE j) hX hx
    rw [Fin.sum_univ_succ] at ho
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update] at ho
    dsimp only [Co, R, K]
    linear_combination (norm := module) ho + hi
  have htrace := curvatureOnFields_iteratedCovariantDerivative_trace_derivative
    (F.connection t) x0 k hx P X hP hX
  change N P (L k X) x - (∑ l, L k (Function.update X l (N P (X l))) x) =
    ∑ i, ∑ j, a x i j • K t (k + 3)
      (Fin.cons P (Fin.cons (E i) (Fin.cons (E j) X))) x at htrace
  have hcot :
      (∑ i, ∑ j, a x i j • K t (k + 3)
        (Fin.cons P (Fin.cons (E i) (Fin.cons (E j) X))) x) -
      L (k + 1) (Fin.cons P X) x = ∑ i, ∑ j, a x i j • Co P (E i) (E j) X x := by
    dsimp only [L]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← smul_sub, hco]
  have htime := (hasDerivAt_ricciFlow_iteratedCurvature_succ F ht e.open_baseSet
    k P X hP hX hx).deriv
  change dotK (k + 1) (Fin.cons P X) x =
    (N P (dotK k X) x - ∑ l, dotK k (Function.update X l (N P (X l))) x) +
    B P (K t k X) x - ∑ l, K t k (Function.update X l (B P (X l))) x at htime
  have hdot : S (dotK k X) := by
    have hf := contMDiffOn_family_curvatureOnFields_iteratedCovariantDerivative
      F.smooth F.connection e.open_baseSet k (fun l _ => X l)
      (fun l => (hX l).comp contMDiffOn_snd (fun _ hp => hp.2))
    exact (family_tangent_time_derivative (F.metric 0) e.open_baseSet
      (fun s y => K s k X y) hf ht).2
  have ha (i j : Fin n) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => a y i j) e.baseSet := by
    have hi := (contMDiffOn_family_metric_frame_inverse F.smooth x0).2.2
    have hs := hi.comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => (t, y)) e.baseSet from contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨interior_subset ht, hy⟩)
    exact (contMDiffOn_const (c := EuclideanSpace.proj i)).clm_apply
      (hs.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j)))
  have hL : S (L k X) := by
    apply ContMDiffOn.sum_section
    intro i _
    apply ContMDiffOn.sum_section
    intro j _
    exact (ha i j).smul_section
      (contMDiffOn_curvatureOnFields_iteratedCovariantDerivative (F.connection t)
        e.open_baseSet (k + 2) _ (hcons _ _ (hE i) (hcons _ _ (hE j) hX)))
  have hmd (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% Q) x :=
    (hQ.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have herrN : N P (Err k X) x = N P (dotK k X) x - N P (L k X) x := by
    have hc := (F.connection t).connection.isCovariantDerivativeOn (s := univ)
    have heq := congrArg (fun f => f (P x))
      (hc.add (hmd _ (hdot.sub_section hL)) (hmd _ hL))
    rw [sub_add_cancel] at heq
    exact eq_sub_iff_add_eq.mpr heq.symm
  rw [herrN]
  dsimp only [Err]
  simp only [Finset.sum_sub_distrib]
  linear_combination (norm := module) htime + htrace + hcot

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ricciFlow_iteratedCurvature_lowered_residual_succ
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) (k : ℕ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let g := F.metric t
    let D := F.connection t
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun y : M => ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ)
      x0 y x0 y (g.inner y)
    let a := fun (y : M) (i j : Fin n) => (G y).inverse (EuclideanSpace.proj j) i
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.connection Q y (P y)
    let R := fun (P Q Z : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.curvatureOnFields P Q Z y
    let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
    let dotK := fun r (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
      deriv (fun s => K s r Z y) t
    let L := fun r (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
      ∑ i, ∑ j, a y i j • K t (r + 2) (Fin.cons (E i) (Fin.cons (E j) Z)) y
    let Err := fun r Z y => dotK r Z y - L r Z y
    let lowErr := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
      g.inner y (Err r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
    let B := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      deriv (fun s => (F.connection s).connection Q y (P y)) t
    let Co := fun (P A C : (y : M) → TangentSpace (𝓡 n) y)
      (Y : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
      R P A (K t (k + 1) (Fin.cons C Y)) y -
      K t (k + 1) (Fin.cons (R P A C) Y) y -
      (∑ l, K t (k + 1) (Fin.cons C (Function.update Y l (R P A (Y l)))) y) +
      K t 1 ![A, P, C, K t k Y] y +
      R P C (K t (k + 1) (Fin.cons A Y)) y -
      (∑ l, K t (k + 1) (Fin.cons A (Function.update Y l (R P C (Y l)))) y) -
      ∑ l, K t k (Function.update Y l (K t 1 ![A, P, C, Y l])) y
    let Corr := fun P (Y : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
      B P (K t k Y) y - (∑ l, K t k (Function.update Y l (B P (Y l))) y) +
      ∑ i, ∑ j, a y i j • Co P (E i) (E j) Y y
    ∀ {x : M}, x ∈ e.baseSet →
      ∀ (P : (y : M) → TangentSpace (𝓡 n) y)
        (X : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y),
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) e.baseSet →
      (∀ l, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (X l)) e.baseSet) →
      lowErr (k + 1) (Fin.cons P X) x =
        mvfderiv (𝓡 n) (lowErr k X) x (P x) -
          (∑ l, lowErr k (Function.update X l (N P (X l))) x) +
        g.inner x (Corr P (Fin.init X) x) (X (Fin.last (k + 3)) x) := by
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
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection Q y (P y)
  let R := fun (P Q Z : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields P Q Z y
  let K := fun s => curvatureOnFields_iteratedCovariantDerivative (F.connection s)
  let dotK := fun r (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
    deriv (fun s => K s r Z y) t
  let L := fun r (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
    ∑ i, ∑ j, a y i j • K t (r + 2) (Fin.cons (E i) (Fin.cons (E j) Z)) y
  let Err := fun r Z y => dotK r Z y - L r Z y
  let lowErr := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (Err r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
  let B := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    deriv (fun s => (F.connection s).connection Q y (P y)) t
  let Co := fun (P A C : (y : M) → TangentSpace (𝓡 n) y)
    (Y : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
    R P A (K t (k + 1) (Fin.cons C Y)) y -
    K t (k + 1) (Fin.cons (R P A C) Y) y -
    (∑ l, K t (k + 1) (Fin.cons C (Function.update Y l (R P A (Y l)))) y) +
    K t 1 ![A, P, C, K t k Y] y +
    R P C (K t (k + 1) (Fin.cons A Y)) y -
    (∑ l, K t (k + 1) (Fin.cons A (Function.update Y l (R P C (Y l)))) y) -
    ∑ l, K t k (Function.update Y l (K t 1 ![A, P, C, Y l])) y
  let Corr := fun P (Y : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
    B P (K t k Y) y - (∑ l, K t k (Function.update Y l (B P (Y l))) y) +
    ∑ i, ∑ j, a y i j • Co P (E i) (E j) Y y
  intro x hx P X hP hX
  let Y := Fin.init X
  let z := X (Fin.last (k + 3))
  let S := fun Q : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% Q) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ _ i
  have hY (j : Fin (k + 3)) : S (Y j) := hX j.castSucc
  have hcons {r : ℕ} (A : (y : M) → TangentSpace (𝓡 n) y)
      (Z : Fin r → (y : M) → TangentSpace (𝓡 n) y) (hA : S A) (hZ : ∀ j, S (Z j)) :
      ∀ j, S ((Fin.cons A Z : Fin (r + 1) → (y : M) → TangentSpace (𝓡 n) y) j) := by
    intro j
    refine Fin.cases ?_ (fun l => ?_) j
    · simpa only [Fin.cons_zero] using hA
    · simpa only [Fin.cons_succ] using hZ l
  have hdot : S (dotK k Y) := by
    have hf := contMDiffOn_family_curvatureOnFields_iteratedCovariantDerivative
      F.smooth F.connection e.open_baseSet k (fun j _ => Y j)
      (fun j => (hY j).comp contMDiffOn_snd (fun _ hp => hp.2))
    exact (family_tangent_time_derivative (F.metric 0) e.open_baseSet
      (fun s y => K s k Y y) hf ht).2
  have ha (i j : Fin n) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => a y i j) e.baseSet := by
    have hi := (contMDiffOn_family_metric_frame_inverse F.smooth x0).2.2
    have hs := hi.comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => (t, y)) e.baseSet from contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨interior_subset ht, hy⟩)
    exact (contMDiffOn_const (c := EuclideanSpace.proj i)).clm_apply
      (hs.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j)))
  have hL : S (L k Y) := by
    apply ContMDiffOn.sum_section
    intro i _
    apply ContMDiffOn.sum_section
    intro j _
    exact (ha i j).smul_section
      (contMDiffOn_curvatureOnFields_iteratedCovariantDerivative (F.connection t)
        e.open_baseSet (k + 2) _ (hcons _ _ (hE i) (hcons _ _ (hE j) hY)))
  have hErr : S (Err k Y) := hdot.sub_section hL
  have hmd (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) (T% Q) x :=
    (hQ.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hd := D.mvfderiv_inner P (Err k Y) z
    (hmd _ hErr) (hmd _ (hX (Fin.last (k + 3))))
  change mvfderiv (𝓡 n) (lowErr k X) x (P x) =
    g.inner x (N P (Err k Y) x) (z x) + g.inner x (Err k Y x) (N P z x) at hd
  have hv := ricciFlow_iteratedCurvature_residual_succ F ht x0 k hx P Y hP hY
  change Err (k + 1) (Fin.cons P Y) x =
    N P (Err k Y) x - (∑ l, Err k (Function.update Y l (N P (Y l))) x) +
    B P (K t k Y) x - (∑ l, K t k (Function.update Y l (B P (Y l))) x) +
    ∑ i, ∑ j, a x i j • Co P (E i) (E j) Y x at hv
  have hv' : Err (k + 1) (Fin.cons P Y) x =
      (N P (Err k Y) x - (∑ l, Err k (Function.update Y l (N P (Y l))) x)) +
        Corr P Y x := by
    dsimp only [Corr]
    linear_combination (norm := module) hv
  have hcast (j : Fin (k + 3)) :
      lowErr k (Function.update X j.castSucc (N P (X j.castSucc))) x =
        g.inner x (Err k (Function.update Y j (N P (Y j))) x) (z x) := by
    dsimp only [lowErr]
    rw [Fin.init_update_castSucc, Function.update_of_ne (Fin.castSucc_ne_last j).symm]
    rfl
  have hlast : lowErr k (Function.update X (Fin.last (k + 3)) (N P z)) x =
      g.inner x (Err k Y x) (N P z x) := by
    dsimp only [lowErr]
    rw [Fin.init_update_last, Function.update_self]
  have hsum : (∑ l, lowErr k (Function.update X l (N P (X l))) x) =
      (∑ j, g.inner x (Err k (Function.update Y j (N P (Y j))) x) (z x)) +
        g.inner x (Err k Y x) (N P z x) := by
    rw [Fin.sum_univ_castSucc, hlast]
    simp only [hcast]
  have hinit : Fin.init (Fin.cons (α := fun _ : Fin (k + 5) =>
      (y : M) → TangentSpace (𝓡 n) y) P X) =
      Fin.cons (α := fun _ : Fin (k + 4) => (y : M) → TangentSpace (𝓡 n) y)
        P (Fin.init X) := by
    funext j
    refine Fin.cases ?_ (fun l => ?_) j
    · rfl
    · simp only [Fin.init, Fin.castSucc_succ, Fin.cons_succ]
  have hnext : lowErr (k + 1) (Fin.cons P X) x =
      g.inner x (Err (k + 1) (Fin.cons P Y) x) (z x) := by
    simp only [lowErr, hinit, Fin.cons_last]
    rfl
  change lowErr (k + 1) (Fin.cons P X) x =
    mvfderiv (𝓡 n) (lowErr k X) x (P x) -
      (∑ l, lowErr k (Function.update X l (N P (X l))) x) +
    g.inner x (Corr P Y x) (z x)
  rw [hnext, hv', hsum, hd]
  simp only [map_add, map_sub, map_sum, add_apply, sub_apply, sum_apply]
  ring

end PoincareConjecture.Proofs.M03

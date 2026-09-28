import PoincareConjecture.Proofs.M03.CurvatureTimeHessian
import PoincareConjecture.Proofs.M03.CurvatureDiffusionContraction
import PoincareConjecture.Proofs.M03.RicciHessianCommutator









set_option autoImplicit false
set_option maxHeartbeats 3600000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasDerivAt_ricciFlow_curvature_diffusion_reaction
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
    let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
    let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
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
    let R := fun (a c d : TangentSpace (𝓡 n) x) => D.curvature x a c d
    let P := fun a : TangentSpace (𝓡 n) x => ∑ i, D.ricci x a (b i) • b i
    let L := ∑ i, ddR (E i) (E i) X Y Z x
    let Q := (∑ i,
        (R (R u v (b i)) (b i) w -
          (2 : ℝ) • R v (b i) (R (b i) u w) +
          (2 : ℝ) • R (b i) u (R v (b i) w))) +
      P (R u v w) - R (P u) v w - R u (P v) w - R u v (P w)
    HasDerivAt (fun s => (F.connection s).curvature x u v w) (L + Q) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  classical
  let D := F.connection t
  let g := F.metric t
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let b0 : Module.Basis ι ℝ (TangentSpace (𝓡 n) x) :=
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    b.toBasis
  have hb0 (i : ι) : b0 i = b i := by
    simp only [b0, OrthonormalBasis.coe_toBasis]
  let ext := fun a : TangentSpace (𝓡 n) x =>
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
  let E := fun i : ι => ext (b i)
  let X := ext u
  let Y := ext v
  let Z := ext w
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let U := e.baseSet
  have hU : IsOpen U := e.open_baseSet
  have hx : x ∈ U := FiberBundle.mem_baseSet_trivializationAt' x
  let S := fun A : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U
  have hExt (a : TangentSpace (𝓡 n) x) : S (ext a) := by
    suffices hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun y => (e ⟨y, ext a y⟩).2) U by
      intro y hy
      rw [e.contMDiffWithinAt_section _ hy]
      exact hh y hy
    have hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun _y : M => (e ⟨x, a⟩).2) U := contMDiffOn_const
    apply hh.congr
    intro y hy
    change (e ⟨y, e.symm y (e ⟨x, a⟩).2⟩).2 = (e ⟨x, a⟩).2
    simpa only using congrArg Prod.snd (e.apply_mk_symm hy (e ⟨x, a⟩).2)
  have hExtValue (a : TangentSpace (𝓡 n) x) : ext a x = a :=
    FiberBundle.extend_apply_self _ _
  have hX : S X := hExt u
  have hY : S Y := hExt v
  have hZ : S Z := hExt w
  have hE (i : ι) : S (E i) := hExt (b i)
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.connection B y (A y)
  let Rf := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.curvatureOnFields A B C y
  let K := fun (A B C G : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N A (Rf B C G) y - Rf (N A B) C G y -
      Rf B (N A C) G y - Rf B C (N A G) y
  let H := fun (A B C G L : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N A (K B C G L) y - K (N A B) C G L y -
      K B (N A C) G L y - K B C (N A G) L y - K B C G (N A L) y
  let c := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    mvfderiv (𝓡 n) (fun z => D.ricci z (B z) (C z)) y (A y) -
      D.ricci y (N A B y) (C y) - D.ricci y (B y) (N A C y)
  let I2 := fun (A B C G : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    mvfderiv (𝓡 n) (c B C G) y (A y) -
      c (N A B) C G y - c B (N A C) G y - c B C (N A G) y
  let R := fun (a c d : TangentSpace (𝓡 n) x) => D.curvature x a c d
  let P := fun a : TangentSpace (𝓡 n) x => ∑ i, D.ricci x a (b i) • b i
  let L := ∑ i, H (E i) (E i) X Y Z x
  let Q := (∑ i,
      (R (R u v (b i)) (b i) w -
        (2 : ℝ) • R v (b i) (R (b i) u w) +
        (2 : ℝ) • R (b i) u (R v (b i) w))) +
    P (R u v w) - R (P u) v w - R u (P v) w - R u v (P w)
  let Vtime := fun s => (F.connection s).curvature x u v w
  change HasDerivAt Vtime (L + Q) t
  have hmd (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A)
      {y : M} (hy : y ∈ U) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) y :=
    (hA.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : S (N A B) :=
    D.contMDiffOn_connection_apply hU A B hA hB
  have hRf (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (Rf A B C) := by
    have hbr : S (VectorField.mlieBracket (𝓡 n) A B) := by
      intro y hy
      exact ((hA.contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
        (hB.contMDiffAt (hU.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hN A _ hA (hN B C hB hC)).sub_section
      (hN B _ hB (hN A C hA hC))).sub_section (hN _ C hbr hC)
  have hK (A B C G : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hG : S G) : S (K A B C G) :=
    (((hN A _ hA (hRf B C G hB hC hG)).sub_section
      (hRf _ C G (hN A B hA hB) hC hG)).sub_section
      (hRf B _ G hB (hN A C hA hC) hG)).sub_section
      (hRf B C _ hB hC (hN A G hA hG))
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hNadd (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) (hC : S C) {y : M} (hy : y ∈ U) :
      N A (B + C) y = N A B y + N A C y :=
    congrArg (fun f => f (A y)) (hc.add (hmd B hB hy) (hmd C hC hy))
  have hNneg (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) {y : M} (hy : y ∈ U) : N A (-B) y = -N A B y := by
    simpa only [neg_one_smul, neg_apply, N] using
      congrArg (fun f => f (A y)) (hc.smul_const (-1) (hmd B hB hy))
  have hNcongr (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) (hC : S C) (heq : ∀ y ∈ U, B y = C y)
      {y : M} (hy : y ∈ U) : N A B y = N A C y :=
    congrArg (fun f => f (A y))
      ((D.connection.isCovariantDerivativeOn (s := U)).congr_of_eqOn
        (hmd B hB hy) (hmd C hC hy) (hU.mem_nhds hy) heq)
  have hRfSwap (A B C : (y : M) → TangentSpace (𝓡 n) y) :
      Rf A B C = -Rf B A C :=
    funext fun y => curvatureOnFields_swap D A B C y
  have hKSwap (A B C G : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hG : S G)
      {y : M} (hy : y ∈ U) : K A B C G y = -K A C B G y := by
    dsimp only [K]
    rw [hRfSwap B C G, hNneg A (Rf C B G) (hRf C B G hC hB hG) hy,
      hRfSwap (N A B) C G, hRfSwap B (N A C) G, hRfSwap B C (N A G)]
    simp only [Pi.neg_apply]
    module
  have hKCyclic (A B C G : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hG : S G)
      {y : M} (hy : y ∈ U) :
      K A B C G y + K B C A G y + K C A B G y = 0 :=
    curvatureOnFields_second_bianchi D hU A B C G hA hB hC hG hy
  have hHCyclic (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x + H P A B Q C x + H P B Q A C x = 0 := by
    have hs := ((hK Q A B C hQ hA hB hC).add_section
      (hK A B Q C hA hB hQ hC)).add_section (hK B Q A C hB hQ hA hC)
    have heq := congrArg (fun f => f (P x))
      ((D.connection.isCovariantDerivativeOn (s := U)).congr_of_eqOn
        (hmd _ hs hx) (Bundle.mdifferentiableAt_zeroSection ..) (hU.mem_nhds hx)
        (fun y hy => hKCyclic Q A B C hQ hA hB hC hy))
    have hd : N P (K Q A B C) x + N P (K A B Q C) x +
        N P (K B Q A C) x = 0 := by
      change N P (K Q A B C + K A B Q C + K B Q A C) x =
        D.connection 0 x (P x) at heq
      rw [hNadd P _ _ ((hK Q A B C hQ hA hB hC).add_section
          (hK A B Q C hA hB hQ hC)) (hK B Q A C hB hQ hA hC) hx,
        hNadd P _ _ (hK Q A B C hQ hA hB hC) (hK A B Q C hA hB hQ hC) hx,
        hc.zero, zero_apply] at heq
      exact heq
    have hq := hKCyclic (N P Q) A B C (hN P Q hP hQ) hA hB hC hx
    have ha := hKCyclic Q (N P A) B C hQ (hN P A hP hA) hB hC hx
    have hb := hKCyclic Q A (N P B) C hQ hA (hN P B hP hB) hC hx
    have hh := hKCyclic Q A B (N P C) hQ hA hB (hN P C hP hC) hx
    calc
      _ = (N P (K Q A B C) x + N P (K A B Q C) x + N P (K B Q A C) x) -
          (K (N P Q) A B C x + K A B (N P Q) C x + K B (N P Q) A C x) -
          (K Q (N P A) B C x + K (N P A) B Q C x + K B Q (N P A) C x) -
          (K Q A (N P B) C x + K A (N P B) Q C x + K (N P B) Q A C x) -
          (K Q A B (N P C) x + K A B Q (N P C) x + K B Q A (N P C) x) := by
        dsimp only [H]
        module
      _ = 0 := by rw [hd, hq, ha, hb, hh]; module
  have hHSwap (P Q A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) :
      H P Q A B C x = -H P Q B A C x := by
    have hd := hNcongr P (K Q A B C) (-K Q B A C)
      (hK Q A B C hQ hA hB hC) (hK Q B A C hQ hB hA hC).neg_section
      (fun y hy => hKSwap Q A B C hQ hA hB hC hy) hx
    rw [hNneg P _ (hK Q B A C hQ hB hA hC) hx] at hd
    dsimp only [H]
    rw [hd,
      hKSwap (N P Q) A B C (hN P Q hP hQ) hA hB hC hx,
      hKSwap Q (N P A) B C hQ (hN P A hP hA) hB hC hx,
      hKSwap Q A (N P B) C hQ hA (hN P B hP hB) hC hx,
      hKSwap Q A B (N P C) hQ hA hB (hN P C hP hC) hx]
    module
  have hDirectionTrace (A B C G : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hG : S G) :
      (∑ i, b0.repr (H A (E i) B C G x) i) =
        I2 A B C G x - I2 A C B G x := by
    have hh₁ := ricci_second_covariant_derivative_eq_sum_basis D hU A B C G
      hA hB hC hG hx b0
    have hh₂ := ricci_second_covariant_derivative_eq_sum_basis D hU A C B G
      hA hC hB hG hx b0
    change I2 A B C G x = ∑ i, b0.repr (H A B (E i) C G x) i at hh₁
    change I2 A C B G x = ∑ i, b0.repr (H A C (E i) B G x) i at hh₂
    rw [hh₁, hh₂, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    have hc := hHCyclic A (E i) B C G hA (hE i) hB hC hG
    rw [hHSwap A B C (E i) G hA hB hC (hE i) hG] at hc
    have hi : H A (E i) B C G x = H A B (E i) C G x - H A C (E i) B G x := by
      apply eq_of_sub_eq_zero
      calc
        _ = H A (E i) B C G x + -H A B (E i) C G x + H A C (E i) B G x := by
          module
        _ = 0 := hc
    rw [hi, map_sub, Finsupp.sub_apply]
  have hcoord (a : TangentSpace (𝓡 n) x) (i : ι) :
      b0.repr a i = g.inner x a (b i) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change b.toBasis.repr a i = _
    rw [b.coe_toBasis_repr_apply, b.repr_apply_apply]
    exact g.symm x (b i) a
  have hRfEval (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      Rf A B C x = R (A x) (B x) (C x) :=
    (curvature_eq_curvatureOnFields D hU A B C hA hB hC hx).symm
  let CR := fun (a b c d e : TangentSpace (𝓡 n) x) =>
    R a b (R c d e) - R (R a b c) d e - R c (R a b d) e - R c d (R a b e)
  let Cr := fun (a b c d : TangentSpace (𝓡 n) x) =>
    -D.ricci x (R a b c) d - D.ricci x c (R a b d)
  let U0 := fun d : TangentSpace (𝓡 n) x =>
    ∑ i, g.inner x (CR d (b i) u v w - CR w (b i) u v d) (b i)
  let V0 := fun d : TangentSpace (𝓡 n) x =>
    -Cr u v w d - Cr u w v d + Cr v w u d + Cr u d v w - Cr v d u w
  have hCurvComm (A B C G W : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hG : S G) (hW : S W) :
      H A B C G W x - H B A C G W x = CR (A x) (B x) (C x) (G x) (W x) := by
    have hh := curvatureOnFields_second_derivative_commutator D hU
      A B C G W hA hB hC hG hW hx
    change H A B C G W x - H B A C G W x =
      Rf A B (Rf C G W) x - Rf (Rf A B C) G W x -
        Rf C (Rf A B G) W x - Rf C G (Rf A B W) x at hh
    simp (disch := solve_by_elim [hRf]) only [hRfEval] at hh
    exact hh
  have hRicComm (A B C G : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hG : S G) :
      I2 A B C G x - I2 B A C G x = Cr (A x) (B x) (C x) (G x) := by
    have hh := ricci_second_covariant_derivative_commutator D hU
      A B C G hA hB hC hG hx
    change I2 A B C G x - I2 B A C G x =
      -D.ricci x (Rf A B C x) (G x) - D.ricci x (C x) (Rf A B G x) at hh
    rw [hRfEval A B C hA hB hC, hRfEval A B G hA hB hG] at hh
    exact hh
  have hPrincipal (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      (I2 W X Y Z x - I2 W Y X Z x) - (I2 Z X Y W x - I2 Z Y X W x) =
        g.inner x L (W x) + U0 (W x) := by
    rw [← hDirectionTrace W X Y Z hW hX hY hZ,
      ← hDirectionTrace Z X Y W hZ hX hY hW, ← Finset.sum_sub_distrib]
    have hi (i : ι) :
        b0.repr (H W (E i) X Y Z x) i -
            b0.repr (H Z (E i) X Y W x) i =
          g.inner x (H (E i) (E i) X Y Z x) (W x) +
            g.inner x (CR (W x) (b i) u v w - CR w (b i) u v (W x)) (b i) := by
      have hc₁ := congrArg (fun a => g.inner x a (b i))
        (hCurvComm W (E i) X Y Z hW (hE i) hX hY hZ)
      have hc₂ := congrArg (fun a => g.inner x a (b i))
        (hCurvComm Z (E i) X Y W hZ (hE i) hX hY hW)
      simp only [X, Y, Z, E, hExtValue, map_sub, sub_apply] at hc₁ hc₂
      have hp := curvatureOnFields_hessian_bianchi_pairing D hU
        (E i) W X Y Z (E i) (hE i) hW hX hY hZ (hE i) hx
      change g.inner x (H (E i) W X Y Z x) (E i x) -
          g.inner x (H (E i) Z X Y W x) (E i x) =
        g.inner x (H (E i) (E i) X Y Z x) (W x) at hp
      have hei : E i x = b i := hExtValue (b i)
      rw [hei] at hp
      simp only [hcoord, map_sub, sub_apply, X, Y, Z, E] at hp ⊢
      linarith only [hc₁, hc₂, hp]
    calc
      _ = ∑ i, (g.inner x (H (E i) (E i) X Y Z x) (W x) +
          g.inner x (CR (W x) (b i) u v w - CR w (b i) u v (W x)) (b i)) :=
        Finset.sum_congr rfl (fun i _hi => hi i)
      _ = _ := by
        simp only [Finset.sum_add_distrib, L, U0, map_sum, sum_apply]
        rfl
  have hGeo (d : TangentSpace (𝓡 n) x) :
      g.inner x (deriv Vtime t) d = g.inner x L d + U0 d + V0 d := by
    let W := ext d
    have hW : S W := hExt d
    have hh := (ricciFlow_curvature_time_derivative_pairing F ht hU
      X Y Z W hX hY hZ hW hx).2
    have hxv : X x = u := hExtValue u
    have hyv : Y x = v := hExtValue v
    have hzv : Z x = w := hExtValue w
    have hwv : W x = d := hExtValue d
    change g.inner x (deriv (fun s => (F.connection s).curvature x (X x) (Y x) (Z x)) t)
        (W x) = -I2 X Y Z W x - I2 X Z Y W x + I2 X W Y Z x +
          I2 Y X Z W x + I2 Y Z X W x - I2 Y W X Z x at hh
    rw [hxv, hyv, hzv, hwv] at hh
    have hp := hPrincipal W hW
    rw [hwv] at hp
    have h₁ := hRicComm X Y Z W hX hY hZ hW
    have h₂ := hRicComm X Z Y W hX hZ hY hW
    have h₃ := hRicComm Y Z X W hY hZ hX hW
    have h₄ := hRicComm X W Y Z hX hW hY hZ
    have h₅ := hRicComm Y W X Z hY hW hX hZ
    rw [hxv, hyv, hzv, hwv] at h₁ h₂ h₃ h₄ h₅
    change g.inner x (deriv Vtime t) d = _ at hh
    dsimp only [V0]
    linarith only [hh, hp, h₁, h₂, h₃, h₄, h₅]
  let E0 := TangentSpace (𝓡 n) x
  let k := fun (a b c d : E0) => g.inner x (R a b c) d
  let ρ := D.ricci x
  obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
  have hRT (a b c : E0) : R a b c = T a b c := (hT a b c).symm
  have hrec (a : E0) : ∑ i, b0.repr a i • b i = a := b0.sum_repr a
  have hk12 (A B C G : E0) : k A B C G = -k B A C G := by
    have hh := congrArg (fun a => g.inner x a G)
      (curvatureOnFields_swap D (ext A) (ext B) (ext C) x)
    change g.inner x (D.curvatureOnFields (ext A) (ext B) (ext C) x) G =
      -g.inner x (D.curvatureOnFields (ext B) (ext A) (ext C) x) G
    simpa only [map_neg, neg_apply] using hh
  have hk34 (A B C G : E0) : k A B C G = -k A B G C := by
    have hh := curvature_pair_skew D x A B C G
    rw [g.symm x C (D.curvature x A B G)] at hh
    exact hh
  have hkrev (A B C G : E0) : k A B C G = k G C B A :=
    curvatureTensor_pair_exchange D x A B G C
  have hkpair (A B C G : E0) : k A B C G = k C G A B := by
    rw [hkrev A B C G, hk12 G C B A, hk34 C G B A, neg_neg]
  have hkcyclic (A B C G : E0) : k A B C G + k B C A G + k C A B G = 0 := by
    have hh := congrArg (fun a => g.inner x a G)
      (curvatureOnFields_first_bianchi D hU (ext A) (ext B) (ext C)
        (hExt A) (hExt B) (hExt C) hx)
    change g.inner x (D.curvatureOnFields (ext A) (ext B) (ext C) x) G +
      g.inner x (D.curvatureOnFields (ext B) (ext C) (ext A) x) G +
      g.inner x (D.curvatureOnFields (ext C) (ext A) (ext B) x) G = 0
    simpa only [map_add, add_apply, map_zero, zero_apply] using hh
  have htrace (A B : E0) : ρ A B = ∑ p, k (b p) A B (b p) := by
    have hh := ricci_eq_sum_basis_of_curvature_pairing D x A B b0
    simpa only [ρ, hcoord, k, R, hb0] using hh
  have hρsym (A B : E0) : ρ A B = ρ B A := by
    have he (A B : E0) :
        HasDerivAt (fun s => (F.metric s).inner x A B) (-2 * ρ A B) t :=
      (F.equation t (interior_subset ht) x A B).hasDerivAt
        (mem_interior_iff_mem_nhds.mp ht)
    have hb := (he B A).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => (F.metric s).symm x A B))
    have hh := (he A B).unique hb
    linarith only [hh]
  have hksum1 (a : ι → E0) (f : ι → ℝ) (B C G : E0) :
      k (∑ i, f i • a i) B C G = ∑ i, f i * k (a i) B C G := by
    simp only [k, hRT, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      sum_apply, smul_apply, smul_eq_mul]
  have hksum2 (a : ι → E0) (f : ι → ℝ) (A C G : E0) :
      k A (∑ i, f i • a i) C G = ∑ i, f i * k A (a i) C G := by
    simp only [k, hRT, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      sum_apply, smul_apply, smul_eq_mul]
  have hksum3 (a : ι → E0) (f : ι → ℝ) (A B G : E0) :
      k A B (∑ i, f i • a i) G = ∑ i, f i * k A B (a i) G := by
    simp only [k, hRT, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  have hρsum1 (a : ι → E0) (f : ι → ℝ) (B : E0) :
      ρ (∑ i, f i • a i) B = ∑ i, f i * ρ (a i) B := by
    simp only [htrace, hksum2, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hρsum2 (a : ι → E0) (f : ι → ℝ) (A : E0) :
      ρ A (∑ i, f i • a i) = ∑ i, f i * ρ A (a i) := by
    simp only [htrace, hksum3, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hkR1 (A B C G L W : E0) :
      k (R A B C) G L W = ∑ i, k A B C (b i) * k (b i) G L W := by
    calc
      _ = k (∑ i, b0.repr (R A B C) i • b i) G L W := by rw [hrec]
      _ = _ := by rw [hksum1]; simp only [hcoord, k]; rfl
  have hkR2 (A B C G L W : E0) :
      k A (R B C G) L W = ∑ i, k B C G (b i) * k A (b i) L W := by
    calc
      _ = k A (∑ i, b0.repr (R B C G) i • b i) L W := by rw [hrec]
      _ = _ := by rw [hksum2]; simp only [hcoord, k]; rfl
  have hkR3 (A B C G L W : E0) :
      k A B (R C G L) W = ∑ i, k C G L (b i) * k A B (b i) W := by
    calc
      _ = k A B (∑ i, b0.repr (R C G L) i • b i) W := by rw [hrec]
      _ = _ := by rw [hksum3]; simp only [hcoord, k]; rfl
  have hρR1 (A B C G : E0) :
      ρ (R A B C) G = ∑ i, k A B C (b i) * ρ (b i) G := by
    calc
      _ = ρ (∑ i, b0.repr (R A B C) i • b i) G := by rw [hrec]
      _ = _ := by rw [hρsum1]; simp only [hcoord, k]; rfl
  have hρR2 (A B C G : E0) :
      ρ A (R B C G) = ∑ i, k B C G (b i) * ρ A (b i) := by
    calc
      _ = ρ A (∑ i, b0.repr (R B C G) i • b i) := by rw [hrec]
      _ = _ := by rw [hρsum2]; simp only [hcoord, k]; rfl
  have hInnerP (A B : E0) : g.inner x (P A) B = ρ A B := by
    calc
      _ = ∑ i, ρ A (b i) * g.inner x (b i) B := by
        simp only [P, ρ, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
      _ = ∑ i, b0.repr B i * ρ A (b i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hcoord, g.symm x (b i) B]
        ring
      _ = ρ A (∑ i, b0.repr B i • b i) := (hρsum2 _ _ A).symm
      _ = ρ A B := by rw [hrec]
  let F0 := fun (d : E0) (p a : ι) =>
    k u v (b p) (b a) * k (b a) (b p) w d
  let Fp := fun (d : E0) (p a : ι) =>
    k (b p) u (b a) d * k v (b p) w (b a)
  let Fm := fun (d : E0) (p a : ι) =>
    k (b p) u w (b a) * k v (b p) (b a) d
  let Q0 := fun d : E0 => ∑ p, ∑ a,
    (F0 d p a - 2 * Fm d p a + 2 * Fp d p a)
  let O := fun d : E0 => ∑ a, ρ d (b a) * k u v w (b a)
  let I := fun d : E0 => ∑ a, ρ u (b a) * k (b a) v w d
  let Jinput := fun d : E0 => ∑ a, ρ v (b a) * k u (b a) w d
  let Kinput := fun d : E0 => ∑ a, ρ w (b a) * k u v (b a) d
  let U8 := fun (d : E0) (p a : ι) =>
    k u v w (b a) * k d (b p) (b a) (b p) -
    k d (b p) u (b a) * k (b a) v w (b p) -
    k d (b p) v (b a) * k u (b a) w (b p) -
    k d (b p) w (b a) * k u v (b a) (b p) -
    k u v d (b a) * k w (b p) (b a) (b p) +
    k w (b p) u (b a) * k (b a) v d (b p) +
    k w (b p) v (b a) * k u (b a) d (b p) +
    k w (b p) d (b a) * k u v (b a) (b p)
  let V4 := fun (d : E0) (a : ι) =>
    (k u v w (b a) + k u w v (b a) - k v w u (b a)) * ρ (b a) d +
    (k u v d (b a) - k u d v (b a) + k v d u (b a)) * ρ (b a) w +
    (k u w d (b a) - k u d w (b a)) * ρ v (b a) +
    (-k v w d (b a) + k v d w (b a)) * ρ u (b a)
  have hUcore (d : E0) (p a : ι) :
      U8 d p a =
        (k u v w (b a) * k d (b p) (b a) (b p) -
          k u v d (b a) * k w (b p) (b a) (b p)) +
        (F0 d a p - 2 * Fm d a p + 2 * Fp d a p) := by
    have h0 :
        (k w (b p) d (b a) - k d (b p) w (b a)) *
          k u v (b a) (b p) = F0 d a p := by
      have hc := hkcyclic w (b p) d (b a)
      rw [hk12 (b p) d w (b a), hk12 d w (b p) (b a),
        hkpair w d (b p) (b a)] at hc
      have he : k w (b p) d (b a) - k d (b p) w (b a) =
          k (b p) (b a) w d := by
        linarith only [hc]
      dsimp only [F0]
      rw [he]
      ring
    have h1 : k d (b p) u (b a) * k (b a) v w (b p) = -Fp d a p := by
      dsimp only [Fp]
      rw [hkrev d (b p) u (b a), hk12 (b a) v w (b p)]
      ring
    have h2 : k w (b p) u (b a) * k (b a) v d (b p) = -Fm d a p := by
      dsimp only [Fm]
      rw [hkpair w (b p) u (b a), hk12 u (b a) w (b p),
        hk12 (b a) v d (b p), hk34 v (b a) d (b p)]
      ring
    have h3 : k d (b p) v (b a) * k u (b a) w (b p) = Fm d a p := by
      dsimp only [Fm]
      rw [hkrev d (b p) v (b a), hk12 (b a) v (b p) d,
        hk12 u (b a) w (b p)]
      ring
    have h4 : k w (b p) v (b a) * k u (b a) d (b p) = Fp d a p := by
      dsimp only [Fp]
      rw [hkpair w (b p) v (b a), hk12 u (b a) d (b p), hk34 (b a) u d (b p)]
      ring
    calc
      U8 d p a =
          (k u v w (b a) * k d (b p) (b a) (b p) -
            k u v d (b a) * k w (b p) (b a) (b p)) +
          ((k w (b p) d (b a) - k d (b p) w (b a)) * k u v (b a) (b p)) -
          (k d (b p) u (b a) * k (b a) v w (b p)) +
          (k w (b p) u (b a) * k (b a) v d (b p)) -
          (k d (b p) v (b a) * k u (b a) w (b p)) +
          (k w (b p) v (b a) * k u (b a) d (b p)) := by
        dsimp only [U8]
        ring
      _ = _ := by
        conv_lhs => rw [h0, h1, h2, h3, h4]
        ring
  have htraceNeg (A B : E0) : (∑ p, k A (b p) B (b p)) = -ρ A B := by
    calc
      _ = ∑ p, -k (b p) A B (b p) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hk12 A (b p) B (b p)
      _ = -ρ A B := by rw [Finset.sum_neg_distrib, ← htrace A B]
  have hUout1 (d : E0) :
      (∑ p, ∑ a, k u v w (b a) * k d (b p) (b a) (b p)) = -O d := by
    calc
      _ = ∑ a, ∑ p, k u v w (b a) * k d (b p) (b a) (b p) := Finset.sum_comm
      _ = ∑ a, k u v w (b a) * (-ρ d (b a)) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [← Finset.mul_sum, htraceNeg d (b a)]
      _ = ∑ a, -(ρ d (b a) * k u v w (b a)) := by
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ = -O d := by simp only [O, Finset.sum_neg_distrib]
  have hUout2 (d : E0) :
      (∑ p, ∑ a, k u v d (b a) * k w (b p) (b a) (b p)) = Kinput d := by
    calc
      _ = ∑ a, ∑ p, k u v d (b a) * k w (b p) (b a) (b p) := Finset.sum_comm
      _ = ∑ a, k u v d (b a) * (-ρ w (b a)) := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [← Finset.mul_sum, htraceNeg w (b a)]
      _ = Kinput d := by
        dsimp only [Kinput]
        apply Finset.sum_congr rfl
        intro a _ha
        rw [hk34 u v d (b a)]
        ring
  have hUfinite (d : E0) : (∑ p, ∑ a, U8 d p a) = Q0 d - O d - Kinput d := by
    have hquad :
        (∑ p, ∑ a, (F0 d a p - 2 * Fm d a p + 2 * Fp d a p)) = Q0 d := by
      dsimp only [Q0]
      exact Finset.sum_comm
    calc
      _ = (∑ p, ∑ a, k u v w (b a) * k d (b p) (b a) (b p)) -
          (∑ p, ∑ a, k u v d (b a) * k w (b p) (b a) (b p)) +
          (∑ p, ∑ a, (F0 d a p - 2 * Fm d a p + 2 * Fp d a p)) := by
        simp_rw [hUcore d]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rfl
      _ = _ := by rw [hUout1 d, hUout2 d, hquad]; ring
  have hVcore (d : E0) (a : ι) :
      V4 d a = 2 * (ρ d (b a) * k u v w (b a)) -
        ρ u (b a) * k (b a) v w d - ρ v (b a) * k u (b a) w d := by
    have h1 : k u v w (b a) + k u w v (b a) - k v w u (b a) =
        2 * k u v w (b a) := by
      have hc := hkcyclic u v w (b a)
      rw [hk12 w u v (b a)] at hc
      linarith only [hc]
    have h2 : k u v d (b a) - k u d v (b a) + k v d u (b a) = 0 := by
      have hc := hkcyclic u v d (b a)
      rw [hk12 d u v (b a)] at hc
      linarith only [hc]
    have h3 : k u w d (b a) - k u d w (b a) = -k u (b a) w d := by
      have hc := hkcyclic u w d (b a)
      rw [hk12 d u w (b a), hkpair w d u (b a)] at hc
      linarith only [hc]
    have h4 : -k v w d (b a) + k v d w (b a) = -k (b a) v w d := by
      have hc := hkcyclic v w d (b a)
      rw [hk12 d v w (b a), hkpair w d v (b a), hk12 v (b a) w d] at hc
      linarith only [hc]
    dsimp only [V4]
    rw [h1, h2, h3, h4, hρsym (b a) d]
    ring
  have hV (d : E0) : (∑ a, V4 d a) = 2 * O d - I d - Jinput d := by
    calc
      _ = ∑ a, (2 * (ρ d (b a) * k u v w (b a)) -
          ρ u (b a) * k (b a) v w d - ρ v (b a) * k u (b a) w d) := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact hVcore d a
      _ = _ := by
        simp only [O, I, Jinput, Finset.sum_sub_distrib, Finset.mul_sum]
  have hUexpand (d : E0) : U0 d = ∑ p, ∑ a, U8 d p a := by
    dsimp only [U0]
    apply Finset.sum_congr rfl
    intro p _hp
    dsimp only [CR]
    simp only [map_sub, sub_apply]
    change (k d (b p) (R u v w) (b p) - k (R d (b p) u) v w (b p) -
        k u (R d (b p) v) w (b p) - k u v (R d (b p) w) (b p)) -
      (k w (b p) (R u v d) (b p) - k (R w (b p) u) v d (b p) -
        k u (R w (b p) v) d (b p) - k u v (R w (b p) d) (b p)) = _
    simp only [hkR1, hkR2, hkR3, U8, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have hVexpand (d : E0) : V0 d = ∑ a, V4 d a := by
    dsimp only [V0, Cr]
    change -(-ρ (R u v w) d - ρ w (R u v d)) -
      (-ρ (R u w v) d - ρ v (R u w d)) +
      (-ρ (R v w u) d - ρ u (R v w d)) +
      (-ρ (R u d v) w - ρ v (R u d w)) -
      (-ρ (R v d u) w - ρ u (R v d w)) = _
    simp only [hρR1, hρR2, hρsym w, V4, add_mul, sub_mul, neg_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  have hQpair (d : E0) :
      g.inner x Q d = Q0 d + O d - I d - Jinput d - Kinput d := by
    have hquad :
        g.inner x (∑ p,
          (R (R u v (b p)) (b p) w - (2 : ℝ) • R v (b p) (R (b p) u w) +
            (2 : ℝ) • R (b p) u (R v (b p) w))) d = Q0 d := by
      simp only [map_sum, sum_apply, map_add, add_apply,
        map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul]
      change (∑ p, (k (R u v (b p)) (b p) w d -
          2 * k v (b p) (R (b p) u w) d + 2 * k (b p) u (R v (b p) w) d)) = _
      dsimp only [Q0]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [hkR1, hkR3, hkR3]
      simp only [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _ha
      dsimp only [F0, Fp, Fm]
      ring
    have ho : g.inner x (P (R u v w)) d = O d := by
      rw [hInnerP, hρsym (R u v w) d, hρR2]
      dsimp only [O]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    have hi : g.inner x (R (P u) v w) d = I d :=
      hksum1 (fun a => b a) (fun a => ρ u (b a)) v w d
    have hj : g.inner x (R u (P v) w) d = Jinput d :=
      hksum2 (fun a => b a) (fun a => ρ v (b a)) u w d
    have hk : g.inner x (R u v (P w)) d = Kinput d :=
      hksum3 (fun a => b a) (fun a => ρ w (b a)) u v d
    simp only [Q, map_sub, sub_apply, map_add, add_apply, hquad, ho, hi, hj, hk]
  have hReaction (d : E0) : U0 d + V0 d = g.inner x Q d := by
    rw [hUexpand, hVexpand, hUfinite, hV, hQpair]
    ring
  have hVector : deriv Vtime t = L + Q := by
    apply b0.repr.injective
    ext i
    rw [hcoord, hcoord, map_add, add_apply]
    have h₁ := hGeo (b i)
    have h₂ := hReaction (b i)
    linarith only [h₁, h₂]
  have hActual := (ricciFlow_curvature_time_derivative_pairing F ht hU
    X Y Z X hX hY hZ hX hx).1
  have hxv : X x = u := hExtValue u
  have hyv : Y x = v := hExtValue v
  have hzv : Z x = w := hExtValue w
  rw [hxv, hyv, hzv] at hActual
  change HasDerivAt Vtime (deriv Vtime t) t at hActual
  rw [hVector] at hActual
  exact hActual



theorem curvature_reaction_eq_pure_inverse_frame_sum
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 x : M)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet)
    (u v w : TangentSpace (𝓡 n) x) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let b := g.orthonormalBasis x
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let R := D.curvature x
    let P := fun z : TangentSpace (𝓡 n) x => ∑ r, D.ricci x z (b r) • b r
    let Z := fun r s : TangentSpace (𝓡 n) x =>
      R (R u v r) s w - (2 : ℝ) • R v r (R s u w) +
        (2 : ℝ) • R r u (R v s w) + R (R u v w) r s -
        R (R u r s) v w - R u (R v r s) w - R u v (R w r s)
    (∑ r, (R (R u v (b r)) (b r) w -
        (2 : ℝ) • R v (b r) (R (b r) u w) +
        (2 : ℝ) • R (b r) u (R v (b r) w))) +
      P (R u v w) - R (P u) v w - R u (P v) w - R u v (P w) =
        ∑ i : Fin n, ∑ j : Fin n, a i j • Z (E i x) (E j x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let b := g.orthonormalBasis x
  let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
  obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
  let P := fun z : TangentSpace (𝓡 n) x => ∑ r, D.ricci x z (b r) • b r
  have hRic (z q : TangentSpace (𝓡 n) x) :
      D.ricci x z q = ∑ r, g.inner x (T z (b r) (b r)) q := by
    simp only [hT, b, LeviCivitaData.ricci, LeviCivitaData.curvatureTensor]
  have hP (z : TangentSpace (𝓡 n) x) :
      P z = ∑ r, T z (b r) (b r) := by
    simp only [P, hRic, Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    calc
      _ = ∑ s, g.inner x (b s) (T z (b r) (b r)) • b s := by
        apply Finset.sum_congr rfl
        intro s _
        rw [g.symm x]
      _ = _ := b.sum_repr' _
  let Z0 := fun r s : TangentSpace (𝓡 n) x =>
    T (T u v r) s w - (2 : ℝ) • T v r (T s u w) +
      (2 : ℝ) • T r u (T v s w) + T (T u v w) r s -
      T (T u r s) v w - T u (T v r s) w - T u v (T w r s)
  let Z : TangentSpace (𝓡 n) x →ₗ[ℝ]
      TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
    LinearMap.mk₂ ℝ Z0
      (by
        intro r r' s
        simp only [Z0, map_add, LinearMap.add_apply]
        module)
      (by
        intro c r s
        simp only [Z0, map_smul, LinearMap.smul_apply, smul_add, smul_sub,
          smul_smul]
        module)
      (by
        intro r s s'
        simp only [Z0, map_add, LinearMap.add_apply]
        module)
      (by
        intro c r s
        simp only [Z0, map_smul, LinearMap.smul_apply, smul_add, smul_sub,
          smul_smul]
        module)
  have hZ (r s : TangentSpace (𝓡 n) x) : Z r s = Z0 r s := rfl
  have hrec (z : TangentSpace (𝓡 n) x) :
      z = ∑ i : Fin n, theta i x z • E i x := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V z) hx
  have hbilin (r s : TangentSpace (𝓡 n) x) :
      Z r s = ∑ i : Fin n, ∑ j : Fin n,
        (theta i x r * theta j x s) • Z (E i x) (E j x) := by
    nth_rw 1 [hrec r]
    rw [map_sum, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, LinearMap.smul_apply]
    nth_rw 1 [hrec s]
    rw [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, smul_smul]
  have htrace (i j : Fin n) : a i j =
      ∑ r, theta i x (b r) * theta j x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hcontract : (∑ r, Z (b r) (b r)) =
      ∑ i : Fin n, ∑ j : Fin n, a i j • Z (E i x) (E j x) := by
    calc
      _ = ∑ r, ∑ i : Fin n, ∑ j : Fin n,
          (theta i x (b r) * theta j x (b r)) • Z (E i x) (E j x) :=
        Finset.sum_congr rfl (fun r _ => hbilin (b r) (b r))
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_smul, ← htrace]
  have hreaction :
      (∑ r, (T (T u v (b r)) (b r) w -
          (2 : ℝ) • T v (b r) (T (b r) u w) +
          (2 : ℝ) • T (b r) u (T v (b r) w))) +
        P (T u v w) - T (P u) v w - T u (P v) w - T u v (P w) =
          ∑ r, Z (b r) (b r) := by
    simp only [hP, hZ, Z0, map_sum, LinearMap.sum_apply,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
  dsimp only
  simpa only [hZ, Z0, hT, P, a, G, b, E, cb, e, V] using
    hreaction.trans hcontract


theorem curvature_reaction_lowered_two_contractions
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 x : M)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet)
    (u v w z : TangentSpace (𝓡 n) x) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := fun i => e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis i x
    let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
      (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x (g.inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let R := D.curvature x
    let L := fun A B C Z => g.inner x (R A B C) Z
    let Z := fun r s : TangentSpace (𝓡 n) x =>
      R (R u v r) s w - (2 : ℝ) • R v r (R s u w) +
        (2 : ℝ) • R r u (R v s w) + R (R u v w) r s -
        R (R u r s) v w - R u (R v r s) w - R u v (R w r s)
    g.inner x (∑ j0 : Fin n, ∑ j1 : Fin n, a j0 j1 • Z (E j0) (E j1)) z =
      ∑ j0 : Fin n, ∑ j1 : Fin n, ∑ i0 : Fin n, ∑ i1 : Fin n,
        (a i0 i1 * a j0 j1) *
          (L u v (E j0) (E i1) * L (E i0) (E j1) w z -
            2 * (L v (E j0) (E i0) z * L (E j1) u w (E i1)) +
            2 * (L (E j0) u (E i0) z * L v (E j1) w (E i1)) +
            L u v w (E i1) * L (E i0) (E j0) (E j1) z -
            L u (E j0) (E j1) (E i1) * L (E i0) v w z -
            L v (E j0) (E j1) (E i1) * L u (E i0) w z -
            L w (E j0) (E j1) (E i1) * L u v (E i0) z) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := fun i => e.localFrame cb i x
  let theta := e.localFrameCoeff (𝓡 n) cb
  let b := g.orthonormalBasis x
  let G := ContinuousLinearMap.inCoordinates V (TangentSpace (𝓡 n))
    (V →L[ℝ] ℝ) (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
  have hframe (W : TangentSpace (𝓡 n) x) :
      W = ∑ i : Fin n, theta i x W • E i := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V W) hx
  have hgram (i j : Fin n) :
      a i j = ∑ r, theta i x (b r) * theta j x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hinner (W : TangentSpace (𝓡 n) x) (r) :
      (∑ j : Fin n, theta j x (b r) * g.inner x W (E j)) = g.inner x W (b r) := by
    nth_rw 2 [hframe (b r)]
    simp only [map_sum, map_smul, smul_eq_mul]
  have horth (W : TangentSpace (𝓡 n) x) :
      (∑ r, g.inner x W (b r) • b r) = W := by
    have hh := b.sum_repr' W
    change (∑ r, g.inner x (b r) W • b r) = W at hh
    simpa only [g.symm x W] using hh
  have hcoeff (i : Fin n) (W : TangentSpace (𝓡 n) x) :
      (∑ j : Fin n, a i j * g.inner x W (E j)) = theta i x W := by
    simp only [hgram, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ r, theta i x (b r) *
          (∑ j : Fin n, theta j x (b r) * g.inner x W (E j)) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ r, theta i x (b r) * g.inner x W (b r) := by simp only [hinner]
      _ = theta i x (∑ r, g.inner x W (b r) • b r) := by
        simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
      _ = _ := by rw [horth]
  have hrec (W : TangentSpace (𝓡 n) x) :
      W = ∑ i : Fin n, ∑ j : Fin n,
        (a i j * g.inner x W (E j)) • E i := by
    nth_rw 1 [hframe W]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_smul, hcoeff]
  obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
  let L := fun A B C Z => g.inner x (T A B C) Z
  have hfirst (W A B : TangentSpace (𝓡 n) x) :
      g.inner x (T W A B) z =
        ∑ i : Fin n, ∑ j : Fin n,
          a i j * (g.inner x W (E j) * L (E i) A B z) := by
    nth_rw 1 [hrec W]
    simp only [L, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      sum_apply, smul_apply, smul_eq_mul, mul_assoc]
  have hsecond (A W B : TangentSpace (𝓡 n) x) :
      g.inner x (T A W B) z =
        ∑ i : Fin n, ∑ j : Fin n,
          a i j * (g.inner x W (E j) * L A (E i) B z) := by
    nth_rw 1 [hrec W]
    simp only [L, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      sum_apply, smul_apply, smul_eq_mul, mul_assoc]
  have hthird (A B W : TangentSpace (𝓡 n) x) :
      g.inner x (T A B W) z =
        ∑ i : Fin n, ∑ j : Fin n,
          a i j * (g.inner x W (E j) * L A B (E i) z) := by
    nth_rw 1 [hrec W]
    simp only [L, map_sum, map_smul,
      sum_apply, smul_apply, smul_eq_mul, mul_assoc]
  let Z := fun r s : TangentSpace (𝓡 n) x =>
    T (T u v r) s w - (2 : ℝ) • T v r (T s u w) +
      (2 : ℝ) • T r u (T v s w) + T (T u v w) r s -
      T (T u r s) v w - T u (T v r s) w - T u v (T w r s)
  have hZ (r s : TangentSpace (𝓡 n) x) :
      g.inner x (Z r s) z =
        ∑ i : Fin n, ∑ j : Fin n, a i j *
          (L u v r (E j) * L (E i) s w z -
            2 * (L v r (E i) z * L s u w (E j)) +
            2 * (L r u (E i) z * L v s w (E j)) +
            L u v w (E j) * L (E i) r s z -
            L u r s (E j) * L (E i) v w z -
            L v r s (E j) * L u (E i) w z -
            L w r s (E j) * L u v (E i) z) := by
    dsimp only [Z]
    simp only [map_sub, sub_apply, map_add, add_apply, map_smul, smul_apply,
      smul_eq_mul]
    rw [hfirst (T u v r) s w, hthird v r (T s u w),
      hthird r u (T v s w), hfirst (T u v w) r s,
      hfirst (T u r s) v w, hsecond u (T v r s) w, hthird u v (T w r s)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [L]
    ring
  dsimp only
  simp only [← hT]
  change g.inner x (∑ j0 : Fin n, ∑ j1 : Fin n, a j0 j1 • Z (E j0) (E j1)) z = _
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, hZ,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j0 _
  apply Finset.sum_congr rfl
  intro j1 _
  apply Finset.sum_congr rfl
  intro i0 _
  apply Finset.sum_congr rfl
  intro i1 _
  change a j0 j1 * (a i0 i1 * _) = a i0 i1 * a j0 j1 * _
  ring

end PoincareConjecture.Proofs.M03

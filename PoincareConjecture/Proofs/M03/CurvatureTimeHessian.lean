import PoincareConjecture.Proofs.M03.ConnectionVariation
import PoincareConjecture.Proofs.M03.CurvatureTimeVariation
import PoincareConjecture.Proofs.M03.CurvatureRicciDerivative
import PoincareConjecture.Proofs.M03.ConnectionRateRicciSmoothness









set_option autoImplicit false
set_option maxHeartbeats 2400000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem ricciFlow_curvature_time_derivative_pairing
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (X Y Z W : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (hW : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U)
    {x : M} (hx : x ∈ U) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let D := F.connection t
    let dRic := fun
        (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      mvfderiv (𝓡 n) (fun z => D.ricci z (B z) (C z)) y (A y) -
        D.ricci y (D.connection B y (A y)) (C y) -
        D.ricci y (B y) (D.connection C y (A y))
    let ddRic := fun
        (A B C E : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      mvfderiv (𝓡 n) (dRic B C E) y (A y) -
        dRic (fun z => D.connection B z (A z)) C E y -
        dRic B (fun z => D.connection C z (A z)) E y -
        dRic B C (fun z => D.connection E z (A z)) y
    let V := fun s => (F.connection s).curvature x (X x) (Y x) (Z x)
    HasDerivAt V (deriv V t) t ∧
      (F.metric t).inner x (deriv V t) (W x) =
        -ddRic X Y Z W x - ddRic X Z Y W x + ddRic X W Y Z x +
          ddRic Y X Z W x + ddRic Y Z X W x - ddRic Y W X Z x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let D := F.connection t
  let g := F.metric t
  let dRic := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    mvfderiv (𝓡 n) (fun z => D.ricci z (B z) (C z)) y (A y) -
      D.ricci y (D.connection B y (A y)) (C y) -
      D.ricci y (B y) (D.connection C y (A y))
  classical
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let S := fun (V : Set M)
      (A : (y : M) → TangentSpace (𝓡 n) y) =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) V
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.connection B y (A y)
  let Br := VectorField.mlieBracket (𝓡 n) (M := M)
  let Rf := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    D.curvatureOnFields A B C y
  have hN {V : Set M} (hV : IsOpen V)
      (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S V A) (hB : S V B) : S V (N A B) :=
    D.contMDiffOn_connection_apply hV A B hA hB
  have hBr {V : Set M} (hV : IsOpen V)
      (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S V A) (hB : S V B) : S V (Br A B) := by
    intro y hy
    exact ((hA.contMDiffAt (hV.mem_nhds hy)).mlieBracket_vectorField
      (hB.contMDiffAt (hV.mem_nhds hy))
      (m := ⊤) (n := ⊤) (by simp)).contMDiffWithinAt
  have hRf {V : Set M} (hV : IsOpen V)
      (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S V A) (hB : S V B) (hC : S V C) : S V (Rf A B C) :=
    ((hN hV A _ hA (hN hV B C hB hC)).sub_section
      (hN hV B _ hB (hN hV A C hA hC))).sub_section
        (hN hV _ C (hBr hV A B hA hB) hC)
  have hRic {V : Set M} (hV : IsOpen V)
      (B C : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S V B) (hC : S V C) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun z => D.ricci z (B z) (C z)) V := by
    intro y hy
    let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) y
    have he : y ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' y
    let b0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let W := V ∩ e.baseSet
    have hW : IsOpen W := hV.inter e.open_baseSet
    have hyW : y ∈ W := ⟨hy, he⟩
    let E := e.localFrame b0
    let q := fun (i : Fin n) (z : M) =>
      e.localFrameCoeff (𝓡 n) b0 i z (Rf (E i) B C z)
    have hBW : S W B := hB.mono inter_subset_left
    have hCW : S W C := hC.mono inter_subset_left
    have hE (i : Fin n) : S W (E i) :=
      (e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b0 i).mono
        (inter_subset_right : W ⊆ e.baseSet)
    have hq (i : Fin n) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q i) W :=
      contMDiffOn_localFrameCoeff b0 hW
        (inter_subset_right : W ⊆ e.baseSet)
        (hRf hW (E i) B C (hE i) hBW hCW) i
    have hsum : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun z => ∑ i, q i z) W :=
      contMDiffOn_finsetSum (fun i _hi => hq i)
    have htrace {z : M} (hz : z ∈ W) :
        D.ricci z (B z) (C z) = ∑ i, q i z := by
      rw [ricci_eq_sum_basis_of_curvature_pairing D z (B z) (C z)
        (e.basisAt b0 hz.2)]
      apply Finset.sum_congr rfl
      intro i _hi
      change _ = e.localFrameCoeff (𝓡 n) b0 i z (Rf (E i) B C z)
      rw [e.localFrameCoeff_apply_of_mem_baseSet b0 hz.2 (Rf (E i) B C) i]
      apply congrArg (fun v => (e.basisAt b0 hz.2).repr v i)
      have hEi : E i z = e.basisAt b0 hz.2 i :=
        e.localFrame_apply_of_mem_baseSet b0 hz.2
      rw [← hEi]
      exact curvature_eq_curvatureOnFields D hW (E i) B C
        (hE i) hBW hCW hz
    have hEq : (fun z => D.ricci z (B z) (C z)) =ᶠ[𝓝 y]
        (fun z => ∑ i, q i z) :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hyW) (fun z hz => htrace hz)
    exact ((hsum.contMDiffAt (hW.mem_nhds hyW)).congr_of_eventuallyEq
      hEq).contMDiffWithinAt
  have hScalarDeriv {V : Set M} (hV : IsOpen V) (f : M → ℝ)
      (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f V)
      (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S V A) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => mvfderiv (𝓡 n) f y (A y)) V := by
    have hf' : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (Function.uncurry (fun (_s : ℝ) (y : M) => f y)) (univ ×ˢ V) :=
      hf.comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd
        (fun _ hp => hp.2)
    have hs := contMDiffOn_family_spatial_mvfderiv
      (f := fun (_s : ℝ) (y : M) => f y) (J := univ) hV hf' A hA
    have hi : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) V :=
      contMDiffOn_const.prodMk contMDiffOn_id
    simpa only [Function.comp_def] using
      hs.comp hi (fun _ hy => ⟨mem_univ (0 : ℝ), hy⟩)
  have hDric {V : Set M} (hV : IsOpen V)
      (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S V A) (hB : S V B) (hC : S V C) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (dRic A B C) V := by
    have hd := hScalarDeriv hV
      (fun y => D.ricci y (B y) (C y)) (hRic hV B C hB hC) A hA
    have hAB := hN hV A B hA hB
    have hAC := hN hV A C hA hC
    simpa only [dRic, N, Pi.sub_apply] using
      (hd.sub (hRic hV (N A B) C hAB hC)).sub
        (hRic hV B (N A C) hB hAC)
  let ddRic := fun (A B C E : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    mvfderiv (𝓡 n) (dRic B C E) y (A y) -
      dRic (N A B) C E y - dRic B (N A C) E y - dRic B C (N A E) y
  let B0 := fun (A B : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    deriv (fun s => (F.connection s).connection B y (A y)) t
  let P0 := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    g.inner y (B0 A B y) (C y)
  let nablaB := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
    N A (B0 B C) y - B0 (N A B) C y - B0 B (N A C) y
  let Vtime := fun s => (F.connection s).curvature x (X x) (Y x) (Z x)
  change HasDerivAt Vtime (deriv Vtime t) t ∧
    g.inner x (deriv Vtime t) (W x) =
      -ddRic X Y Z W x - ddRic X Z Y W x + ddRic X W Y Z x +
        ddRic Y X Z W x + ddRic Y Z X W x - ddRic Y W X Z x
  have hmd (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S U A)
      {y : M} (hy : y ∈ U) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) y :=
    (hA.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hDricmd (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S U A) (hB : S U B) (hC : S U C) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (dRic A B C) x :=
    ((hDric hU A B C hA hB hC).contMDiffAt
      (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hB0 (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S U A) (hB : S U B) : S U (B0 A B) := by
    simpa only [B0] using
      (family_tangent_time_derivative (F.metric 0) hU
        (fun s y => (F.connection s).connection B y (A y))
        (contMDiffOn_connection_family_apply F.smooth F.connection hU B A hB hA) ht).2
  have hchart (f : M → ℝ) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
      {y : M} (hy : y ∈ U) (a : TangentSpace (𝓡 n) y) :
      fderiv ℝ (fun z => f ((extChartAt (𝓡 n) y).symm z))
          ((extChartAt (𝓡 n) y) y) a = mvfderiv (𝓡 n) f y a := by
    let ch := extChartAt (𝓡 n) y
    have hcy : ch y ∈ ch.target := mem_extChartAt_target y
    have hcsymm : ch.symm (ch y) = y := ch.left_inv (mem_extChartAt_source y)
    have hfAt := hf.contMDiffAt (hU.mem_nhds hy)
    have hch : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞
        ch.symm (ch y) :=
      (contMDiffOn_extChartAt_symm (I := 𝓡 n) y).contMDiffAt
        (extChartAt_target_mem_nhds' hcy)
    have heid : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n)
        ch.symm (ch y) = ContinuousLinearMap.id ℝ
          (TangentSpace (𝓡 n) (ch y)) := by
      simpa only [(𝓡 n).range_eq_univ, mfderivWithin_univ] using
        (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := y))
    have hdf : fderiv ℝ (fun z => f (ch.symm z)) (ch y) =
        mvfderiv (𝓡 n) f y := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (f ∘ ch.symm) (ch y) = _
      have hf' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (ch.symm (ch y)) := by
        simpa only [hcsymm] using hfAt.mdifferentiableAt (by simp)
      rw [mvfderiv_comp (ch y) hf' (hch.mdifferentiableAt (by simp)), heid]
      change mvfderiv (𝓡 n) f (ch.symm (ch y)) = mvfderiv (𝓡 n) f y
      rw [hcsymm]
    exact congrArg (fun L => L a) hdf
  have hIntrinsic (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S U A) (hB : S U B) (hC : S U C)
      {y : M} (hy : y ∈ U) :
      P0 A B C y = -dRic A B C y - dRic B C A y + dRic C A B y := by
    let ch := extChartAt (𝓡 n) y
    let cr := fun (P Q R : (z : M) → TangentSpace (𝓡 n) z) =>
      fderiv ℝ (fun z => D.ricci (ch.symm z) (Q (ch.symm z)) (R (ch.symm z)))
          (ch y) (P y) -
        D.ricci y (N P Q y) (R y) - D.ricci y (Q y) (N P R y)
    have hh := (ricciFlow_connection_variation_pairing F ht hU A B C hA hB hC hy).2
    change P0 A B C y = -cr A B C - cr B C A + cr C A B at hh
    have hcr (P Q R : (z : M) → TangentSpace (𝓡 n) z)
        (hQ : S U Q) (hR : S U R) : cr P Q R = dRic P Q R y := by
      dsimp only [cr, dRic, N]
      rw [hchart (fun z => D.ricci z (Q z) (R z)) (hRic hU Q R hQ hR) hy (P y)]
    rw [hcr A B C hB hC, hcr B C A hC hA, hcr C A B hA hB] at hh
    exact hh
  have hRicSymm (y : M) (a b : TangentSpace (𝓡 n) y) :
      D.ricci y a b = D.ricci y b a := by
    have he (a b : TangentSpace (𝓡 n) y) :
        HasDerivAt (fun s => (F.metric s).inner y a b) (-2 * D.ricci y a b) t :=
      (F.equation t (interior_subset ht) y a b).hasDerivAt
        (mem_interior_iff_mem_nhds.mp ht)
    have hb := (he b a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => (F.metric s).symm y a b))
    have hh := (he a b).unique hb
    linarith only [hh]
  have hDSym (A B C : (y : M) → TangentSpace (𝓡 n) y) :
      dRic A B C = dRic A C B := by
    have hf : (fun y => D.ricci y (B y) (C y)) =
        (fun y => D.ricci y (C y) (B y)) :=
      funext fun y => hRicSymm y (B y) (C y)
    funext y
    dsimp only [dRic]
    rw [hf, hRicSymm y (D.connection B y (A y)) (C y),
      hRicSymm y (B y) (D.connection C y (A y))]
    ring
  have hHSym (A B C E : (y : M) → TangentSpace (𝓡 n) y) (y : M) :
      ddRic A B C E y = ddRic A B E C y := by
    dsimp only [ddRic]
    rw [hDSym B C E, hDSym (N A B) C E,
      hDSym B (N A C) E, hDSym B C (N A E)]
    ring
  have hPderiv (A B C E : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S U B) (hC : S U C) (hE : S U E) :
      mvfderiv (𝓡 n) (P0 B C E) x (A x) =
        -mvfderiv (𝓡 n) (dRic B C E) x (A x) -
          mvfderiv (𝓡 n) (dRic C E B) x (A x) +
          mvfderiv (𝓡 n) (dRic E B C) x (A x) := by
    have heq : P0 B C E =ᶠ[𝓝 x]
        (fun y => -dRic B C E y - dRic C E B y + dRic E B C y) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hx)
        (fun y hy => hIntrinsic B C E hB hC hE hy)
    have h₁ := hDricmd B C E hB hC hE
    have h₂ := hDricmd C E B hC hE hB
    have h₃ := hDricmd E B C hE hB hC
    calc
      _ = mvfderiv (𝓡 n)
          (fun y => -dRic B C E y - dRic C E B y + dRic E B C y) x (A x) := by
        dsimp only [mvfderiv]
        rw [heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)), heq.eq_of_nhds]
      _ = _ := by
        rw [mvfderiv_fun_add (g := fun y => -dRic B C E y - dRic C E B y)
          (g' := dRic E B C) (h₁.neg.sub h₂) h₃, add_apply,
          mvfderiv_fun_sub (g := fun y => -dRic B C E y) (g' := dRic C E B)
            h₁.neg h₂, sub_apply, mvfderiv_fun_neg, neg_apply]
  have hPair (A B C E : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S U B) (hC : S U C) (hE : S U E) :
      g.inner x (nablaB A B C x) (E x) =
        mvfderiv (𝓡 n) (P0 B C E) x (A x) -
          P0 (N A B) C E x - P0 B (N A C) E x - P0 B C (N A E) x := by
    dsimp only [nablaB, P0]
    rw [D.mvfderiv_inner A (B0 B C) E
      (hmd _ (hB0 B C hB hC) hx) (hmd E hE hx)]
    simp only [map_sub, sub_apply]
    dsimp only [N]
    ring
  have hHess (A B C E : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S U A) (hB : S U B) (hC : S U C) (hE : S U E) :
      g.inner x (nablaB A B C x) (E x) =
        -ddRic A B C E x - ddRic A C B E x + ddRic A E B C x := by
    have hh : g.inner x (nablaB A B C x) (E x) =
        -ddRic A B C E x - ddRic A C E B x + ddRic A E B C x := by
      rw [hPair A B C E hB hC hE, hPderiv A B C E hB hC hE,
        hIntrinsic (N A B) C E (hN hU A B hA hB) hC hE hx,
        hIntrinsic B (N A C) E hB (hN hU A C hA hC) hE hx,
        hIntrinsic B C (N A E) hB hC (hN hU A E hA hE) hx]
      dsimp only [ddRic]
      ring
    rw [hHSym A C E B x] at hh
    exact hh
  have hd := hasDerivAt_ricciFlow_curvature F ht hU X Y Z hX hY hZ hx
  change HasDerivAt Vtime (nablaB X Y Z x - nablaB Y X Z x) t at hd
  refine ⟨hd.differentiableAt.hasDerivAt, ?_⟩
  rw [hd.deriv, map_sub, sub_apply,
    hHess X Y Z W hX hY hZ hW, hHess Y X Z W hY hX hZ hW]
  ring


theorem ricciFlow_connection_variation_pairing_eq_curvature_derivative_trace
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.connection B y (A y)
    let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.curvatureOnFields A B C y
    let K := fun (A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
      N A (R B C W) y - R (N A B) C W y -
        R B (N A C) W y - R B C (N A W) y
    (F.metric t).inner x
      (deriv (fun s => (F.connection s).connection Y x (X x)) t) (Z x) =
      -(∑ i, (F.metric t).inner x (K X (E i) Y Z x) (b i)) -
        (∑ i, (F.metric t).inner x (K Y (E i) Z X x) (b i)) +
        ∑ i, (F.metric t).inner x (K Z (E i) X Y x) (b i) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let D := F.connection t
  let g := F.metric t
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let b0 : Module.Basis ι ℝ (TangentSpace (𝓡 n) x) :=
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    b.toBasis
  let E := fun i : ι => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection B y (A y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let K := fun (A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
    N A (R B C W) y - R (N A B) C W y -
      R B (N A C) W y - R B C (N A W) y
  let dRic := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) =>
    mvfderiv (𝓡 n) (fun y => D.ricci y (B y) (C y)) x (A x) -
      D.ricci x (N A B x) (C x) - D.ricci x (B x) (N A C x)
  let ch := extChartAt (𝓡 n) x
  let cr := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) =>
    fderiv ℝ (fun z => D.ricci (ch.symm z) (B (ch.symm z)) (C (ch.symm z)))
        (ch x) (A x) - D.ricci x (N A B x) (C x) -
      D.ricci x (B x) (N A C x)
  have hchart (f : M → ℝ) (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
      (a : TangentSpace (𝓡 n) x) :
      fderiv ℝ (fun z => f (ch.symm z)) (ch x) a = mvfderiv (𝓡 n) f x a := by
    have hcx : ch x ∈ ch.target := mem_extChartAt_target x
    have hcsymm : ch.symm (ch x) = x := ch.left_inv (mem_extChartAt_source x)
    have hch : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞
        ch.symm (ch x) :=
      (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).contMDiffAt
        (extChartAt_target_mem_nhds' hcx)
    have heid : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n)
        ch.symm (ch x) = ContinuousLinearMap.id ℝ
          (TangentSpace (𝓡 n) (ch x)) := by
      simpa only [(𝓡 n).range_eq_univ, mfderivWithin_univ] using
        (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
    have hdf : fderiv ℝ (fun z => f (ch.symm z)) (ch x) = mvfderiv (𝓡 n) f x := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (f ∘ ch.symm) (ch x) = _
      have hf' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (ch.symm (ch x)) := by
        simpa only [hcsymm] using hf
      rw [mvfderiv_comp (ch x) hf' (hch.mdifferentiableAt (by simp)), heid]
      change mvfderiv (𝓡 n) f (ch.symm (ch x)) = mvfderiv (𝓡 n) f x
      rw [hcsymm]
    exact congrArg (fun L => L a) hdf
  have hcr (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hB : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
      (hC : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U) :
      cr A B C = dRic A B C := by
    have hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun y => D.ricci y (B y) (C y)) x :=
      (connection_rate_ricci_pair_smooth F ht hU B C hB hC hx).mdifferentiableAt (by simp)
    dsimp only [cr, dRic]
    rw [hchart (fun y => D.ricci y (B y) (C y)) hf (A x)]
  have hb0 (i : ι) : b0 i = b i := by
    simp only [b0, OrthonormalBasis.coe_toBasis]
  have hrepr (v : TangentSpace (𝓡 n) x) (i : ι) :
      b0.repr v i = g.inner x v (b i) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change (g.orthonormalBasis x).toBasis.repr v i =
      g.inner x v ((g.orthonormalBasis x) i)
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    exact g.symm x _ _
  have htrace (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
      (hC : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U) :
      dRic A B C = ∑ i, g.inner x (K A (E i) B C x) (b i) := by
    have hh := ricci_covariant_derivative_eq_sum_basis D hU A B C hA hB hC hx b0
    change dRic A B C = ∑ i, b0.repr
      (K A (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b0 i)) B C x) i at hh
    simpa only [hrepr, hb0, E] using hh
  have hh := (ricciFlow_connection_variation_pairing F ht hU X Y Z hX hY hZ hx).2
  change g.inner x (deriv (fun s => (F.connection s).connection Y x (X x)) t) (Z x) =
    -cr X Y Z - cr Y Z X + cr Z X Y at hh
  rw [hcr X Y Z hY hZ, hcr Y Z X hZ hX, hcr Z X Y hX hY,
    htrace X Y Z hX hY hZ, htrace Y Z X hY hZ hX, htrace Z X Y hZ hX hY] at hh
  exact hh

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ricciFlow_curvature_derivative_scalar_heat_identity
    {I : Set ℝ} (F : RicciFlow n M I) {t : ℝ} (ht : t ∈ interior I)
    (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun (s : ℝ) (y : M) => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y ((F.metric s).inner y)
    let a := fun (s : ℝ) (y : M) (i j : Fin n) =>
      ((G s y).inverse (EuclideanSpace.proj j)) i
    let N := fun s (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).connection Q y (P y)
    let R := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).curvatureOnFields A B C y
    let K := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N s P (R s A B C) y - R s (N s P A) B C y -
        R s A (N s P B) C y - R s A B (N s P C) y
    let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N t P (K t Q A B C) y - K t (N t P Q) A B C y -
        K t Q (N t P A) B C y - K t Q A (N t P B) C y - K t Q A B (N t P C) y
    let J := fun (P Q A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
      N t P (H Q A B C W) y - H (N t P Q) A B C W y -
        H Q (N t P A) B C W y - H Q A (N t P B) C W y -
        H Q A B (N t P C) W y - H Q A B C (N t P W) y
    let W := fun s y (α β : Fin 4 → Fin n) => ∏ r, a s y (α r) (β r)
    let pair := fun s (y : M)
        (v w : (Fin 4 → Fin n) → TangentSpace (𝓡 n) y) =>
      ∑ α, ∑ β, W s y α β * (F.metric s).inner y (v α) (w β)
    let k := fun s (α : Fin 4 → Fin n) =>
      K s (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
    let k1 := fun i (α : Fin 4 → Fin n) =>
      H (E i) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
    let k2 := fun i j (α : Fin 4 → Fin n) =>
      J (E i) (E j) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
    let q := fun s y => pair s y (fun α => k s α y) (fun α => k s α y)
    let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
      mvfderiv (𝓡 n) f y (P y)
    let raised := fun i => e.symmL ℝ x ((G t x).inverse (EuclideanSpace.proj i))
    deriv (fun s => q s x) t -
        (∑ i, ∑ j, a t x i j *
          (d (E i) (d (E j) (q t)) x - d (N t (E i) (E j)) (q t) x)) =
      -2 * (∑ i, ∑ j, a t x i j *
        pair t x (fun α => k1 i α x) (fun α => k1 j α x)) +
      2 * pair t x
        (fun α => deriv (fun s => k s α x) t - ∑ i, ∑ j, a t x i j • k2 i j α x)
        (fun α => k t α x) -
      2 * (∑ α, ∑ β, W t x α β * (F.connection t).ricci x (k t α x) (k t β x)) +
      ∑ α, ∑ β, ∑ r : Fin 4,
        2 * (F.connection t).ricci x (raised (β r)) (raised (α r)) *
          (∏ s ∈ Finset.univ.erase r, a t x (α s) (β s)) *
            (F.metric t).inner x (k t α x) (k t β x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun (s : ℝ) (y : M) => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y ((F.metric s).inner y)
  let a := fun (s : ℝ) (y : M) (i j : Fin n) =>
    ((G s y).inverse (EuclideanSpace.proj j)) i
  let N := fun s (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).connection Q y (P y)
  let R := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).curvatureOnFields A B C y
  let K := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N s P (R s A B C) y - R s (N s P A) B C y -
      R s A (N s P B) C y - R s A B (N s P C) y
  let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N t P (K t Q A B C) y - K t (N t P Q) A B C y -
      K t Q (N t P A) B C y - K t Q A (N t P B) C y - K t Q A B (N t P C) y
  let J := fun (P Q A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
    N t P (H Q A B C W) y - H (N t P Q) A B C W y -
      H Q (N t P A) B C W y - H Q A (N t P B) C W y -
      H Q A B (N t P C) W y - H Q A B C (N t P W) y
  let W := fun s y (α β : Fin 4 → Fin n) => ∏ r, a s y (α r) (β r)
  let pair := fun s (y : M)
      (v w : (Fin 4 → Fin n) → TangentSpace (𝓡 n) y) =>
    ∑ α, ∑ β, W s y α β * (F.metric s).inner y (v α) (w β)
  let k := fun s (α : Fin 4 → Fin n) =>
    K s (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
  let k1 := fun i (α : Fin 4 → Fin n) =>
    H (E i) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
  let k2 := fun i j (α : Fin 4 → Fin n) =>
    J (E i) (E j) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
  let q := fun s y => pair s y (fun α => k s α y) (fun α => k s α y)
  let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
    mvfderiv (𝓡 n) f y (P y)
  let raised := fun i => e.symmL ℝ x ((G t x).inverse (EuclideanSpace.proj i))
  let dotk := fun α => deriv (fun s => k s α x) t
  let diff := fun α => ∑ i, ∑ j, a t x i j • k2 i j α x
  let G2 := ∑ i, ∑ j, a t x i j *
    pair t x (fun α => k1 i α x) (fun α => k1 j α x)
  let C2 := ∑ i, ∑ j, a t x i j *
    pair t x (fun α => k2 i j α x) (fun α => k t α x)
  let outputRate := ∑ α, ∑ β,
    W t x α β * (F.connection t).ricci x (k t α x) (k t β x)
  let inputRate := ∑ α, ∑ β, ∑ r : Fin 4,
      2 * (F.connection t).ricci x (raised (β r)) (raised (α r)) *
        (∏ s ∈ Finset.univ.erase r, a t x (α s) (β s)) *
          (F.metric t).inner x (k t α x) (k t β x)
  have htime := (hasDerivAt_ricciFlow_curvature_derivative_squared_norm_frame
    F ht x0 hx).deriv
  change deriv (fun s => q s x) t =
    2 * pair t x dotk (fun α => k t α x) - 2 * outputRate + inputRate at htime
  have hspace := curvature_derivative_bochner_local_frame (F.connection t) x0 hx
  change (∑ i, ∑ j, a t x i j *
      (d (E i) (d (E j) (q t)) x - d (N t (E i) (E j)) (q t) x)) =
    2 * G2 + 2 * C2 at hspace
  have hlinear {A B Z : Type} [Fintype A] [Fintype B]
      [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (L : Z →L[ℝ] Z →L[ℝ] ℝ) (w : A → A → ℝ) (c : B → B → ℝ)
      (v z : A → Z) (h : B → B → A → Z) :
      (∑ α, ∑ β, w α β * L (v α - ∑ i, ∑ j, c i j • h i j α) (z β)) =
        (∑ α, ∑ β, w α β * L (v α) (z β)) -
        ∑ i, ∑ j, c i j * (∑ α, ∑ β, w α β * L (h i j α) (z β)) := by
    simp only [map_sub, map_sum, map_smul, sub_apply, sum_apply, smul_apply,
      smul_eq_mul, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1
    calc
      _ = ∑ α, ∑ i, ∑ β, ∑ j, w α β * (c i j * L (h i j α) (z β)) := by
        apply Finset.sum_congr rfl
        intro α _
        exact Finset.sum_comm
      _ = ∑ i, ∑ α, ∑ β, ∑ j, w α β * (c i j * L (h i j α) (z β)) :=
        Finset.sum_comm
      _ = ∑ i, ∑ α, ∑ j, ∑ β, w α β * (c i j * L (h i j α) (z β)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro α _
        exact Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ α, ∑ β, w α β * (c i j * L (h i j α) (z β)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        ring
  have hdiff : pair t x (fun α => dotk α - diff α) (fun α => k t α x) =
      pair t x dotk (fun α => k t α x) - C2 :=
    hlinear (A := Fin 4 → Fin n) (B := Fin n) (Z := TangentSpace (𝓡 n) x)
      ((F.metric t).inner x) (W t x) (a t x) dotk
      (fun α => k t α x) (fun i j α => k2 i j α x)
  change deriv (fun s => q s x) t -
      (∑ i, ∑ j, a t x i j *
        (d (E i) (d (E j) (q t)) x - d (N t (E i) (E j)) (q t) x)) =
    -2 * G2 + 2 * pair t x (fun α => dotk α - diff α) (fun α => k t α x) -
      2 * outputRate + inputRate
  rw [htime, hspace, hdiff]
  ring

set_option synthInstance.maxHeartbeats 200000 in

theorem ricciFlow_connection_variation_tangentNorm_le_curvature_derivative_energy
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (X Y : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    {x : M} (hx : x ∈ U) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let g := F.metric t
    let D := F.connection t
    let b := g.orthonormalBasis x
    let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.connection Q y (P y)
    let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      D.curvatureOnFields A B C y
    let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (R A B C) y - R (N P A) B C y -
        R A (N P B) C y - R A B (N P C) y
    let kb := fun (γ : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) =>
      K (E (γ 0)) (E (γ 1)) (E (γ 2)) (E (γ 3)) x
    g.tangentNorm x (deriv (fun s => (F.connection s).connection Y x (X x)) t) ≤
      3 * (n : ℝ) * Real.sqrt (∑ γ, g.inner x (kb γ) (kb γ)) *
        g.tangentNorm x (X x) * g.tangentNorm x (Y x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let g := F.metric t
  let D := F.connection t
  let V := EuclideanSpace ℝ (Fin n)
  let Btime := deriv (fun s => (F.connection s).connection Y x (X x)) t
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  let E := fun i : ι => FiberBundle.extend V (b i)
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection Q y (P y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (R A B C) y - R (N P A) B C y -
      R A (N P B) C y - R A B (N P C) y
  let kb := fun γ : Fin 4 → ι => K (E (γ 0)) (E (γ 1)) (E (γ 2)) (E (γ 3)) x
  let q := ∑ γ : Fin 4 → ι, g.inner x (kb γ) (kb γ)
  let C := 3 * (n : ℝ) * Real.sqrt q * g.tangentNorm x (X x) * g.tangentNorm x (Y x)
  change g.tangentNorm x Btime ≤ C
  let e := trivializationAt V (TangentSpace (𝓡 n)) x
  let W := U ∩ e.baseSet
  have hW : IsOpen W := hU.inter e.open_baseSet
  have hxW : x ∈ W := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let S := fun P : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) W
  have hXs : S X := hX.mono inter_subset_left
  have hYs : S Y := hY.mono inter_subset_left
  have hExt (v : TangentSpace (𝓡 n) x) : S (FiberBundle.extend V v) := by
    have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun _y : M => (e ⟨x, v⟩).2) e.baseSet := contMDiffOn_const
    have hec : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun y => (e ⟨y, FiberBundle.extend V v y⟩).2) e.baseSet := by
      apply hc.congr
      intro y hy
      change (e ⟨y, e.symm y (e ⟨x, v⟩).2⟩).2 = (e ⟨x, v⟩).2
      simpa only using congrArg Prod.snd (e.apply_mk_symm hy (e ⟨x, v⟩).2)
    have hext : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
        (T% (FiberBundle.extend V v)) e.baseSet := by
      intro y hy
      rw [e.contMDiffWithinAt_section _ hy]
      exact hec y hy
    exact hext.mono inter_subset_right
  let Z := FiberBundle.extend V Btime
  have hZ : S Z := hExt Btime
  have hZx : Z x = Btime := FiberBundle.extend_apply_self V Btime
  have hE (i : ι) : S (E i) := hExt (b i)
  have hEx (i : ι) : E i x = b i := FiberBundle.extend_apply_self V (b i)
  have hb (i : ι) : g.tangentNorm x (b i) = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Real.sqrt (inner ℝ (b i) (b i)) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
    norm_num
  have hself (v : TangentSpace (𝓡 n) x) :
      g.inner x v v = g.tangentNorm x v ^ 2 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hv : 0 ≤ g.inner x v v := by
      change 0 ≤ inner ℝ v v
      exact real_inner_self_nonneg
    exact (Real.sq_sqrt hv).symm
  have hdim : Fintype.card ι = n := by
    simp only [ι, Fintype.card_fin]
    rw [VectorBundle.finrank_eq ℝ V (TangentSpace (𝓡 n)) x,
      finrank_euclideanSpace_fin]
  have hpair (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) (i : ι) :
      |g.inner x (K P A B C x) (b i)| ≤ Real.sqrt q *
        g.tangentNorm x (P x) * g.tangentNorm x (A x) *
          g.tangentNorm x (B x) * g.tangentNorm x (C x) := by
    have hh := abs_curvature_derivative_pairing_le_orthonormal_energy
      D hW P A B C hP hA hB hC hxW (b i)
    change |g.inner x (K P A B C x) (b i)| ≤ Real.sqrt q *
      g.tangentNorm x (P x) * g.tangentNorm x (A x) *
        g.tangentNorm x (B x) * g.tangentNorm x (C x) * g.tangentNorm x (b i) at hh
    simpa only [hb, mul_one] using hh
  let c := Real.sqrt q * g.tangentNorm x (X x) *
    g.tangentNorm x (Y x) * g.tangentNorm x Btime
  have hfirst (i : ι) : |g.inner x (K X (E i) Y Z x) (b i)| ≤ c := by
    calc
      _ ≤ Real.sqrt q * g.tangentNorm x (X x) * g.tangentNorm x (E i x) *
          g.tangentNorm x (Y x) * g.tangentNorm x (Z x) :=
        hpair X (E i) Y Z hXs (hE i) hYs hZ i
      _ = c := by rw [hEx, hb, hZx, mul_one]
  have hsecond (i : ι) : |g.inner x (K Y (E i) Z X x) (b i)| ≤ c := by
    calc
      _ ≤ Real.sqrt q * g.tangentNorm x (Y x) * g.tangentNorm x (E i x) *
          g.tangentNorm x (Z x) * g.tangentNorm x (X x) :=
        hpair Y (E i) Z X hYs (hE i) hZ hXs i
      _ = c := by rw [hEx, hb, hZx, mul_one]; dsimp only [c]; ring
  have hthird (i : ι) : |g.inner x (K Z (E i) X Y x) (b i)| ≤ c := by
    calc
      _ ≤ Real.sqrt q * g.tangentNorm x (Z x) * g.tangentNorm x (E i x) *
          g.tangentNorm x (X x) * g.tangentNorm x (Y x) :=
        hpair Z (E i) X Y hZ (hE i) hXs hYs i
      _ = c := by rw [hEx, hb, hZx, mul_one]; dsimp only [c]; ring
  have hsum (f : ι → ℝ) (hf : ∀ i, |f i| ≤ c) :
      |∑ i, f i| ≤ (n : ℝ) * c := by
    calc
      _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, c := Finset.sum_le_sum (fun i _ => hf i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hdim, nsmul_eq_mul]
  let a1 := ∑ i : ι, g.inner x (K X (E i) Y Z x) (b i)
  let a2 := ∑ i : ι, g.inner x (K Y (E i) Z X x) (b i)
  let a3 := ∑ i : ι, g.inner x (K Z (E i) X Y x) (b i)
  have h1 : |a1| ≤ (n : ℝ) * c := hsum _ hfirst
  have h2 : |a2| ≤ (n : ℝ) * c := hsum _ hsecond
  have h3 : |a3| ≤ (n : ℝ) * c := hsum _ hthird
  have hrate := ricciFlow_connection_variation_pairing_eq_curvature_derivative_trace
    F ht hW X Y Z hXs hYs hZ hxW
  change g.inner x Btime (Z x) = -a1 - a2 + a3 at hrate
  rw [hZx] at hrate
  have htriangle (p q r : ℝ) : -p - q + r ≤ |p| + |q| + |r| := by
    linarith only [neg_le_abs p, neg_le_abs q, le_abs_self r]
  have hsq : g.tangentNorm x Btime ^ 2 ≤ C * g.tangentNorm x Btime := by
    calc
      _ = g.inner x Btime Btime := (hself Btime).symm
      _ = -a1 - a2 + a3 := hrate
      _ ≤ |a1| + |a2| + |a3| := htriangle a1 a2 a3
      _ ≤ (n : ℝ) * c + (n : ℝ) * c + (n : ℝ) * c :=
        add_le_add (add_le_add h1 h2) h3
      _ = _ := by dsimp only [c, C]; ring
  have hC : 0 ≤ C := by dsimp only [C, RiemannianMetric.tangentNorm]; positivity
  by_cases hzero : g.tangentNorm x Btime = 0
  · rw [hzero]
    exact hC
  · have hpos : 0 < g.tangentNorm x Btime :=
      lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hzero)
    exact (mul_le_mul_iff_right₀ hpos).mp
      (by simpa only [pow_two, mul_comm C] using hsq)

set_option synthInstance.maxHeartbeats 200000 in

theorem exists_ricciFlow_connection_variation_bilinearMap
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    ∃ B : TangentSpace (𝓡 n) x →ₗ[ℝ]
        TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x,
      ∀ {U : Set M}, IsOpen U →
      ∀ (X Y : (y : M) → TangentSpace (𝓡 n) y),
        ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U →
        ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U →
        x ∈ U → B (X x) (Y x) =
          deriv (fun s => (F.connection s).connection Y x (X x)) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let Rate := fun (X Y : (y : M) → TangentSpace (𝓡 n) y) =>
    deriv (fun s => (F.connection s).connection Y x (X x)) t
  let g := F.metric t
  let D := F.connection t
  let V := EuclideanSpace ℝ (Fin n)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_derivative_quadrilinearMap D x
  let sigma := fun (u v w : TangentSpace (𝓡 n) x) =>
    -(∑ i : ι, g.inner x (T u (b i) v w) (b i)) -
      (∑ i : ι, g.inner x (T v (b i) w u) (b i)) +
      ∑ i : ι, g.inner x (T w (b i) u v) (b i)
  let B0 := fun (u v : TangentSpace (𝓡 n) x) =>
    ∑ o : ι, sigma u v (b o) • b o
  have hsadd1 (u u' v w : TangentSpace (𝓡 n) x) :
      sigma (u + u') v w = sigma u v w + sigma u' v w := by
    simp only [sigma, map_add, LinearMap.add_apply, add_apply,
      Finset.sum_add_distrib]
    ring
  have hssmul1 (c : ℝ) (u v w : TangentSpace (𝓡 n) x) :
      sigma (c • u) v w = c * sigma u v w := by
    simp only [sigma, map_smul, LinearMap.smul_apply, smul_apply,
      smul_eq_mul, ← Finset.mul_sum]
    ring
  have hsadd2 (u v v' w : TangentSpace (𝓡 n) x) :
      sigma u (v + v') w = sigma u v w + sigma u v' w := by
    simp only [sigma, map_add, LinearMap.add_apply, add_apply,
      Finset.sum_add_distrib]
    ring
  have hssmul2 (c : ℝ) (u v w : TangentSpace (𝓡 n) x) :
      sigma u (c • v) w = c * sigma u v w := by
    simp only [sigma, map_smul, LinearMap.smul_apply, smul_apply,
      smul_eq_mul, ← Finset.mul_sum]
    ring
  let B := LinearMap.mk₂ ℝ B0
    (by
      intro u u' v
      simp only [B0, hsadd1, add_smul, Finset.sum_add_distrib])
    (by
      intro c u v
      simp only [B0, hssmul1, mul_smul, Finset.smul_sum])
    (by
      intro u v v'
      simp only [B0, hsadd2, add_smul, Finset.sum_add_distrib])
    (by
      intro c u v
      simp only [B0, hssmul2, mul_smul, Finset.smul_sum])
  refine ⟨B, ?_⟩
  intro U hU X Y hX hY hx
  change B0 (X x) (Y x) = Rate X Y
  let e := trivializationAt V (TangentSpace (𝓡 n)) x
  let E := fun i : ι => FiberBundle.extend V (b i)
  let W := U ∩ e.baseSet
  have hW : IsOpen W := hU.inter e.open_baseSet
  have hxW : x ∈ W := ⟨hx, FiberBundle.mem_baseSet_trivializationAt' x⟩
  let S := fun P : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) W
  have hXs : S X := hX.mono inter_subset_left
  have hYs : S Y := hY.mono inter_subset_left
  have hE (i : ι) : S (E i) := by
    have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun _y : M => (e ⟨x, b i⟩).2) e.baseSet := contMDiffOn_const
    have hec : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun y => (e ⟨y, E i y⟩).2) e.baseSet := by
      apply hc.congr
      intro y hy
      change (e ⟨y, e.symm y (e ⟨x, b i⟩).2⟩).2 = (e ⟨x, b i⟩).2
      simpa only using congrArg Prod.snd (e.apply_mk_symm hy (e ⟨x, b i⟩).2)
    have hext : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
        (T% (E i)) e.baseSet := by
      intro y hy
      rw [e.contMDiffWithinAt_section _ hy]
      exact hec y hy
    exact hext.mono inter_subset_right
  have hEx (i : ι) : E i x = b i := FiberBundle.extend_apply_self V (b i)
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection Q y (P y)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let K := fun (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (R A B C) y - R (N P A) B C y -
      R A (N P B) C y - R A B (N P C) y
  have hK (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) :
      K P A B C x = T (P x) (A x) (B x) (C x) :=
    (hT hW P A B C hP hA hB hC hxW).symm
  have hpair (o : ι) :
      g.inner x (Rate X Y) (b o) = sigma (X x) (Y x) (b o) := by
    have hh := ricciFlow_connection_variation_pairing_eq_curvature_derivative_trace
      F ht hW X Y (E o) hXs hYs (hE o) hxW
    change g.inner x (Rate X Y) (E o x) =
      -(∑ i : ι, g.inner x (K X (E i) Y (E o) x) (b i)) -
        (∑ i : ι, g.inner x (K Y (E i) (E o) X x) (b i)) +
        ∑ i : ι, g.inner x (K (E o) (E i) X Y x) (b i) at hh
    simp_rw [hK X (E _) Y (E o) hXs (hE _) hYs (hE o),
      hK Y (E _) (E o) X hYs (hE _) (hE o) hXs,
      hK (E o) (E _) X Y (hE o) (hE _) hXs hYs, hEx] at hh
    exact hh
  have hrepr (o : ι) :
      b.repr (Rate X Y) o = sigma (X x) (Y x) (b o) := by
    rw [OrthonormalBasis.repr_apply_apply]
    change g.inner x (b o) (Rate X Y) = sigma (X x) (Y x) (b o)
    rw [g.symm, hpair]
  calc
    B0 (X x) (Y x) = ∑ o : ι, b.repr (Rate X Y) o • b o := by
      simp only [B0, hrepr]
    _ = Rate X Y := b.sum_repr (Rate X Y)

end PoincareConjecture.Proofs.M03

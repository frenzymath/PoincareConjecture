import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Connection.ConnectionVariation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Connection.SpacetimePairings
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries











set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

set_option maxHeartbeats 4000000 in

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_curvatureTensor_first_variation (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s ↦ (F.connection s).curvatureTensor x u v w z)
      (-2 * (F.connection t).ricci x ((F.connection t).curvature x u v z) w -
        (F.connection t).iteratedCovariantTensorDerivative (F.connection t).ricciEvaluation
          2 x ![u, v, z, w] -
        (F.connection t).iteratedCovariantTensorDerivative (F.connection t).ricciEvaluation
          2 x ![u, z, v, w] +
        (F.connection t).iteratedCovariantTensorDerivative (F.connection t).ricciEvaluation
          2 x ![u, w, v, z] +
        (F.connection t).iteratedCovariantTensorDerivative (F.connection t).ricciEvaluation
          2 x ![v, u, z, w] +
        (F.connection t).iteratedCovariantTensorDerivative (F.connection t).ricciEvaluation
          2 x ![v, z, u, w] -
        (F.connection t).iteratedCovariantTensorDerivative (F.connection t).ricciEvaluation
          2 x ![v, w, u, z]) t := by
  classical
  let g := F.metric t
  let D := F.connection t
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let K := D.covariantTensorDerivative D.ricciEvaluation
  let K2 := D.covariantTensorDerivative K
  let L : (y : M) → TangentSpace (𝓡 n) y → TangentSpace (𝓡 n) y →
      TangentSpace (𝓡 n) y → ℝ := fun y a b c ↦
    -K y ![a, b, c] - K y ![b, a, c] + K y ![c, a, b]
  have hRic : IsSmoothCovariantTensor D.ricciEvaluation :=
    isSmoothCovariantTensor_ricciEvaluation D
  have hK : IsSmoothCovariantTensor K :=
    isSmoothCovariantTensor_covariantTensorDerivative D hRic
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let U := e.baseSet
  have hU : IsOpen U := e.open_baseSet
  have hx : x ∈ U := FiberBundle.mem_baseSet_trivializationAt' x
  let V : Fin 4 → (y : M) → TangentSpace (𝓡 n) y :=
    ![FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u,
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v,
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) z,
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w]
  have hV (i : Fin 4) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (V i)) U := by
    fin_cases i
    · exact contMDiffOn_extend_baseSet u
    · exact contMDiffOn_extend_baseSet v
    · exact contMDiffOn_extend_baseSet z
    · exact contMDiffOn_extend_baseSet w
  let C (s : ℝ) (i j : Fin 4) := fun y ↦ (F.connection s).connection (V j) y (V i y)
  have hCs (s : ℝ) (i j : Fin 4) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (C s i j)) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings (F.metric s) (C s i j)
    intro a
    let q := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hyq : y ∈ U ∩ q.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    exact (contMDiffOn_connection_pairing (F.connection s) (hU.inter q.open_baseSet)
      ((hV i).mono inter_subset_left) ((hV j).mono inter_subset_left)
      ((contMDiffOn_extend_baseSet a).mono inter_subset_right)).contMDiffAt
        ((hU.inter q.open_baseSet).mem_nhds hyq)
  have hclm {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
      [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
      {H : ℝ → A →L[ℝ] B}
      (hH : ∀ a, DifferentiableAt ℝ (fun s ↦ H s a) t) :
      DifferentiableAt ℝ H t := by
    let d := Module.finrank ℝ A
    have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
    let e1 := ContinuousLinearEquiv.ofFinrankEq hd
    let e2 := (e1.arrowCongr (1 : B ≃L[ℝ] B)).trans (ContinuousLinearEquiv.piRing (Fin d))
    have hc : DifferentiableAt ℝ (fun s ↦ e2 (H s)) t :=
      differentiableAt_pi.mpr fun _ ↦ hH _
    have he := e2.symm.toContinuousLinearMap.differentiableAt.comp t hc
    have heq : (fun s ↦ e2.symm (e2 (H s))) = H := by
      funext s
      exact e2.symm_apply_apply (H s)
    have he' : DifferentiableAt ℝ (fun s ↦ e2.symm (e2 (H s))) t := by
      simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe] using! he
    rwa [heq] at he'
  have hCt {P Q : (y : M) → TangentSpace (𝓡 n) y}
      (hP : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
      (hQ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U)
      {y : M} (hy : y ∈ U) :
      DifferentiableAt ℝ (fun s ↦ (F.connection s).connection Q y (P y)) t := by
    let E := TangentSpace (𝓡 n) y
    let : FiniteDimensional ℝ E := VectorBundle.finiteDimensional ℝ
      (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : M → Type _) y
    let : CompleteSpace E := FiniteDimensional.complete ℝ E
    let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
    let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
    let H : ℝ → E →L[ℝ] ℝ := fun s ↦ g.inner y ((F.connection s).connection Q y (P y))
    have hHd : DifferentiableAt ℝ H t := by
      apply hclm (A := E) (B := ℝ) (H := H)
      intro a
      let q := trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) y
      have hyq : y ∈ U ∩ q.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
      have ha := hasDerivAt_connection_pairing F (hU.inter q.open_baseSet)
        (hP.mono inter_subset_left) (hQ.mono inter_subset_left)
        ((contMDiffOn_extend_baseSet (n := n) (M := M) (x := y) a).mono inter_subset_right)
        ht hyq
      simpa only [FiberBundle.extend_apply_self] using! ha.differentiableAt
    let inv : (E →L[ℝ] ℝ) →L[ℝ] E :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hid : DifferentiableAt ℝ (fun k : E →L[ℝ] ℝ ↦ inv k) (H t) :=
      inv.differentiableAt
    have hd : DifferentiableAt ℝ (fun s ↦ inv (H s)) t := hid.comp t hHd
    have heq : (fun s ↦ inv (H s)) =
        (fun s ↦ (F.connection s).connection Q y (P y)) := by
      funext s
      exact (InnerProductSpace.toDual ℝ E).symm_apply_apply _
    rwa [heq] at hd
  have hVelocity {P Q : (y : M) → TangentSpace (𝓡 n) y}
      (hP : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
      (hQ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U)
      {y : M} (hy : y ∈ U) (a : TangentSpace (𝓡 n) y) :
      g.inner y (deriv (fun s ↦ (F.connection s).connection Q y (P y)) t) a =
        L y (P y) (Q y) a := by
    let E := TangentSpace (𝓡 n) y
    let q := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hyq : y ∈ U ∩ q.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    have ha := hasDerivAt_connection_pairing F (hU.inter q.open_baseSet)
      (hP.mono inter_subset_left) (hQ.mono inter_subset_left)
      ((contMDiffOn_extend_baseSet (n := n) (M := M) (x := y) a).mono inter_subset_right)
      ht hyq
    have hd : HasDerivAt (fun s ↦ g.inner y ((F.connection s).connection Q y (P y)) a)
        (g.inner y (deriv (fun s ↦ (F.connection s).connection Q y (P y)) t) a) t := by
      have hb := (hCt hP hQ hy).hasDerivAt
      have he := ((g.inner y).flip a).hasFDerivAt.comp_hasDerivAt t hb
      simpa only [ContinuousLinearMap.flip_apply] using! he
    simp only [FiberBundle.extend_apply_self] at ha
    exact hd.unique ha

  have hInnerTime (y : M) {p q : ℝ → TangentSpace (𝓡 n) y}
      (hp : DifferentiableAt ℝ p t) (hq : DifferentiableAt ℝ q t) :
      HasDerivAt (fun s ↦ (F.metric s).inner y (p s) (q s))
        (-2 * D.ricci y (p t) (q t) + g.inner y (deriv p t) (q t) +
          g.inner y (p t) (deriv q t)) t := by
    let E := TangentSpace (𝓡 n) y
    let : FiniteDimensional ℝ E := VectorBundle.finiteDimensional ℝ
      (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : M → Type _) y
    let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
    let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
    let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
    let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
    let G : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ (F.metric s).inner y
    have hg (a b : E) : HasDerivAt (fun s ↦ G s a b) (-2 * D.ricci y a b) t :=
      (F.equation t (interior_subset ht) y a b).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)
    have hGd : DifferentiableAt ℝ G t := by
      apply hclm (A := E) (B := E →L[ℝ] ℝ) (H := G)
      intro a
      apply hclm (A := E) (B := ℝ) (H := fun s ↦ G s a)
      intro b
      exact (hg a b).differentiableAt
    have hGtime : HasDerivAt G (deriv G t) t := hGd.hasDerivAt
    have hG' (a b : E) : deriv G t a b = -2 * D.ricci y a b := by
      have he : HasDerivAt (fun s ↦ G s a b) (deriv G t a b) t := by
        simpa only [map_zero, zero_apply, zero_add, add_zero] using!
          (hGtime.clm_apply (F := E) (G := E →L[ℝ] ℝ)
            (hasDerivAt_const t a)).clm_apply (F := E) (G := ℝ) (hasDerivAt_const t b)
      exact he.unique (hg a b)
    have hp' : HasDerivAt p (deriv p t) t := hp.hasDerivAt
    have hq' : HasDerivAt q (deriv q t) t := hq.hasDerivAt
    simpa only [add_apply, hG', G] using!
      (hGtime.clm_apply (F := E) (G := E →L[ℝ] ℝ) hp').clm_apply
        (F := E) (G := ℝ) hq'
  have hPair {P Q : (y : M) → TangentSpace (𝓡 n) y}
      (hP : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
      (hQ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U)
      {y : M} (hy : y ∈ U) (a : TangentSpace (𝓡 n) y) :
      HasDerivAt (fun s ↦ (F.metric s).inner y ((F.connection s).connection Q y (P y)) a)
        (-2 * D.ricci y (D.connection Q y (P y)) a + L y (P y) (Q y) a) t := by
    simpa only [deriv_const, map_zero, add_zero, hVelocity hP hQ hy a] using!
      hInnerTime y (hCt hP hQ hy) (differentiableAt_const a)
  have hCross (i j k l : Fin 4) :
      HasDerivAt (fun s ↦ (F.metric s).inner x (C s i j x) (C s k l x))
        (-2 * D.ricci x (C t i j x) (C t k l x) +
          L x (V i x) (V j x) (C t k l x) +
          L x (V k x) (V l x) (C t i j x)) t := by
    have hd := hInnerTime x (hCt (hV i) (hV j) hx) (hCt (hV k) (hV l) hx)
    apply hd.congr_deriv
    rw [hVelocity (hV i) (hV j) hx, g.symm x (C t i j x),
      hVelocity (hV k) (hV l) hx]
  let B := VectorField.mlieBracket (𝓡 n) (V 0) (V 1)
  have hB : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U := by
    intro y hy
    let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
      apply IsManifold.of_le (n := (↑(⊤ : ℕ∞) : ℕ∞ω))
      simpa [minSmoothness_eq_infty] using
        (minSmoothness_monotone (𝕜 := ℝ)
          (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)))
    let : IsManifold (𝓡 n) (∞ + 1) M := by
      simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
    exact (((hV 0).contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
      (m := ⊤) (n := ⊤) ((hV 1).contMDiffAt (hU.mem_nhds hy)) (by simp)).contMDiffWithinAt
  let P (s : ℝ) (i j k : Fin 4) := fun y ↦
    (F.metric s).inner y (C s i j y) (V k y)
  let S (i j k : Fin 4) := fun y ↦
    -2 * D.ricci y (C t i j y) (V k y) + L y (V i y) (V j y) (V k y)
  have hMixed (i j k l : Fin 4) :
      HasDerivAt (fun s ↦ mvfderiv (𝓡 n) (P s j k l) x (V i x))
        (mvfderiv (𝓡 n) (S j k l) x (V i x)) t :=
    hasDerivAt_mvfderiv_time hU
      (contMDiffOn_flow_connection_pairing F hU (hV j) (hV k) (hV l)) ht hx
      (fun y hy ↦ hPair (hV j) (hV k) hy (V l y)) (V i x)
  have hVd (i : Fin 4) := ((hV i).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hCd (s : ℝ) (i j : Fin 4) :=
    ((hCs s i j).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hScalar (s : ℝ) :
      (F.metric s).inner x ((F.connection s).curvatureOnFields (V 0) (V 1) (V 2) x) (V 3 x) =
        mvfderiv (𝓡 n) (P s 1 2 3) x (V 0 x) -
        mvfderiv (𝓡 n) (P s 0 2 3) x (V 1 x) -
        (F.metric s).inner x (C s 1 2 x) (C s 0 3 x) +
        (F.metric s).inner x (C s 0 2 x) (C s 1 3 x) -
        (F.metric s).inner x ((F.connection s).connection (V 2) x (B x)) (V 3 x) := by
    have h1 := metric_derivative_pairing (F.connection s) (V 0) (hCd s 1 2) (hVd 3)
    have h2 := metric_derivative_pairing (F.connection s) (V 1) (hCd s 0 2) (hVd 3)
    simp only [LeviCivitaData.curvatureOnFields, map_sub, sub_apply]
    dsimp only [P, C, B] at h1 h2 ⊢
    linarith only [h1, h2]
  have hdScalar := ((((hMixed 0 1 2 3).sub (hMixed 1 0 2 3)).sub
    (hCross 1 2 0 3)).add (hCross 0 2 1 3)).sub (hPair hB (hV 2) hx (V 3 x))
  have hdActual := hdScalar.congr_of_eventuallyEq (Eventually.of_forall hScalar)

  have hRicDiff {P Q R : (y : M) → TangentSpace (𝓡 n) y}
      (hP : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
      (hQ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U)
      (hR : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% R) U) :
      mvfderiv (𝓡 n) (fun y ↦ D.ricci y (Q y) (R y)) x (P x) =
        K x ![P x, Q x, R x] + D.ricci x (D.connection Q x (P x)) (R x) +
          D.ricci x (Q x) (D.connection R x (P x)) := by
    have he := covariantTensorDerivativeOnFields_eq D hRic hU (X := ![P, Q, R])
      (by intro i; fin_cases i; exact hP; exact hQ; exact hR) hx
    simp only [covariantTensorDerivativeOnFields, Fin.sum_univ_succ] at he
    change mvfderiv (𝓡 n) (fun y ↦ D.ricci y (Q y) (R y)) x (P x) -
      (D.ricci x (D.connection Q x (P x)) (R x) +
        (D.ricci x (Q x) (D.connection R x (P x)) + 0)) = K x ![P x, Q x, R x] at he
    linarith only [he]
  have hKsym (a b c : TangentSpace (𝓡 n) x) : K x ![a, b, c] = K x ![a, c, b] := by
    let Ea := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
    let Eb := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
    let Ec := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) c
    have hEa : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% Ea) U := contMDiffOn_extend_baseSet a
    have hEb : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% Eb) U := contMDiffOn_extend_baseSet b
    have hEc : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% Ec) U := contMDiffOn_extend_baseSet c
    have heq : (fun y ↦ D.ricci y (Eb y) (Ec y)) = (fun y ↦ D.ricci y (Ec y) (Eb y)) :=
      funext fun y ↦ ricci_symm D y (Eb y) (Ec y)
    have h1 := hRicDiff hEa hEb hEc
    have h2 := hRicDiff hEa hEc hEb
    rw [heq] at h1
    simp only [Ea, Eb, Ec, FiberBundle.extend_apply_self] at h1 h2
    rw [ricci_symm D x b (D.connection Ec x a)] at h1
    rw [ricci_symm D x c (D.connection Eb x a)] at h2
    linarith only [h1, h2]
  have hLadd (a b c : TangentSpace (𝓡 n) x) :
      L x a b c + L x a c b = -2 * K x ![a, b, c] := by
    dsimp only [L]
    rw [hKsym a c b]
    ring
  have hLsub (a b c d : TangentSpace (𝓡 n) x) :
      L x (a - b) c d = L x a c d - L x b c d := by
    obtain ⟨T, hT⟩ := hK.1 x
    have hu0 (a b c z : TangentSpace (𝓡 n) x) : Function.update ![a, b, c] 0 z = ![z, b, c] := by
      ext i
      fin_cases i <;> simp [Function.update]
    have hu1 (a b c z : TangentSpace (𝓡 n) x) : Function.update ![a, b, c] 1 z = ![a, z, c] := by
      ext i
      fin_cases i <;> simp [Function.update]
    have h0 : T ![a - b, c, d] = T ![a, c, d] - T ![b, c, d] := by
      simpa only [hu0] using T.map_update_sub ![a, c, d] 0 a b
    have h1 : T ![c, a - b, d] = T ![c, a, d] - T ![c, b, d] := by
      simpa only [hu1] using T.map_update_sub ![c, a, d] 1 a b
    have h2 : T ![d, a - b, c] = T ![d, a, c] - T ![d, b, c] := by
      simpa only [hu1] using T.map_update_sub ![d, a, c] 1 a b
    simp only [L, hT, h0, h1, h2]
    ring
  have hKDiff (i j k l : Fin 4) :
      mvfderiv (𝓡 n) (fun y ↦ K y ![V j y, V k y, V l y]) x (V i x) =
        K2 x ![V i x, V j x, V k x, V l x] +
          K x ![C t i j x, V k x, V l x] +
          K x ![V j x, C t i k x, V l x] + K x ![V j x, V k x, C t i l x] := by
    have he := covariantTensorDerivativeOnFields_eq D (k := 3) (T := K) hK hU
      (X := ![V i, V j, V k, V l])
      (by intro a; fin_cases a; exact hV i; exact hV j; exact hV k; exact hV l) hx
    have hpoint : (fun a : Fin 4 ↦ ![V i, V j, V k, V l] a x) =
        ![V i x, V j x, V k x, V l x] := by
      funext a
      fin_cases a <;> rfl
    have htail (y : M) : (fun a : Fin 3 ↦ ![V i, V j, V k, V l] a.succ y) =
        ![V j y, V k y, V l y] := by
      funext a
      fin_cases a <;> rfl
    have hu0 (a b c z : TangentSpace (𝓡 n) x) : Function.update ![a, b, c] 0 z = ![z, b, c] := by
      funext d
      fin_cases d <;> simp [Function.update]
    have hu1 (a b c z : TangentSpace (𝓡 n) x) : Function.update ![a, b, c] 1 z = ![a, z, c] := by
      funext d
      fin_cases d <;> simp [Function.update]
    have hu2 (a b c z : TangentSpace (𝓡 n) x) : Function.update ![a, b, c] 2 z = ![a, b, z] := by
      funext d
      fin_cases d <;> simp [Function.update]
    rw [hpoint] at he
    simp only [covariantTensorDerivativeOnFields, htail, Fin.sum_univ_succ, hu0] at he
    change mvfderiv (𝓡 n) (fun y ↦ K y ![V j y, V k y, V l y]) x (V i x) -
      (K x ![C t i j x, V k x, V l x] +
        (K x ![V j x, C t i k x, V l x] +
          (K x ![V j x, V k x, C t i l x] + 0))) =
      K2 x ![V i x, V j x, V k x, V l x] at he
    linarith only [he]
  have hKs (i j k : Fin 4) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y ↦ K y ![V i y, V j y, V k y]) U := by
    have heq (y : M) : (fun a : Fin 3 ↦ ![V i, V j, V k] a y) =
        ![V i y, V j y, V k y] := by
      funext a
      fin_cases a <;> rfl
    simpa only [heq] using hK.2 U hU ![V i, V j, V k]
      (by intro a; fin_cases a; exact hV i; exact hV j; exact hV k)
  have hKd (i j k : Fin 4) := ((hKs i j k).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hLs (i j k : Fin 4) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y ↦ L y (V i y) (V j y) (V k y)) U :=
    ((hKs i j k).neg.sub (hKs j i k)).add (hKs k i j)
  let N (i j k l : Fin 4) :=
    -K2 x ![V i x, V j x, V k x, V l x] -
      K2 x ![V i x, V k x, V j x, V l x] + K2 x ![V i x, V l x, V j x, V k x]
  have hLDiff (i j k l : Fin 4) :
      mvfderiv (𝓡 n) (fun y ↦ L y (V j y) (V k y) (V l y)) x (V i x) =
        N i j k l + L x (C t i j x) (V k x) (V l x) +
          L x (V j x) (C t i k x) (V l x) + L x (V j x) (V k x) (C t i l x) := by
    dsimp only [L]
    erw [mvfderiv_add ((hKd j k l).neg.sub (hKd k j l)) (hKd l j k),
      mvfderiv_sub (hKd j k l).neg (hKd k j l), mvfderiv_neg]
    simp only [add_apply, sub_apply, neg_apply, hKDiff, N]
    ring
  have hSdiff (i j k l : Fin 4) :
      mvfderiv (𝓡 n) (S j k l) x (V i x) =
        -2 * (K x ![V i x, C t j k x, V l x] +
          D.ricci x (D.connection (C t j k) x (V i x)) (V l x) +
          D.ricci x (C t j k x) (C t i l x)) + N i j k l +
          L x (C t i j x) (V k x) (V l x) +
          L x (V j x) (C t i k x) (V l x) + L x (V j x) (V k x) (C t i l x) := by
    have hr := ((contMDiffOn_ricci D hU (hCs t j k) (hV l)).contMDiffAt
      (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have hl := ((hLs j k l).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    dsimp only [S]
    erw [mvfderiv_add (mdifferentiableAt_const.mul hr) hl,
      mvfderiv_fun_mul mdifferentiableAt_const hr]
    simp only [add_apply, smul_apply, mvfderiv_const, zero_apply, mul_zero, add_zero, smul_eq_mul]
    rw [hRicDiff (hV i) (hCs t j k) (hV l), hLDiff]
    ring
  have hRsub (a b c : TangentSpace (𝓡 n) x) :
      D.ricci x (a - b) c = D.ricci x a c - D.ricci x b c := by
    obtain ⟨T, hT⟩ := hRic.1 x
    have hu0 (a b z : TangentSpace (𝓡 n) x) : Function.update ![a, b] 0 z = ![z, b] := by
      ext i
      fin_cases i <;> simp [Function.update]
    change D.ricciEvaluation x ![a - b, c] =
      D.ricciEvaluation x ![a, c] - D.ricciEvaluation x ![b, c]
    simp only [hT]
    simpa only [hu0] using T.map_update_sub ![a, c] 0 a b
  have hRcurv : D.ricci x (D.curvatureOnFields (V 0) (V 1) (V 2) x) (V 3 x) =
      D.ricci x (D.connection (C t 1 2) x (V 0 x)) (V 3 x) -
        D.ricci x (D.connection (C t 0 2) x (V 1 x)) (V 3 x) -
        D.ricci x (D.connection (V 2) x (B x)) (V 3 x) := by
    simp only [LeviCivitaData.curvatureOnFields, hRsub, C, B, D]
  have hBracket : B x = C t 0 1 x - C t 1 0 x :=
    (connection_commutator D (hVd 0) (hVd 1)).symm
  have hVelocityFinal :
      mvfderiv (𝓡 n) (S 1 2 3) x (V 0 x) - mvfderiv (𝓡 n) (S 0 2 3) x (V 1 x) -
        (-2 * D.ricci x (C t 1 2 x) (C t 0 3 x) +
          L x (V 1 x) (V 2 x) (C t 0 3 x) + L x (V 0 x) (V 3 x) (C t 1 2 x)) +
        (-2 * D.ricci x (C t 0 2 x) (C t 1 3 x) +
          L x (V 0 x) (V 2 x) (C t 1 3 x) + L x (V 1 x) (V 3 x) (C t 0 2 x)) -
        (-2 * D.ricci x (D.connection (V 2) x (B x)) (V 3 x) + L x (B x) (V 2 x) (V 3 x)) =
      -2 * D.ricci x (D.curvatureOnFields (V 0) (V 1) (V 2) x) (V 3 x) +
        N 0 1 2 3 - N 1 0 2 3 := by
    rw [hSdiff, hSdiff, hRcurv]
    have hb : L x (B x) (V 2 x) (V 3 x) =
        L x (C t 0 1 x) (V 2 x) (V 3 x) - L x (C t 1 0 x) (V 2 x) (V 3 x) := by
      rw [hBracket, hLsub]
    rw [hb]
    linarith only [hLadd (V 0 x) (C t 1 2 x) (V 3 x),
      hLadd (V 1 x) (C t 0 2 x) (V 3 x)]
  have hdFinal := hdActual.congr_deriv hVelocityFinal
  have hFields : D.curvatureOnFields (V 0) (V 1) (V 2) x = D.curvature x u v z := by
    rfl
  rw [hFields] at hdFinal
  have heq (s : ℝ) : (F.connection s).curvatureTensor x u v w z =
      (F.metric s).inner x ((F.connection s).curvatureOnFields (V 0) (V 1) (V 2) x) (V 3 x) := by
    simp [V, LeviCivitaData.curvatureTensor, LeviCivitaData.curvature]
  have hdTarget := hdFinal.congr_of_eventuallyEq (Eventually.of_forall heq)
  apply hdTarget.congr_deriv
  simp only [N, K2, K, LeviCivitaData.iteratedCovariantTensorDerivative, V,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, FiberBundle.extend_apply_self, D]
  ring

end PoincareConjecture.RicciFlowAnalysis

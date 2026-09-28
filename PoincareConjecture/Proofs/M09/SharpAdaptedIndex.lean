import PoincareConjecture.Proofs.M09.UnitAdaptedIndexComparison
import PoincareConjecture.Proofs.M09.ScalarIndexBoundary
import PoincareConjecture.Proofs.M09.AdaptedVariationIndex








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_sharp_adapted_diagonal
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b hb hmax))
    (f : M → ℝ) (O : Set M) (hO : IsOpen O) (hqO : A.gamma Z b ∈ O)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O)
    (hvalue : f (A.gamma Z b) = A.action Z b / (2 * Real.sqrt b))
    (hlower : ∀ᶠ q in 𝓝 (A.gamma Z b), f q ≤ reducedLength F T p q b)
    (hsharp : (F.connection (T - b)).laplacian f (A.gamma Z b) =
      (n : ℝ) / (2 * b) - (F.connection (T - b)).scalarCurvature (A.gamma Z b) -
        reducedHarnackIntegral F T (A.gamma Z)
          (backwardScalarEvolutionAlong F T (A.gamma Z)) b / (2 * b * Real.sqrt b))
    (P : Fin n → ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s))
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 (Real.sqrt b) ⊆ U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z) U)
    (hP : ∀ i, IsAdaptedFieldOn F T (A.squareFamily Z) (P i) U)
    (hpair : ∀ s ∈ U, ∀ i j, (F.metric (T - s ^ 2)).inner (A.squareFamily Z s)
      (P i s) (P j s) = if i = j then 1 else 0) :
    ∀ i, (F.connection (T - b)).ricci (A.gamma Z b) (P i (Real.sqrt b)) (P i (Real.sqrt b)) +
      (F.connection (T - b)).hessian f (A.gamma Z b) (P i (Real.sqrt b)) (P i (Real.sqrt b)) =
        1 / (2 * b) := by
  classical
  let c := Real.sqrt b
  let K := sqrtParameterInterval 0 b
  have hc : 0 < c := Real.sqrt_pos.mpr hb
  have hc2 : c ^ 2 = b := Real.sq_sqrt hb.le
  have hcI : c ∈ Set.Icc 0 c := ⟨hc.le, le_rfl⟩
  have hKU' : K ⊆ U := by simpa only [K, sqrtParameterInterval, Real.sqrt_zero] using hKU
  have hcK : c ∈ K := by simpa only [K, sqrtParameterInterval, Real.sqrt_zero] using hcI
  have hend : A.squareFamily Z c = A.gamma Z b :=
    (A.square_agrees Z c ⟨hc.le, Real.sqrt_lt_sqrt hb.le hmax⟩).trans (congrArg (A.gamma Z) hc2)
  let Y : Fin n → ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s) := fun i s ↦ (s / c) • P i s
  have hY (i : Fin n) := field_smul_smooth (A.squareFamily Z) (P i) (fun s ↦ s / c) U
    hU hα (contDiffOn_id.div_const c) (hP i).smooth
  let HP (i : Fin n) := Classical.choice (nonempty_parametricFieldExtensionOn_compact
    (A.squareFamily Z) (P i) U K hU hKU' isCompact_Icc hα (hP i).smooth)
  let HY (i : Fin n) := Classical.choice (nonempty_parametricFieldExtensionOn_compact
    (A.squareFamily Z) (Y i) U K hU hKU' isCompact_Icc hα (hY i))
  choose V hbase hfield using fun i : Fin n ↦
    exists_initialFixedLVariation_of_smooth_field hM04 hτmax hwindow A Z b hb hmax
      (Y i) U hU hKU hα (hY i) (by simp [Y])
  choose D hH using fun i : Fin n ↦ lExponentialFamily_hessian_le_variation_index hM04 hL
    hτmax hwindow A Z b hb hmax hmin f O hO hqO hf hvalue hlower (V i) (hbase i)
  have hfieldK (i : Fin n) : ∀ s ∈ K,
      (squareVariationField (V i).toLVariation s : E) = (s / c) • P i s := by
    simpa only [K, sqrtParameterInterval, Real.sqrt_zero, Y] using hfield i
  have hterminal (i : Fin n) : (squareVariationField (V i).toLVariation c : E) = P i c := by
    rw [hfieldK i c hcK, div_self hc.ne', one_smul]
  have hdiag (i : Fin n) : (F.connection (T - b)).hessian f (A.gamma Z b) (P i c) (P i c) ≤
      secondVariationIndexForm (V i).toLVariation (D i) / (2 * c) := by
    have h := hH i
    change (F.connection (T - b)).hessian f (A.gamma Z b)
      (squareVariationField (V i).toLVariation c) (squareVariationField (V i).toLVariation c) ≤
        secondVariationIndexForm (V i).toLVariation (D i) / (2 * c) at h
    rwa [hterminal i] at h
  have htrace : (∑ i, (F.connection (T - b)).hessian f (A.gamma Z b) (P i c) (P i c)) =
      (F.connection (T - b)).laplacian f (A.gamma Z b) := by
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - c ^ 2)).toRiemannianMetric⟩
    have hePair (i j : Fin n) : (F.metric (T - c ^ 2)).inner (A.gamma Z b) (P i c) (P j c) =
        if i = j then 1 else 0 := by
      rw [← hend]
      exact hpair c (hKU hcI) i j
    obtain ⟨e, he⟩ := exists_orthonormalBasis_of_metric_pairing (F.metric (T - c ^ 2))
      (A.gamma Z b) (fun i ↦ (P i c : E)) hePair
    have h := squareTime_laplacian_orthonormal_trace_local F T τmax hτmax hwindow
      (A.gamma Z b) c (htime (hKU hcI)) f O hO hqO hf e
    have h' : (∑ i, (F.connection (T - c ^ 2)).hessian f (A.gamma Z b) (P i c) (P i c)) =
        (F.connection (T - c ^ 2)).laplacian f (A.gamma Z b) := by
      simpa only [he] using h
    rwa [hc2] at h'
  have halgebra (R Q : ℝ) : ((n : ℝ) / c - 2 * c * R - Q / b) / (2 * c) =
      (n : ℝ) / (2 * b) - R - Q / (2 * b * c) := by
    rw [← hc2]
    field_simp [hc.ne'] <;> ring
  have hsumEq : (∑ i, (F.connection (T - b)).hessian f (A.gamma Z b) (P i c) (P i c)) =
      ∑ i, secondVariationIndexForm (V i).toLVariation (D i) / (2 * c) := by
    rw [htrace, ← Finset.sum_div,
      realized_adapted_variations_index_sum hM04 hτmax hwindow A Z b hb hmax P U hU hKU'
        htime hα hP hpair HP HY V hbase hfieldK D]
    change (F.connection (T - b)).laplacian f (A.gamma Z b) =
      ((n : ℝ) / c - 2 * c * (F.connection (T - c ^ 2)).scalarCurvature (A.squareFamily Z c) -
        reducedHarnackIntegral F T (A.gamma Z)
          (backwardScalarEvolutionAlong F T (A.gamma Z)) b / c ^ 2) / (2 * c)
    rw [hc2, hend, halgebra, hsharp]
  have heach := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ ↦ hdiag i)).mp hsumEq
  intro i
  obtain ⟨W, B, C, hW, hKW, hWU, hB, hC, hcoeff⟩ := exists_unit_adapted_scalar_coefficients
    F hM04 T τmax hτmax hwindow (A.squareFamily Z) (P i) c hc U hU hKU htime hα (hP i)
      (fun s hs ↦ by simpa using hpair s hs i i)
  have hindex := unit_adapted_scalar_index_eq hM04 hτmax hwindow A Z b hb hmax (P i) W hW hKW
    (hWU.trans htime) (hα.mono hWU) ((hP i).mono hWU) B C (fun s hs ↦ (hcoeff s hs).2)
      (fun s ↦ s / c) (contDiffOn_id.div_const c) (V i).toLVariation (hbase i) (hfield i) (D i)
  have heq : scalarIndex B C c (fun s ↦ s / c) =
      2 * c * (F.connection (T - b)).hessian f (A.gamma Z b) (P i c) (P i c) := by
    have h := heach i (Finset.mem_univ i)
    rw [hindex] at h
    have h' := (eq_div_iff (by positivity : (2 * c) ≠ 0)).mp h
    nlinarith
  have hcompare := unit_adapted_scalar_index_comparison hM04 hL hτmax hwindow A Z b hb hmax
    hmin f O hO hqO hf hvalue hlower (P i) W hW hKW (hWU.trans htime) (hα.mono hWU)
      ((hP i).mono hWU) B C (fun s hs ↦ (hcoeff s hs).2)
  have hrigid := scalarIndex_boundary_rigidity B C c hc W hW hKW hB hC _ hcompare heq
  change 2 * c * (F.connection (T - b)).hessian f (A.gamma Z b) (P i c) (P i c) =
    1 / c + B c / 2 at hrigid
  rw [(hcoeff c hcI).1, hc2, hend] at hrigid
  field_simp [hc.ne'] at hrigid
  change (F.connection (T - b)).ricci (A.gamma Z b) (P i c) (P i c) +
    (F.connection (T - b)).hessian f (A.gamma Z b) (P i c) (P i c) = 1 / (2 * b)
  conv_rhs => rw [← hc2]
  field_simp [hc.ne']
  nlinarith

end PoincareConjecture.Proofs.M09

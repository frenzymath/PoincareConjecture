import PoincareConjecture.Proofs.M09.ExponentialAdaptedFrame
import PoincareConjecture.Proofs.M09.AdaptedVariationIndex
import PoincareConjecture.Proofs.M09.RealizedSquareVariation
import PoincareConjecture.Proofs.M09.VariationHessianComparison
import PoincareConjecture.Proofs.M09.LocalHessianTrace








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T2Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_laplacian_le_of_lower_contact
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b hb hmax))
    (f : M → ℝ) (O : Set M) (hO : IsOpen O) (hqO : A.gamma Z b ∈ O)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O)
    (hvalue : f (A.gamma Z b) = A.action Z b / (2 * Real.sqrt b))
    (hlower : ∀ᶠ q in 𝓝 (A.gamma Z b), f q ≤ reducedLength F T p q b) :
    (F.connection (T - b)).laplacian f (A.gamma Z b) ≤
      (n : ℝ) / (2 * b) - (F.connection (T - b)).scalarCurvature (A.gamma Z b) -
        reducedHarnackIntegral F T (A.gamma Z)
          (backwardScalarEvolutionAlong F T (A.gamma Z)) b / (2 * b * Real.sqrt b) := by
  classical
  let c := Real.sqrt b
  let K := sqrtParameterInterval 0 b
  have hc : 0 < c := Real.sqrt_pos.mpr hb
  have hc2 : c ^ 2 = b := Real.sq_sqrt hb.le
  have hcK : c ∈ K := by simp only [K, sqrtParameterInterval, Real.sqrt_zero, Set.mem_Icc]; exact ⟨hc.le, le_rfl⟩
  have hend : A.squareFamily Z c = A.gamma Z b :=
    (A.square_agrees Z c ⟨hc.le, Real.sqrt_lt_sqrt hb.le hmax⟩).trans (congrArg (A.gamma Z) hc2)
  obtain ⟨U, P, hU, _, hKU', htime, hα, hP, hpair⟩ :=
    lExponentialFamily_exists_adapted_frame hτmax hwindow A Z b hb hmax
  have hKU : K ⊆ U := by simpa only [K, sqrtParameterInterval, Real.sqrt_zero] using hKU'
  let Y : Fin n → ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s) :=
    fun i s ↦ (s / c) • P i s
  have hY (i : Fin n) : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ (⟨A.squareFamily Z s, Y i s⟩ : TangentBundle (𝓡 n) M)) U :=
    field_smul_smooth (A.squareFamily Z) (P i) (fun s ↦ s / c) U hU hα
      (contDiffOn_id.div_const c) (hP i).smooth
  let HP (i : Fin n) := Classical.choice (nonempty_parametricFieldExtensionOn_compact
    (A.squareFamily Z) (P i) U K hU hKU isCompact_Icc hα (hP i).smooth)
  let HY (i : Fin n) := Classical.choice (nonempty_parametricFieldExtensionOn_compact
    (A.squareFamily Z) (Y i) U K hU hKU isCompact_Icc hα (hY i))
  choose V hbase hfield using fun i : Fin n ↦
    exists_initialFixedLVariation_of_smooth_field hM04 hτmax hwindow A Z b hb hmax
      (Y i) U hU hKU' hα (hY i) (by simp [Y])
  choose D hH using fun i : Fin n ↦ lExponentialFamily_hessian_le_variation_index
    hM04 hL hτmax hwindow A Z b hb hmax hmin f O hO hqO hf hvalue hlower (V i) (hbase i)
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
    rw [hterminal i] at h
    exact h
  have htrace : (∑ i, (F.connection (T - b)).hessian f (A.gamma Z b) (P i c) (P i c)) =
      (F.connection (T - b)).laplacian f (A.gamma Z b) := by
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - c ^ 2)).toRiemannianMetric⟩
    have hePair (i j : Fin n) : (F.metric (T - c ^ 2)).inner (A.gamma Z b) (P i c) (P j c) =
        if i = j then 1 else 0 := by
      rw [← hend]
      exact hpair c (hKU hcK) i j
    obtain ⟨e, he⟩ := exists_orthonormalBasis_of_metric_pairing (F.metric (T - c ^ 2))
      (A.gamma Z b) (fun i ↦ (P i c : E)) hePair
    have h := squareTime_laplacian_orthonormal_trace_local F T τmax hτmax hwindow
      (A.gamma Z b) c (htime (hKU hcK)) f O hO hqO hf e
    have h' : (∑ i, (F.connection (T - c ^ 2)).hessian f (A.gamma Z b) (P i c) (P i c)) =
        (F.connection (T - c ^ 2)).laplacian f (A.gamma Z b) := by
      simpa only [he] using h
    rw [hc2] at h'
    exact h'
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hdiag i)
  rw [htrace, ← Finset.sum_div,
    realized_adapted_variations_index_sum hM04 hτmax hwindow A Z b hb hmax P U hU hKU
      htime hα hP hpair HP HY V hbase hfieldK D] at hsum
  change (F.connection (T - b)).laplacian f (A.gamma Z b) ≤
    ((n : ℝ) / c - 2 * c * (F.connection (T - c ^ 2)).scalarCurvature (A.squareFamily Z c) -
      reducedHarnackIntegral F T (A.gamma Z)
        (backwardScalarEvolutionAlong F T (A.gamma Z)) b / c ^ 2) / (2 * c) at hsum
  rw [hc2, hend] at hsum
  have halgebra (R Q : ℝ) : ((n : ℝ) / c - 2 * c * R - Q / b) / (2 * c) =
      (n : ℝ) / (2 * b) - R - Q / (2 * b * c) := by
    rw [← hc2]
    field_simp [hc.ne'] <;> ring
  exact hsum.trans_eq (halgebra _ _)

end PoincareConjecture.Proofs.M09

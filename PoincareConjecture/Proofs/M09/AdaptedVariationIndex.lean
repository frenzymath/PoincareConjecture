import PoincareConjecture.Proofs.M09.RealizedIndexDensity
import PoincareConjecture.Proofs.M09.ScaledAdaptedField
import PoincareConjecture.Proofs.M09.AdaptedOrthonormalFrame
import PoincareConjecture.Proofs.M09.ScalarIndexIntegral
import PoincareConjecture.Proofs.M09.VariationIndexIntegrability








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology intervalIntegral BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
theorem realized_adapted_variations_index_sum
    (hM04 : RicciFlowCurvatureTheory.{u}) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (P : Fin n → ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s))
    (U : Set ℝ) (hU : IsOpen U) (hKU : sqrtParameterInterval 0 b ⊆ U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z) U)
    (hP : ∀ i, IsAdaptedFieldOn F T (A.squareFamily Z) (P i) U)
    (hpair : ∀ s ∈ U, ∀ i j, (F.metric (T - s ^ 2)).inner (A.squareFamily Z s)
      (P i s) (P j s) = if i = j then 1 else 0)
    (HP : ∀ i, ParametricAlongCurveExtensionOn (n := n) (sqrtParameterInterval 0 b)
      (A.squareFamily Z) (P i))
    (HY : ∀ i, ParametricAlongCurveExtensionOn (n := n) (sqrtParameterInterval 0 b)
      (A.squareFamily Z) (fun s ↦ (s / Real.sqrt b) • P i s))
    (V : Fin n → InitialFixedLVariation F T 0 b (A.path Z b hb hmax))
    (hbase : ∀ i, (V i).toLVariation.baseSquareCurve = A.squareFamily Z)
    (hfield : ∀ i, ∀ s ∈ sqrtParameterInterval 0 b,
      (squareVariationField (V i).toLVariation s : E) = (s / Real.sqrt b) • P i s)
    (D : ∀ i, LVariationDerivativeData (V i).toLVariation) :
    (∑ i, secondVariationIndexForm (V i).toLVariation (D i)) =
      (n : ℝ) / Real.sqrt b - 2 * Real.sqrt b *
        (F.connection (T - (Real.sqrt b) ^ 2)).scalarCurvature (A.squareFamily Z (Real.sqrt b)) -
        reducedHarnackIntegral F T (A.gamma Z)
          (backwardScalarEvolutionAlong F T (A.gamma Z)) b / (Real.sqrt b) ^ 2 := by
  classical
  let c := Real.sqrt b
  let K := sqrtParameterInterval 0 b
  have hc : 0 < c := Real.sqrt_pos.mpr hb
  have hKd : UniqueDiffOn ℝ K := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt (le_refl 0) hb)
  have hweight : ContDiffOn ℝ ∞ (fun s : ℝ ↦ s / c) U := contDiffOn_id.div_const c
  have hweightDer (s : ℝ) : deriv (fun t : ℝ ↦ t / c) s = 1 / c :=
    ((hasDerivAt_id s).div_const c).deriv
  have hpoint (i : Fin n) (s : ℝ) (hs : s ∈ K) :
      secondVariationIndexDensity (V i).toLVariation (D i) s =
        pointwiseSecondVariationDensity F T (A.squareFamily Z s) s
          (curveVelocity (A.squareFamily Z) s) ((s / c) • P i s)
          ((1 / c : ℝ) • P i s - (2 * s * (s / c)) •
            ricciOperator hM04 (F.connection (T - s ^ 2)) (A.squareFamily Z s) (P i s)) := by
    rw [realized_variation_indexDensity A Z b hb hmax _ (HY i) (V i).toLVariation
      (hbase i) (hfield i) (D i) s hs]
    rw [IsAdaptedFieldOn.scaled_pullback F hM04 T τmax hτmax hwindow
      (A.squareFamily Z) (P i) (fun t ↦ t / c) K U hU hα hweight (hP i) (HP i) (HY i)
      s hs (hKU hs) (hKd s hs) (htime (hKU hs)), hweightDer]
  have hsum (s : ℝ) (hs : s ∈ K) :
      (∑ i, secondVariationIndexDensity (V i).toLVariation (D i) s) =
        adaptedScalarIndexDensity F T (A.squareFamily Z) c s := by
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
    obtain ⟨e, he⟩ := exists_orthonormalBasis_of_metric_pairing (F.metric (T - s ^ 2))
      (A.squareFamily Z s) (fun i ↦ P i s) (hpair s (hKU hs))
    calc
      _ = ∑ i, pointwiseSecondVariationDensity F T (A.squareFamily Z s) s
          (curveVelocity (A.squareFamily Z) s) ((s / c) • P i s)
          ((1 / c : ℝ) • P i s - (2 * s * (s / c)) •
            ricciOperator hM04 (F.connection (T - s ^ 2)) (A.squareFamily Z s) (P i s)) :=
        Finset.sum_congr rfl (fun i _ ↦ hpoint i s hs)
      _ = ∑ i, pointwiseSecondVariationDensity F T (A.squareFamily Z s) s
          (curveVelocity (A.squareFamily Z) s) ((s / c) • e i)
          ((1 / c : ℝ) • e i - (2 * s * (s / c)) •
            ricciOperator hM04 (F.connection (T - s ^ 2)) (A.squareFamily Z s) (e i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [he i]
      _ = _ := pointwiseSecondVariationDensity_linear_weight_trace F hM04 T τmax hτmax
        hwindow (A.squareFamily Z) c hc s (htime (hKU hs)) e
  have hi (i : Fin n) := secondVariationIndexDensity_intervalIntegrable hM04 hτmax hwindow
    hb hmax (V i).toLVariation (D i)
  change (∑ i, ∫ s in Real.sqrt 0..c, secondVariationIndexDensity (V i).toLVariation (D i) s) = _
  rw [Real.sqrt_zero, ← intervalIntegral.integral_finsetSum (fun i _ ↦ hi i)]
  calc
    _ = ∫ s in 0..c, adaptedScalarIndexDensity F T (A.squareFamily Z) c s := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hsK : s ∈ K := by
        simpa only [K, sqrtParameterInterval, Real.sqrt_zero,
          Set.uIcc_of_le (Real.sqrt_nonneg b)] using hs
      exact hsum s hsK
    _ = _ := (lExponentialFamily_adaptedScalarIndex_integral hM04 hτmax hwindow
      A Z b hb hmax).2

end PoincareConjecture.Proofs.M09

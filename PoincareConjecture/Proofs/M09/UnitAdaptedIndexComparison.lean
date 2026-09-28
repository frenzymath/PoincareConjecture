import PoincareConjecture.Proofs.M09.UnitAdaptedIndexCoefficients
import PoincareConjecture.Proofs.M09.ScalarIndexForm
import PoincareConjecture.Proofs.M09.RealizedIndexDensity
import PoincareConjecture.Proofs.M09.RealizedSquareVariation
import PoincareConjecture.Proofs.M09.VariationHessianComparison
import PoincareConjecture.Proofs.M09.LocalHessianTrace








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology intervalIntegral
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem unit_adapted_scalar_index_eq (hM04 : RicciFlowCurvatureTheory.{u})
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (P : ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s))
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 (Real.sqrt b) ⊆ U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z) U)
    (hP : IsAdaptedFieldOn F T (A.squareFamily Z) P U) (B C : ℝ → ℝ)
    (hcoeff : ∀ s ∈ Set.Icc 0 (Real.sqrt b), ∀ f fp : ℝ,
      pointwiseSecondVariationDensity F T (A.squareFamily Z s) s
        (curveVelocity (A.squareFamily Z) s) (f • P s)
        (fp • P s - (2 * s * f) •
          ricciOperator hM04 (F.connection (T - s ^ 2)) (A.squareFamily Z s) (P s)) =
          fp ^ 2 + B s * f * fp + C s * f ^ 2)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (V : LVariation F T 0 b (A.path Z b hb hmax))
    (hbase : V.baseSquareCurve = A.squareFamily Z)
    (hfield : ∀ s ∈ Set.Icc 0 (Real.sqrt b), (squareVariationField V s : E) = f s • P s)
    (D : LVariationDerivativeData V) :
    secondVariationIndexForm V D = scalarIndex B C (Real.sqrt b) f := by
  let K := sqrtParameterInterval 0 b
  have hKU' : K ⊆ U := by simpa only [K, sqrtParameterInterval, Real.sqrt_zero] using hKU
  have hKd : UniqueDiffOn ℝ K := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt (le_refl 0) hb)
  let Y : ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s) := fun s ↦ f s • P s
  have hY := field_smul_smooth (A.squareFamily Z) P f U hU hα hf hP.smooth
  obtain ⟨HP⟩ := nonempty_parametricFieldExtensionOn_compact (A.squareFamily Z) P U K
    hU hKU' isCompact_Icc hα hP.smooth
  obtain ⟨HY⟩ := nonempty_parametricFieldExtensionOn_compact (A.squareFamily Z) Y U K
    hU hKU' isCompact_Icc hα hY
  have hfieldK : ∀ s ∈ K, (squareVariationField V s : E) = Y s := by
    simpa only [K, sqrtParameterInterval, Real.sqrt_zero, Y] using hfield
  change (∫ s in Real.sqrt 0..Real.sqrt b, secondVariationIndexDensity V D s) = _
  rw [Real.sqrt_zero]
  unfold scalarIndex
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc 0 (Real.sqrt b) := by
    simpa only [Set.uIcc_of_le (Real.sqrt_nonneg b)] using hs
  have hsK : s ∈ K := by simpa only [K, sqrtParameterInterval, Real.sqrt_zero] using hs'
  rw [realized_variation_indexDensity A Z b hb hmax Y HY V hbase hfieldK D s hsK,
    IsAdaptedFieldOn.scaled_pullback F hM04 T τmax hτmax hwindow (A.squareFamily Z)
      P f K U hU hα hf hP HP HY s hsK (hKU hs') (hKd s hsK) (htime (hKU hs'))]
  exact hcoeff s hs' (f s) (deriv f s)

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem unit_adapted_scalar_index_comparison [ConnectedSpace M]
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b hb hmax))
    (ψ : M → ℝ) (O : Set M) (hO : IsOpen O) (hqO : A.gamma Z b ∈ O)
    (hψ : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ ψ O)
    (hvalue : ψ (A.gamma Z b) = A.action Z b / (2 * Real.sqrt b))
    (hlower : ∀ᶠ q in 𝓝 (A.gamma Z b), ψ q ≤ reducedLength F T p q b)
    (P : ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s))
    (U : Set ℝ) (hU : IsOpen U) (hKU : Set.Icc 0 (Real.sqrt b) ⊆ U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (A.squareFamily Z) U)
    (hP : IsAdaptedFieldOn F T (A.squareFamily Z) P U) (B C : ℝ → ℝ)
    (hcoeff : ∀ s ∈ Set.Icc 0 (Real.sqrt b), ∀ f fp : ℝ,
      pointwiseSecondVariationDensity F T (A.squareFamily Z s) s
        (curveVelocity (A.squareFamily Z) s) (f • P s)
        (fp • P s - (2 * s * f) •
          ricciOperator hM04 (F.connection (T - s ^ 2)) (A.squareFamily Z s) (P s)) =
          fp ^ 2 + B s * f * fp + C s * f ^ 2) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f U → f 0 = 0 →
      (2 * Real.sqrt b * (F.connection (T - b)).hessian ψ (A.gamma Z b)
        (P (Real.sqrt b)) (P (Real.sqrt b))) * f (Real.sqrt b) ^ 2 ≤
          scalarIndex B C (Real.sqrt b) f := by
  intro f hf hf0
  let c := Real.sqrt b
  have hc : 0 < c := Real.sqrt_pos.mpr hb
  have hcK : c ∈ Set.Icc 0 c := ⟨hc.le, le_rfl⟩
  have hc2 : c ^ 2 = b := Real.sq_sqrt hb.le
  have hY := field_smul_smooth (A.squareFamily Z) P f U hU hα hf hP.smooth
  obtain ⟨V, hbase, hfield⟩ := exists_initialFixedLVariation_of_smooth_field hM04
    hτmax hwindow A Z b hb hmax (fun s ↦ f s • P s) U hU hKU hα hY (by simp [hf0])
  obtain ⟨D, hcompare⟩ := lExponentialFamily_hessian_le_variation_index hM04 hL hτmax hwindow
    A Z b hb hmax hmin ψ O hO hqO hψ hvalue hlower V hbase
  rw [unit_adapted_scalar_index_eq hM04 hτmax hwindow A Z b hb hmax P U hU hKU htime
    hα hP B C hcoeff f hf V.toLVariation hbase hfield D, hfield c hcK] at hcompare
  obtain ⟨H, hH⟩ := squareTime_hessian_exists_bilinear_local F T τmax hτmax hwindow
    (A.gamma Z b) c (htime (hKU hcK)) ψ O hO hqO hψ
  rw [hc2] at hH
  have hscale : (F.connection (T - b)).hessian ψ (A.gamma Z b) (f c • P c) (f c • P c) =
      f c ^ 2 * (F.connection (T - b)).hessian ψ (A.gamma Z b) (P c) (P c) := by
    rw [hH, hH]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [hscale] at hcompare
  have h := (le_div_iff₀ (by positivity : 0 < 2 * c)).mp hcompare
  nlinarith

end PoincareConjecture.Proofs.M09

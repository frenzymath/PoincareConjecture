import PoincareConjecture.Proofs.M09.PullbackFieldCongruence
import PoincareConjecture.Proofs.M09.AdaptedIndexTrace
import PoincareConjecture.Proofs.M09.FamilySlices
import PoincareConjecture.Proofs.M09.VelocityRestriction








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem realized_variation_indexDensity
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (Y : ∀ s, TangentSpace (𝓡 n) (A.squareFamily Z s))
    (HY : ParametricAlongCurveExtensionOn (n := n) (sqrtParameterInterval 0 b)
      (A.squareFamily Z) Y)
    (V : LVariation F T 0 b (A.path Z b hb hmax))
    (hbase : V.baseSquareCurve = A.squareFamily Z)
    (hfield : ∀ s ∈ sqrtParameterInterval 0 b, (squareVariationField V s : E) = Y s)
    (D : LVariationDerivativeData V) (s : ℝ) (hs : s ∈ sqrtParameterInterval 0 b) :
    secondVariationIndexDensity V D s =
      pointwiseSecondVariationDensity F T (A.squareFamily Z s) s
        (curveVelocity (A.squareFamily Z) s) (Y s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) (A.squareFamily Z) Y
          (sqrtParameterInterval 0 b) HY s) := by
  have hKd : UniqueDiffOn ℝ (sqrtParameterInterval 0 b) :=
    uniqueDiffOn_Icc (Real.sqrt_lt_sqrt (le_refl 0) hb)
  have hs' : s ∈ Set.Ico 0 (Real.sqrt τmax) :=
    ⟨by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  have hα := (lExponentialFamily_squareSlice_contMDiffAt A Z s hs').mdifferentiableAt
    (by simp)
  have hpull := pullbackCovariantDerivative_curve_field_congr F (fun r ↦ T - r ^ 2)
    V.baseSquareCurve (A.squareFamily Z) (squareVariationField V) Y
    (sqrtParameterInterval 0 b) D.variation_extension HY hbase hfield s hs (hKd s hs) hα
  have hvel : (curveVelocityWithin V.baseSquareCurve (sqrtParameterInterval 0 b) s : E) =
      curveVelocity (A.squareFamily Z) s := by
    rw [hbase]
    exact curveVelocityWithin_eq_curveVelocity _ _ _ (hKd s hs) hα
  rw [secondVariationIndexDensity_eq_pointwise]
  let Q : M → E → E → E → ℝ := fun q a y w ↦
    pointwiseSecondVariationDensity F T q s a y w
  exact congrArg₂ (fun q a ↦ Q q a
      (squareVariationField V s) (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2)
        V.baseSquareCurve (squareVariationField V) (sqrtParameterInterval 0 b)
        D.variation_extension s)) (congrFun hbase s) hvel |>.trans
    (congrArg₂ (Q (A.squareFamily Z s) (curveVelocity (A.squareFamily Z) s))
      (hfield s hs) hpull)

end PoincareConjecture.Proofs.M09

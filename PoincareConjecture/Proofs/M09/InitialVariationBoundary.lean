import PoincareConjecture.Proofs.M09.InitialVariationFields
import PoincareConjecture.Proofs.M09.FamilySquareVelocity
import PoincareConjecture.Proofs.M09.VelocityRestriction

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

local notation "Q" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem initialVectorVariation_boundaryTerm (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    firstVariationBoundaryTerm (initialVectorVariation A Z W b hb hmax).toLVariation =
      2 * Real.sqrt b * (F.metric (T - b)).inner (A.gamma Z b)
        (curveVelocity (n := n) (A.gamma Z) b) (A.sliceDifferential Z b W) := by
  let V := (initialVectorVariation A Z W b hb hmax).toLVariation
  let K := sqrtParameterInterval 0 b
  have hbase : V.baseSquareCurve = A.squareFamily Z :=
    initialVectorVariation_baseSquareCurve A Z W b hb hmax
  have hroot : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hrootmax : Real.sqrt b < Real.sqrt τmax := Real.sqrt_lt_sqrt hb.le hmax
  have hK : K = Set.Icc 0 (Real.sqrt b) := by simp [K, sqrtParameterInterval]
  have hKdiff : UniqueDiffOn ℝ K := hK ▸ uniqueDiffOn_Icc hroot
  have hend : Real.sqrt b ∈ K := by rw [hK]; exact ⟨hroot.le, le_rfl⟩
  have hdiff : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) V.baseSquareCurve (Real.sqrt b) := by
    rw [hbase]
    exact (lExponentialFamily_squareSlice_contMDiffAt A Z (Real.sqrt b)
      ⟨hroot.le, hrootmax⟩).mdifferentiableAt (by simp)
  have hwithin := curveVelocityWithin_eq_curveVelocity V.baseSquareCurve K (Real.sqrt b)
    (hKdiff _ hend) hdiff
  have hvbase := congrArg (fun α : ℝ → M ↦ (curveVelocity (n := n) α (Real.sqrt b) : Q)) hbase
  have hvsquare := lExponentialFamily_square_velocity_eq A Z (Real.sqrt b) ⟨hroot, hrootmax⟩
  have hvsq := congrArg (fun t : ℝ ↦ (curveVelocity (n := n) (A.gamma Z) t : Q))
    (Real.sq_sqrt hb.le)
  have hv : (curveVelocityWithin (n := n) V.baseSquareCurve K (Real.sqrt b) : Q) =
      (2 * Real.sqrt b) • curveVelocity (n := n) (A.gamma Z) b :=
    hwithin.trans (hvbase.trans (hvsquare.trans
      (congrArg (fun v : Q ↦ (2 * Real.sqrt b) • v) hvsq)))
  have hx : V.baseSquareCurve (Real.sqrt b) = A.gamma Z b := by
    apply (congrFun hbase (Real.sqrt b)).trans
    simpa only [Real.sq_sqrt hb.le] using
      A.square_agrees Z (Real.sqrt b) ⟨hroot.le, hrootmax⟩
  have hy : (squareVariationField V (Real.sqrt b) : Q) = A.sliceDifferential Z b W :=
    initialVectorVariation_squareField_terminal A Z W b hb hmax
  have htriple :
      (V.baseSquareCurve (Real.sqrt b),
        ((curveVelocityWithin (n := n) V.baseSquareCurve K (Real.sqrt b) : Q),
          (squareVariationField V (Real.sqrt b) : Q))) =
      (A.gamma Z b, ((2 * Real.sqrt b) • curveVelocity (n := n) (A.gamma Z) b,
        A.sliceDifferential Z b W)) := Prod.ext hx (Prod.ext hv hy)
  have hvalue := congrArg (fun q : M × (Q × Q) ↦
    (F.metric (T - b)).inner q.1 q.2.1 q.2.2) htriple
  have hlinear : (F.metric (T - b)).inner (A.gamma Z b)
      ((2 * Real.sqrt b) • curveVelocity (n := n) (A.gamma Z) b) (A.sliceDifferential Z b W) =
      2 * Real.sqrt b * (F.metric (T - b)).inner (A.gamma Z b)
        (curveVelocity (n := n) (A.gamma Z) b) (A.sliceDifferential Z b W) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
  have hterminal : (F.metric (T - (Real.sqrt b) ^ 2)).inner (V.baseSquareCurve (Real.sqrt b))
      (curveVelocityWithin (n := n) V.baseSquareCurve K (Real.sqrt b))
      (squareVariationField V (Real.sqrt b)) =
      2 * Real.sqrt b * (F.metric (T - b)).inner (A.gamma Z b)
        (curveVelocity (n := n) (A.gamma Z) b) (A.sliceDifferential Z b W) := by
    rw [Real.sq_sqrt hb.le]
    exact hvalue.trans hlinear
  have hzero : (squareVariationField V 0 : Q) = 0 :=
    initialVectorVariation_squareField_zero A Z W b hb hmax
  have hinitial : (F.metric (T - (0 : ℝ) ^ 2)).inner (V.baseSquareCurve 0)
      (curveVelocityWithin (n := n) V.baseSquareCurve K 0) (squareVariationField V 0) = 0 := by
    rw [hzero]
    exact map_zero _
  change firstVariationBoundaryTerm V = _
  unfold firstVariationBoundaryTerm
  dsimp only
  rw [Real.sqrt_zero, hterminal, hinitial, sub_zero]

end PoincareConjecture.Proofs.M09

import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.OrdinaryRealization.SliceGeometry
import PoincareLib.Geometry.RicciFlow.Harnack.Matrix.Tensors

/-!
# Scalar analytic transport to actual Chapter 11 slices

Morgan-Tian Theorem 12.28, pp. 323-324, and Theorem 11.1,
pp. 267-269. The actual inclusion differential preserves unit vectors
and scalar evaluations; the one ordinary box retains the original
within-domain scalar evolution witness at every valid time.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.M35.OrdinaryRealization

/-- Theorem 12.28, pp. 323-324: actual scalar directional derivatives
commute with the inclusion of a valid ordinary slice. -/
theorem scalar_directional_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (y : (slice J t).carrier) (v : TangentSpace (𝓡 3) y) :
    mvfderiv (𝓡 3) (connection F t).scalarCurvature y v =
      mvfderiv (𝓡 3) (F.connection t).scalarCurvature y.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : (slice J t).carrier → StandardCapSpace) y v) := by
  have hf : (connection F t).scalarCurvature =
      (F.connection t).scalarCurvature ∘
        (Subtype.val : (slice J t).carrier → StandardCapSpace) := by
    funext z
    exact scalar_eq P F ht z.val
  rw [hf]
  have hreg := Poincare.RicciFlow.Harnack.scalarCurvature_contMDiff_slice P.curvature J F t ht
  exact mvfderiv_comp_apply y
    (hreg.mdifferentiable (by simp) _)
    ((sliceDiffeomorph ht).contMDiff.mdifferentiable (by simp) _) v

/-- Theorem 11.1's scalar directional bound transfers with the identical
constant and scalar cutoff on the actual retained slice. -/
theorem scalar_directional_bound (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    {A H : ℝ}
    (hbound : ∀ x : StandardCapSpace, H ≤ (F.connection t).scalarCurvature x →
      ∀ v : TangentSpace (𝓡 3) x, (F.metric t).inner x v v = 1 →
        |mvfderiv (𝓡 3) (F.connection t).scalarCurvature x v| ≤
          A * (F.connection t).scalarCurvature x ^ (3 / 2 : ℝ))
    (y : ((generalizedFlow F).slice t).carrier)
    (hy : H ≤ ((generalizedFlow F).connection t).scalarCurvature y)
    (v : TangentSpace (𝓡 3) y) (hv : ((generalizedFlow F).metric t).inner y v v = 1) :
    |mvfderiv (𝓡 3) ((generalizedFlow F).connection t).scalarCurvature y v| ≤
      A * ((generalizedFlow F).connection t).scalarCurvature y ^ (3 / 2 : ℝ) := by
  have hs : ((generalizedFlow F).connection t).scalarCurvature y =
      (F.connection t).scalarCurvature y.val := scalar_eq P F ht y.val
  have hy' : H ≤ (F.connection t).scalarCurvature y.val := hs ▸ hy
  calc
    _ = |mvfderiv (𝓡 3) (F.connection t).scalarCurvature y.val
        (mfderiv (𝓡 3) (𝓡 3)
          (Subtype.val : (slice J t).carrier → StandardCapSpace) y v)| :=
      congrArg abs (scalar_directional_eq P F ht y v)
    _ ≤ A * (F.connection t).scalarCurvature y.val ^ (3 / 2 : ℝ) :=
      hbound y.val hy' _ hv
    _ = _ := congrArg (fun r : ℝ => A * r ^ (3 / 2 : ℝ)) hs.symm

/-- Theorem 11.1's boxwise time bound uses M04's exact within-domain
scalar evolution derivative, since every box is the original ordinary flow. -/
theorem scalar_time_bound (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    {A H : ℝ}
    (hbound : ∀ x : StandardCapSpace, H ≤ (F.connection t).scalarCurvature x →
      |(F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x| ≤ A * ((F.connection t).scalarCurvature x) ^ 2)
    (b : (generalizedFlow F).box_index) (x : ((generalizedFlow F).box b).carrier.carrier)
    (hx : H ≤ (((generalizedFlow F).box b).flow.connection t).scalarCurvature x) :
    ∃ d : ℝ, HasDerivWithinAt
        (fun s => (((generalizedFlow F).box b).flow.connection s).scalarCurvature x) d
        ((generalizedFlow F).box b).interval t ∧
      |d| ≤ A * ((((generalizedFlow F).box b).flow.connection t).scalarCurvature x) ^ 2 :=
  ⟨_, P.curvature.scalar_evolution 3 StandardCapSpace J F t ht x, hbound x hx⟩

end PoincareMT.M35.OrdinaryRealization

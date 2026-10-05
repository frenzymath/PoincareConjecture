import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.VectorEquality

/-!
# Scalar graph acceleration for curve uniqueness

Projection along the graph tangent cancels the arbitrary tangential
coefficient. The actual continuous curvature then recovers a continuous
graph second derivative. MT2007 Claim 19.1, p. 437;
`2026-09-21-uniqueness-graph-comparison-components.md`, section 2.
These identities retain the graph constraint and curvature identity as
explicit inputs; they do not construct the graph coordinates.
-/

set_option autoImplicit false

open Set
open scoped RealInnerProductSpace

namespace PoincareMT.M63

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal lower term in a graph over a fixed smooth reference,
with scalar principal coefficient. MT2007 Claim 19.1, p. 437;
graph comparison components, section 2. Its geometric identities are
asserted only where the graph's reference projection is nonzero. -/
noncomputable def curveGraphLower (A : ℝ) (b₀ r₁ r₂ r₃ U P : E) : E :=
  A • r₂ + b₀ +
    (-(A * (⟪r₂, r₁⟫ - 2 * ⟪P, r₂⟫ - ⟪U, r₃⟫) + ⟪b₀, r₁⟫) /
      ⟪r₁ + P, r₁⟫) • (r₁ + P)

/-- The fixed-reference graph projection of actual curvature has
the positive scalar graph principal part. The supplied tangential
coefficient cancels. MT2007 Claim 19.1, p. 437; graph comparison
components, section 2. -/
theorem graph_acceleration_projection
    {r₁ r₂ r₃ U P Q eta b₀ : E} {A lambda : ℝ}
    (hd : ⟪r₁ + P, r₁⟫ ≠ 0)
    (hconstraint : ⟪Q, r₁⟫ = -2 * ⟪P, r₂⟫ - ⟪U, r₃⟫)
    (hcurvature : eta = A • (r₂ + Q) + b₀ - lambda • (r₁ + P)) :
    eta - (⟪eta, r₁⟫ / ⟪r₁ + P, r₁⟫) • (r₁ + P) =
      A • Q + curveGraphLower A b₀ r₁ r₂ r₃ U P := by
  have hinner : ⟪eta, r₁⟫ =
      A * (⟪r₂, r₁⟫ - 2 * ⟪P, r₂⟫ - ⟪U, r₃⟫) + ⟪b₀, r₁⟫ -
        lambda * ⟪r₁ + P, r₁⟫ := by
    rw [hcurvature, inner_sub_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, inner_add_left, hconstraint]
    ring
  have hcoeff : -lambda - ⟪eta, r₁⟫ / ⟪r₁ + P, r₁⟫ =
      -(A * (⟪r₂, r₁⟫ - 2 * ⟪P, r₂⟫ - ⟪U, r₃⟫) + ⟪b₀, r₁⟫) /
        ⟪r₁ + P, r₁⟫ := by
    rw [hinner]
    field_simp
    ring
  nth_rw 1 [hcurvature]
  rw [curveGraphLower, smul_add]
  calc
    _ = A • Q + (A • r₂ + b₀) +
        (-lambda - ⟪eta, r₁⟫ / ⟪r₁ + P, r₁⟫) • (r₁ + P) := by
      rw [sub_smul, neg_smul]
      abel
    _ = _ := by rw [hcoeff]; abel

/-- Nonzero scalar diffusion recovers the actual graph second derivative
from curvature and first-order graph data. MT2007 Claim 19.1, p. 437;
graph comparison components, section 2. -/
theorem graph_acceleration_recovery
    {Q eta B V r₁ : E} {A : ℝ} (hA : A ≠ 0)
    (hgraph : eta - (⟪eta, r₁⟫ / ⟪V, r₁⟫) • V = A • Q + B) :
    Q = A⁻¹ • (eta - (⟪eta, r₁⟫ / ⟪V, r₁⟫) • V - B) := by
  rw [hgraph, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hA, one_smul]

/-- Continuous curvature and first graph jets give continuity of the
actual second graph derivative through the initial time. MT2007
Claim 19.1, p. 437; graph comparison components, section 2. The
domain is arbitrary, and the time equation is not an input. -/
theorem continuousOn_graph_acceleration
    {Z : Type*} [TopologicalSpace Z] {s : Set Z}
    {A : Z → ℝ} {B V r₁ eta Q : Z → E}
    (hA : ContinuousOn A s) (hB : ContinuousOn B s)
    (hV : ContinuousOn V s) (hr₁ : ContinuousOn r₁ s)
    (heta : ContinuousOn eta s)
    (hAne : ∀ z ∈ s, A z ≠ 0) (hd : ∀ z ∈ s, ⟪V z, r₁ z⟫ ≠ 0)
    (hgraph : ∀ z ∈ s,
      eta z - (⟪eta z, r₁ z⟫ / ⟪V z, r₁ z⟫) • V z = A z • Q z + B z) :
    ContinuousOn Q s := by
  have hproj : ContinuousOn
      (fun z => eta z - (⟪eta z, r₁ z⟫ / ⟪V z, r₁ z⟫) • V z - B z) s :=
    (heta.sub (((heta.inner hr₁).div (hV.inner hr₁) hd).smul hV)).sub hB
  exact ((hA.inv₀ hAne).smul hproj).congr
    (fun z hz => graph_acceleration_recovery (hAne z hz) (hgraph z hz))

end PoincareMT.M63

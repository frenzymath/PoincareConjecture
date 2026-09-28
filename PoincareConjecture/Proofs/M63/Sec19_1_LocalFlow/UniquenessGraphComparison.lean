import PoincareConjecture.Proofs.M63.Mathlib.PeriodicVectorEquality












set_option autoImplicit false

open Set
open scoped RealInnerProductSpace

namespace PoincareConjecture.M63

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]





noncomputable def curveGraphLower (A : ℝ) (b₀ r₁ r₂ r₃ U P : E) : E :=
  A • r₂ + b₀ +
    (-(A * (⟪r₂, r₁⟫ - 2 * ⟪P, r₂⟫ - ⟪U, r₃⟫) + ⟪b₀, r₁⟫) /
      ⟪r₁ + P, r₁⟫) • (r₁ + P)





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




theorem graph_acceleration_recovery
    {Q eta B V r₁ : E} {A : ℝ} (hA : A ≠ 0)
    (hgraph : eta - (⟪eta, r₁⟫ / ⟪V, r₁⟫) • V = A • Q + B) :
    Q = A⁻¹ • (eta - (⟪eta, r₁⟫ / ⟪V, r₁⟫) • V - B) := by
  rw [hgraph, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hA, one_smul]





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

end PoincareConjecture.M63

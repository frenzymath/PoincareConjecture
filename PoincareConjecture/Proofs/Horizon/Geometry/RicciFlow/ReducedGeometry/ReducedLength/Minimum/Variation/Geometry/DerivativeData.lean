import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Extension.Section
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Tangent








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe uV vV

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type uV} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_parametricVelocityExtension {I U : Set ℝ} (hU : IsOpen U)
    (hsub : I ⊆ U) (hI : UniqueDiffOn ℝ I) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U) :
    Nonempty (ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I)) := by
  have hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
        (curveVelocity (n := n) α s)) U :=
    contMDiffOn_mfderiv_const_apply hU α hα 1
  obtain ⟨E⟩ := exists_parametricSectionExtension hU α hα (curveVelocity (n := n) α) hY
  refine ⟨{
    extension := E.extension
    domain := E.domain
    open_domain := E.open_domain
    graph_mem := fun s hs ↦ E.graph_mem s (hsub hs)
    smooth := E.smooth
    agrees := ?_ }⟩
  intro s hs
  rw [E.agrees s (hsub hs)]
  unfold curveVelocityWithin curveVelocity
  rw [mfderivWithin_eq_mfderiv (hI.uniqueMDiffOn s hs)
    (((hα s (hsub hs)).contMDiffAt (hU.mem_nhds (hsub hs))).mdifferentiableAt (by simp))]

theorem exists_variationDerivativeData {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) : Nonempty (LVariationDerivativeData V) := by
  classical
  let U := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain
  have hU : IsOpen U := V.square_open.preimage (continuous_id.prodMk continuous_const)
  have hsub : sqrtParameterInterval τ₁ τ₂ ⊆ U := by
    intro s hs
    exact V.square_contains ⟨hs, neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ V.baseSquareCurve U :=
    V.square_smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun s hs ↦ hs)
  have hC : UniqueDiffOn ℝ (sqrtParameterInterval τ₁ τ₂) :=
    uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  obtain ⟨Evelocity⟩ := exists_parametricVelocityExtension hU hsub hC V.baseSquareCurve hα
  obtain ⟨Evariation⟩ := exists_parametricSectionExtension hU V.baseSquareCurve hα
    (squareVariationField V) (squareVariationField_contMDiffOn V)
  have hendpoint (s : ℝ) (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
      Nonempty (ParametricAlongCurveExtensionOn V.parameterDomain (V.squareFamily s)
        (curveVelocityWithin (n := n) (V.squareFamily s) V.parameterDomain)) := by
    apply exists_parametricVelocityExtension isOpen_Ioo Subset.rfl isOpen_Ioo.uniqueDiffOn
      (V.squareFamily s)
    exact V.square_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun t ht ↦ V.square_contains ⟨hs, ht⟩)
  exact ⟨{
    velocity_extension := Evelocity
    variation_extension := restrictParametricSectionExtension hsub Evariation
    endpoint_extension := fun s hs ↦ Classical.choice (hendpoint s hs) }⟩

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

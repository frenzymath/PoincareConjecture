import PoincareConjecture.Proofs.M14.Sec6_3_FamilyActionComparison
import PoincareConjecture.Proofs.M14.Sec6_3_ActionFirstVariation










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}




theorem fderiv_squareFamilyAction_euler_line
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) R.horizontal_velocity)
    (hEuler : ∀ s ∈ M14SqrtParameterInterval a b, ∀ W,
      M14SquareRootEulerResidual G R E s W = 0)
    (V : M14LVariationData G p R) (γ : ℝ × P → G.Point) {C : Set ℝ} {U : Set P}
    (hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P))) (spacetimeModel n) ∞ γ (C ×ˢ U))
    (hsub : M14SqrtParameterInterval a b ⊆ C)
    (hclock : ∀ s ∈ C, ∀ z ∈ U, G.spacetime.timeFunction (γ (s, z)) = T - s ^ 2)
    (z d : P) (hparam : ∀ u ∈ V.parameterDomain, z + u • d ∈ U)
    (hV : ∀ s ∈ M14SqrtParameterInterval a b, ∀ u, V.squareFamily s u = γ (s, z + u • d))
    (hzero : M14VariationField V (Real.sqrt a) = 0)
    (hdiff : DifferentiableAt ℝ (squareFamilyAction G γ C (Real.sqrt a) (Real.sqrt b)) z) :
    fderiv ℝ (squareFamilyAction G γ C (Real.sqrt a) (Real.sqrt b)) z d =
      G.spacetime.horizontalMetric.inner (R.curve (Real.sqrt b))
        (R.horizontal_velocity (Real.sqrt b)) (M14VariationField V (Real.sqrt b)) := by
  have hfirst := firstVariation_euler_fixedInitial hCoordinates hM12 E hEuler V hzero
  have h0 : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have heq : (fun u => squareFamilyAction G γ C (Real.sqrt a) (Real.sqrt b) (z + u • d)) =ᶠ[𝓝 0]
      M14VariationAction V := by
    filter_upwards [hP.mem_nhds h0] with u hu
    exact (variationAction_eq_squareFamilyAction hM12 V γ hγ hsub hclock hu
      (hparam u hu) (fun s hs => hV s hs u)).symm
  have hline : HasDerivAt (fun u : ℝ => z + u • d) d 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add z
  have hactual := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline
    (by simp only [zero_smul, add_zero])
  exact hactual.unique (hfirst.congr_of_eventuallyEq heq)

end PoincareConjecture.M14

import PoincareConjecture.Proofs.M14.Sec6_3_SquareFamilyAction
import PoincareConjecture.Proofs.M14.Sec6_3_SquareCurveAction
import PoincareConjecture.Proofs.M14.Sec6_2_VariationActionComparison










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}




theorem variationAction_eq_squareFamilyAction (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (γ : ℝ × P → G.Point) {C : Set ℝ} {U : Set P}
    (hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P))) (spacetimeModel n) ∞ γ (C ×ˢ U))
    (hsub : M14SqrtParameterInterval a b ⊆ C)
    (hclock : ∀ s ∈ C, ∀ z ∈ U, G.spacetime.timeFunction (γ (s, z)) = T - s ^ 2)
    {u : ℝ} (hu : u ∈ V.parameterDomain) {z : P} (hz : z ∈ U)
    (hV : ∀ s ∈ M14SqrtParameterInterval a b, V.squareFamily s u = γ (s, z)) :
    M14VariationAction V u = squareFamilyAction G γ C (Real.sqrt a) (Real.sqrt b) z := by
  let α := fun s => γ (s, z)
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α C :=
    hγ.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hs => ⟨hs, hz⟩)
  have htime (s : ℝ) (hs : s ∈ M14SqrtParameterInterval a b) :
      G.spacetime.timeFunction (α s) = T - s ^ 2 := hclock s (hsub hs) z hz
  let S := squareRootPathOfSquareCurve hM12 p.tau_nonneg p.tau_lt α (hα.mono hsub) htime
  have haction := variationAction_eq_of_squareFamily V S hu (fun s hs =>
    (hV s hs).trans (squareRootPathOfSquareCurve_curve hM12 p.tau_nonneg p.tau_lt
      α (hα.mono hsub) htime hs).symm)
  exact haction.trans
    (integral_squareCurveDensity_eq_action hM12 p.tau_nonneg p.tau_lt α hα hsub htime).symm

end PoincareConjecture.M14

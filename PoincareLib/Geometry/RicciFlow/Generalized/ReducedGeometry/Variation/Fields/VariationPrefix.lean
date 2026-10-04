import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Action.SquarePathPrefix

/-!
# Restricting actual variations to a prefix

Morgan-Tian Lemma 6.4 and Proposition 6.30, pp. 107-108, 118-119.
The original family, parameter interval and variation field are retained.
The new final endpoint is allowed to move with the parameter.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b c : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}

/-- Restrict an actual variation to a nondegenerate prefix, retaining
the whole square family and actual field, Proposition 6.30, pp. 118-119. -/
def prefixVariation (V : M14LVariationData G p R) (hac : a < c) (hcb : c ≤ b) :
    M14LVariationData G (prefixPath p c hac hcb) (prefixSquarePath R hac hcb) := by
  have hsub : M14SqrtParameterInterval a c ⊆ M14SqrtParameterInterval a b :=
    Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hcb)
  refine {
    family := V.family
    family_velocity := V.family_velocity
    family_at_zero := V.family_at_zero
    radius := V.radius
    radius_pos := V.radius_pos
    parameterDomain := V.parameterDomain
    parameterDomain_eq := V.parameterDomain_eq
    parameterDomain_nonempty := V.parameterDomain_nonempty
    family_time := fun u hu s hs => V.family_time u hu s ⟨hs.1, hs.2.trans hcb⟩
    family_derivative := fun u hu s hs => V.family_derivative u hu s
      ⟨hs.1, hs.2.trans_le hcb⟩
    squareFamily := V.squareFamily
    squareDomain := V.squareDomain
    square_contains := fun z hz => V.square_contains ⟨hsub hz.1, hz.2⟩
    square_smooth := V.square_smooth
    square_agrees := fun s hs u hu => V.square_agrees s (hsub hs) u hu
    square_base := V.square_base
    square_horizontal_velocity := V.square_horizontal_velocity
    square_horizontal_agrees := fun s hs u hu => V.square_horizontal_agrees s (hsub hs) u hu
    left_endpoint_fixed := V.left_endpoint_fixed
    left_endpoint_fixed_spec := V.left_endpoint_fixed_spec
    right_endpoint_fixed := ∀ u ∈ V.parameterDomain, V.family c u = p.curve c
    right_endpoint_fixed_spec := Iff.rfl
    action_integrable := ?_ }
  intro u hu
  apply (V.action_integrable u hu).mono_set
  rw [uIcc_of_le hac.le, uIcc_of_le p.tau_lt.le]
  exact Icc_subset_Icc le_rfl hcb

/-- The frozen field is unchanged at every parameter value by the
prefix construction, Proposition 6.30, pp. 118-119. -/
theorem variationField_prefixVariation (V : M14LVariationData G p R)
    (hac : a < c) (hcb : c ≤ b) (s : ℝ) :
    M14VariationField (prefixVariation V hac hcb) s = M14VariationField V s := rfl

end PoincareMT.M14

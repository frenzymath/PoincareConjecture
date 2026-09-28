import PoincareConjecture.Proofs.M14.Sec6_2_SquarePathPrefix









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b c : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}



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



theorem variationField_prefixVariation (V : M14LVariationData G p R)
    (hac : a < c) (hcb : c ≤ b) (s : ℝ) :
    M14VariationField (prefixVariation V hac hcb) s = M14VariationField V s := rfl

end PoincareConjecture.M14

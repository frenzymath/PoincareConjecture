import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Basic

/-!
# Transporting actual pullback extensions

Morgan-Tian Lemma 6.4, pp. 107-108. Equal base curves and fields equal
on their parameter set identify pullback extensions without changing
their parameter-dependent sections or their actual derivatives.
-/

set_option autoImplicit false
-- Equal base points identify the frozen dependent horizontal tangent fibers.
set_option backward.isDefEq.respectTransparency false

open scoped Manifold

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ γ' : ℝ → G.Point} {J : Set ℝ}
  {Y : ∀ s, G.Horizontal (γ s)} {Y' : ∀ s, G.Horizontal (γ' s)}

/-- Transport an actual extension along an equality of base curves
and on-set equality of fields; Lemma 6.4, pp. 107-108. -/
def pullbackExtensionCongr (E : M14PullbackExtension G γ J Y)
    (hγ : γ = γ') (hY : ∀ s ∈ J, HEq (Y s) (Y' s)) :
    M14PullbackExtension G γ' J Y' := by
  subst γ'
  exact { E with agrees := fun s hs => (E.agrees s hs).trans (eq_of_heq (hY s hs)) }

/-- Transporting the curve and its field preserves the exact frozen
pullback derivative; Lemma 6.4, pp. 107-108. -/
theorem horizontalCovariantDerivative_congr
    (E : M14PullbackExtension G γ J Y) (hγ : γ = γ')
    (hY : ∀ s ∈ J, HEq (Y s) (Y' s)) (s : ℝ) :
    HEq (M14HorizontalCovariantDerivative G γ J Y E s)
      (M14HorizontalCovariantDerivative G γ' J Y' (pullbackExtensionCongr E hγ hY) s) := by
  subst γ'
  rfl

private theorem section_apply_heq (S : HorizontalSection G.spacetime)
    {q r : G.Point} (h : q = r) : HEq (S q) (S r) := by
  cases h
  rfl

/-- On-set equality of base curves and fields transports an actual
pullback extension, including closed endpoints, Lemma 6.8, pp. 108-109. -/
def pullbackExtensionCongrOn (E : M14PullbackExtension G γ J Y)
    (hγ : Set.EqOn γ γ' J) (hY : ∀ s ∈ J, HEq (Y s) (Y' s)) :
    M14PullbackExtension G γ' J Y' where
  extension := E.extension
  domain := E.domain
  domain_open := E.domain_open
  graph_mem := fun s hs => hγ hs ▸ E.graph_mem s hs
  spatial_smooth := E.spatial_smooth
  joint_smooth := by
    obtain ⟨U, hU, hgraph, hsmooth⟩ := E.joint_smooth
    exact ⟨U, hU, fun s hs => hγ hs ▸ hgraph s hs, hsmooth⟩
  agrees := by
    intro s hs
    exact eq_of_heq ((section_apply_heq (E.extension s) (hγ hs).symm).trans
      ((heq_of_eq (E.agrees s hs)).trans (hY s hs)))
  parameter_derivative := by
    intro s hs
    rw [← hγ hs]
    exact E.parameter_derivative s hs

private theorem pullbackDerivative_heq (S : ℝ → HorizontalSection G.spacetime)
    {q r : G.Point} (h : q = r) {v : TangentSpace (spacetimeModel n) q}
    {w : TangentSpace (spacetimeModel n) r} (hv : HEq v w) (s : ℝ) :
    HEq (deriv (fun t => S t q) s + rawHorizontalCovariantDerivative G.leafwise (S s) q v)
      (deriv (fun t => S t r) s + rawHorizontalCovariantDerivative G.leafwise (S s) r w) := by
  cases h
  cases hv
  rfl

/-- The actual within pullback derivative respects equality on the
parameter set, including its endpoints, Lemma 6.8, pp. 108-109. -/
theorem horizontalCovariantDerivative_congrOn
    (E : M14PullbackExtension G γ J Y) (hγ : Set.EqOn γ γ' J)
    (hY : ∀ s ∈ J, HEq (Y s) (Y' s)) {s : ℝ} (hs : s ∈ J) :
    HEq (M14HorizontalCovariantDerivative G γ J Y E s)
      (M14HorizontalCovariantDerivative G γ' J Y' (pullbackExtensionCongrOn E hγ hY) s) := by
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ))
    (I' := spacetimeModel n) hγ hs
  dsimp only [M14HorizontalCovariantDerivative, pullbackExtensionCongrOn]
  apply pullbackDerivative_heq (G := G) E.extension (hγ hs) (s := s)
  exact heq_of_eq (congrArg (fun A => A (1 : ℝ)) hd)

end PoincareMT.M14

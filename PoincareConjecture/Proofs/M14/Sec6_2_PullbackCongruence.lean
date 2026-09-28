import PoincareConjecture.Definitions.M14PathCalculus









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ γ' : ℝ → G.Point} {J : Set ℝ}
  {Y : ∀ s, G.Horizontal (γ s)} {Y' : ∀ s, G.Horizontal (γ' s)}



def pullbackExtensionCongr (E : M14PullbackExtension G γ J Y)
    (hγ : γ = γ') (hY : ∀ s ∈ J, HEq (Y s) (Y' s)) :
    M14PullbackExtension G γ' J Y' := by
  subst γ'
  exact { E with agrees := fun s hs => (E.agrees s hs).trans (eq_of_heq (hY s hs)) }



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

end PoincareConjecture.M14

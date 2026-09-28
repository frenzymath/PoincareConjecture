import PoincareConjecture.Definitions.M14PathCalculus

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}

theorem horizontalCovariantDerivative_eq_zero_of_constant
    (E : M14PullbackExtension G γ J Y) {s : ℝ} (hs : s ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J s)
    (hγ : Set.EqOn γ (fun _ => γ s) J)
    (hY : ∀ r ∈ J, Y r = 0) :
    M14HorizontalCovariantDerivative G γ J Y E s = 0 := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have hext : ∀ r ∈ J, E.extension r (γ s) = 0 := by
    intro r hr
    have he : E.extension r (γ r) = 0 := (E.agrees r hr).trans (hY r hr)
    have hp : γ r = γ s := hγ hr
    exact hp ▸ he
  obtain ⟨d, hd⟩ := E.parameter_derivative s hs
  have hzero : HasDerivWithinAt (fun r => E.extension r (γ s))
      (0 : G.Horizontal (γ s)) J s :=
    (hasDerivWithinAt_const s J (0 : G.Horizontal (γ s))).congr_of_mem hext hs
  have hpar : deriv (fun r => E.extension r (γ s)) s = 0 :=
    hd.deriv.trans ((hd.hasDerivWithinAt.derivWithin hJ).symm.trans
      (hzero.derivWithin hJ))
  have hder : (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s :
      ℝ →L[ℝ] SpacetimeModelVector n) = 0 :=
    (mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n) hγ hs).trans
      mfderivWithin_const
  have hvel : mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ) =
      (0 : TangentSpace (spacetimeModel n) (γ s)) :=
    congrArg (fun L : ℝ →L[ℝ] SpacetimeModelVector n => L 1) hder
  simp only [M14HorizontalCovariantDerivative, hpar, hvel, map_zero, add_zero]

end PoincareConjecture.M14

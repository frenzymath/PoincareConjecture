import PoincareConjecture.Proofs.M14.Sec6_2_PullbackCongruence
import PoincareConjecture.Proofs.M14.Sec6_2_SquareRootVelocityExtension
import PoincareConjecture.Proofs.M14.Sec6_2_EulerResidual










set_option autoImplicit false

open scoped Manifold

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}



theorem squareRoot_curve_eqOn (R S : M14SquareRootPath G p) :
    Set.EqOn R.curve S.curve (M14SqrtParameterInterval τ₁ τ₂) :=
  fun s hs => (R.agrees s hs).trans (S.agrees s hs).symm

private theorem horizontalProjection_heq {q r : G.Point} (h : q = r)
    {v : TangentSpace (spacetimeModel n) q} {w : TangentSpace (spacetimeModel n) r}
    (hv : HEq v w) :
    HEq (G.spacetime.horizontalProjection q v) (G.spacetime.horizontalProjection r w) := by
  cases h
  cases hv
  rfl



theorem squareRoot_horizontalVelocity_heq (R S : M14SquareRootPath G p)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    HEq (R.horizontal_velocity s) (S.horizontal_velocity s) := by
  rw [squareRoot_horizontalVelocity_eq_projection R hs,
    squareRoot_horizontalVelocity_eq_projection S hs]
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := spacetimeModel n)
    (squareRoot_curve_eqOn R S) hs
  exact horizontalProjection_heq (G := G) (squareRoot_curve_eqOn R S hs)
    (heq_of_eq (congrArg (fun A => A (1 : ℝ)) hd))

private theorem squareEulerPair_heq {q r : G.Point} (h : q = r)
    {A V W : G.Horizontal q} {A' V' W' : G.Horizontal r}
    (hA : HEq A A') (hV : HEq V V') (hW : HEq W W') (s : ℝ) :
    G.spacetime.horizontalMetric.inner q A W -
        2 * s ^ 2 * M14HorizontalScalarDifferential G q W.val +
        4 * s * horizontalRicci G.leafwise q V W =
      G.spacetime.horizontalMetric.inner r A' W' -
        2 * s ^ 2 * M14HorizontalScalarDifferential G r W'.val +
        4 * s * horizontalRicci G.leafwise r V' W' := by
  cases h
  cases hA
  cases hV
  cases hW
  rfl



theorem squareRootEulerResidual_congr (R S : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      R.horizontal_velocity)
    (F : M14PullbackExtension G S.curve (M14SqrtParameterInterval τ₁ τ₂)
      S.horizontal_velocity) {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂)
    {W : G.Horizontal (R.curve s)} {W' : G.Horizontal (S.curve s)} (hW : HEq W W') :
    M14SquareRootEulerResidual G R E s W = M14SquareRootEulerResidual G S F s W' := by
  let E' := pullbackExtensionCongrOn E (squareRoot_curve_eqOn R S)
    (fun _ ht => squareRoot_horizontalVelocity_heq R S ht)
  have hd := horizontalCovariantDerivative_congrOn E (squareRoot_curve_eqOn R S)
    (fun _ ht => squareRoot_horizontalVelocity_heq R S ht) hs
  have hp := squareEulerPair_heq (G := G) (squareRoot_curve_eqOn R S hs) hd
    (squareRoot_horizontalVelocity_heq R S hs) hW s
  change M14SquareRootEulerResidual G R E s W =
    M14SquareRootEulerResidual G S E' s W' at hp
  exact hp.trans (squareRootEulerResidual_extension_independent E' F hs W')

end PoincareConjecture.M14

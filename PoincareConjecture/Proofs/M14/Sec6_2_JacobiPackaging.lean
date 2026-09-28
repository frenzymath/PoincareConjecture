import PoincareConjecture.Proofs.M14.Sec6_2_JacobiPair









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J : Set ℝ} {Y P : ∀ s, G.Horizontal (γ s)}




def jacobiFieldOfPair (EY : M14PullbackExtension G γ J Y)
    (EP : M14PullbackExtension G γ J P)
    (hP : ∀ s ∈ J, M14HorizontalCovariantDerivative G γ J Y EY s = P s) :
    M14JacobiFieldData G γ J where
  field := Y
  extension := EY
  derivative_extension := { EP with
    agrees := fun s hs => (EP.agrees s hs).trans (hP s hs).symm }



theorem jacobiFieldOfPair_firstDerivative (EY : M14PullbackExtension G γ J Y)
    (EP : M14PullbackExtension G γ J P)
    (hP : ∀ s ∈ J, M14HorizontalCovariantDerivative G γ J Y EY s = P s)
    {s : ℝ} (hs : s ∈ J) : M14JacobiFirstDerivative (jacobiFieldOfPair EY EP hP) s = P s :=
  hP s hs



theorem jacobiFieldOfPair_secondDerivative (EY : M14PullbackExtension G γ J Y)
    (EP : M14PullbackExtension G γ J P)
    (hP : ∀ s ∈ J, M14HorizontalCovariantDerivative G γ J Y EY s = P s) (s : ℝ) :
    M14JacobiSecondDerivative (jacobiFieldOfPair EY EP hP) s =
      M14HorizontalCovariantDerivative G γ J P EP s := rfl

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}




theorem jacobiField_isHorizontalJacobiPair
    (Q : M14JacobiFieldData G R.curve (M14SqrtParameterInterval τ₁ τ₂))
    (hQ : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
      ∀ W : G.Horizontal (R.curve s), M14JacobiResidual G R Q s W = 0) :
    IsHorizontalJacobiPairOn R (Real.sqrt τ₁) (Real.sqrt τ₂)
      (fun s => (Q.field s, M14JacobiFirstDerivative Q s)) := by
  have hR := R.smooth.mono R.interval_subset
  refine ⟨Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt, Subset.rfl,
    pullbackExtension_field_contMDiffOn Q.extension hR,
    pullbackExtension_field_contMDiffOn Q.derivative_extension hR,
    Q.extension, Q.derivative_extension, fun _ _ => rfl, ?_⟩
  exact hQ




theorem IsHorizontalJacobiPairOn.exists_jacobiField
    {z : ∀ s, G.Horizontal (R.curve s) × G.Horizontal (R.curve s)}
    (h : IsHorizontalJacobiPairOn R (Real.sqrt τ₁) (Real.sqrt τ₂) z) :
    ∃ Q : M14JacobiFieldData G R.curve (M14SqrtParameterInterval τ₁ τ₂),
      Q.field = (fun s => (z s).1) ∧
      (∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, M14JacobiFirstDerivative Q s = (z s).2) ∧
      ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
        ∀ W : G.Horizontal (R.curve s), M14JacobiResidual G R Q s W = 0 := by
  obtain ⟨EY, EP, hY, hP⟩ := h.equations
  refine ⟨jacobiFieldOfPair EY EP hY, rfl,
    fun _ hs => jacobiFieldOfPair_firstDerivative EY EP hY hs, ?_⟩
  intro s hs W
  change horizontalJacobiPairResidual R s (z s).1
    (M14HorizontalCovariantDerivative G R.curve (Icc (Real.sqrt τ₁) (Real.sqrt τ₂))
      (fun r => (z r).1) EY s)
    (M14HorizontalCovariantDerivative G R.curve (Icc (Real.sqrt τ₁) (Real.sqrt τ₂))
      (fun r => (z r).2) EP s) W = 0
  rw [hY s hs]
  exact hP s hs W

end PoincareConjecture.M14

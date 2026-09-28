import PoincareConjecture.Definitions.M14Exponential











set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M34

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}




theorem exists_squareInitialValue_of_euler {T tau : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T 0 tau x y) (S : M14SquareRootPath G p)
    (E : M14PullbackExtension G S.curve (M14SqrtParameterInterval 0 tau) S.horizontal_velocity)
    (hEuler : ∀ s ∈ M14SqrtParameterInterval 0 tau, ∀ W,
      M14SquareRootEulerResidual G S E s W = 0) :
    ∃ Z : G.Horizontal x, Nonempty (M14SquareRootInitialValuePath G T tau x y Z) := by
  have hzero : 0 ∈ M14SqrtParameterInterval 0 tau := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Set.mem_Icc] using
      (show 0 ≤ (0 : ℝ) ∧ 0 ≤ Real.sqrt tau from ⟨le_rfl, Real.sqrt_nonneg _⟩)
  have h : S.curve 0 = x := (S.agrees 0 hzero).trans (by simpa using p.curve_start)
  let V : G.Horizontal x := h ▸ S.horizontal_velocity 0
  refine ⟨(1 / 2 : ℝ) • V, ⟨{
    path := p
    square_path := S
    extension := E
    euler := hEuler
    initial_velocity := ⟨h, ?_⟩ }⟩⟩
  change V = (2 : ℝ) • ((1 / 2 : ℝ) • V)
  rw [smul_smul]
  norm_num

end PoincareConjecture.M34

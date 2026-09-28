import PoincareConjecture.Statements.M14GeneralizedLGeometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem exists_stableSet_of_minimizing
    (H : GeneralizedLGeometryConclusion G)
    {T tau : ℝ} {x y : G.Point}
    (E : M14ExponentialFamily G T x)
    (p : M14BackwardPath G T 0 tau x y) (hp : M14IsMinimizing p) :
    Nonempty (M14StableSet G T tau x E) := by
  obtain ⟨E0, hE0⟩ := H.path_calculus.minimizer_euler T 0 tau x y p hp
  obtain ⟨R, ER, hER⟩ := H.path_calculus.square_root_regularization T 0 tau x y p E0 hE0
  have hzero : R.curve 0 = x := by
    have hz : (0 : ℝ) ∈ M14SqrtParameterInterval 0 tau := by
      simp only [M14SqrtParameterInterval, Real.sqrt_zero, mem_Icc, le_refl,
        Real.sqrt_nonneg, and_self]
    simpa only [zero_pow (by norm_num : 2 ≠ 0), p.curve_start] using R.agrees 0 hz
  let A : G.Horizontal x := hzero ▸ R.horizontal_velocity 0
  let Z : G.Horizontal x := (1 / 2 : ℝ) • A
  have hIVP : Nonempty (M14SquareRootInitialValuePath G T tau x y Z) := by
    refine ⟨{
      path := p
      square_path := R
      extension := ER
      euler := hER
      initial_velocity := ⟨hzero, ?_⟩
    }⟩
    change A = (2 : ℝ) • ((1 / 2 : ℝ) • A)
    simp only [smul_smul, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  have hroot : 0 < Real.sqrt tau := Real.sqrt_pos.mpr p.tau_lt
  have hsurvive : (Z, Real.sqrt tau) ∈ E.domain := by
    apply (E.positive_survival_iff Z (Real.sqrt tau) hroot).mpr
    refine ⟨y, ?_⟩
    simpa only [Real.sq_sqrt p.tau_lt.le] using hIVP
  exact H.exponential.stable T tau x E.base_time p.tau_lt E ⟨Z, hsurvive⟩

end PoincareConjecture.Proofs.M15

import PoincareConjecture.Proofs.M14.Sec6_6_RescalingSquareInverse
import PoincareConjecture.Definitions.M14Exponential

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

private theorem horizontal_cast_val (S : GeneralizedFlowSpacetime n X time I)
    {p q : S.Point} (h : p = q) (v : S.Horizontal p) :
    (show SpacetimeModelVector n from (h ▸ v : S.Horizontal q).val) = v.val := by
  cases h
  rfl

theorem rescalingSquare_initial_vector
    {T τ : ℝ} {x y : G.Point} {Z : G.Horizontal x}
    (P : M14SquareRootInitialValuePath G T τ x y Z)
    (R : M14SquareRootPath (rescalingTransport hM12 hM13 G Q hQ a)
      (rescalingPath hM12 hM13 G Q hQ a P.path)) :
    ∃ h : R.curve 0 = x,
      h ▸ R.horizontal_velocity 0 = (2 : ℝ) • rescalingInitialEquiv G.spacetime Q hQ a x Z := by
  have h0 : 0 ∈ M14SqrtParameterInterval (Q * 0) (Q * τ) := by
    simp [M14SqrtParameterInterval, Real.sqrt_nonneg]
  have hc : R.curve 0 = x := by
    rw [R.agrees 0 h0]
    change P.path.curve (0 ^ 2 / Q) = x
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] using P.path.curve_start
  obtain ⟨hP, hZ⟩ := P.initial_velocity
  have hval : (P.square_path.horizontal_velocity 0).val = ((2 : ℝ) • Z).val :=
    (horizontal_cast_val G.spacetime hP (P.square_path.horizontal_velocity 0)).symm.trans
      (congrArg (fun V : G.Horizontal x => V.val) hZ)
  have hid := rescalingSquare_initial_velocity hM12 hM13 G Q hQ a P.square_path R
  rw [hval] at hid
  refine ⟨hc, Subtype.ext ?_⟩
  refine (horizontal_cast_val (rescalingTransport hM12 hM13 G Q hQ a).spacetime
    hc (R.horizontal_velocity 0)).trans ?_
  change (R.horizontal_velocity 0).val =
    (2 : ℝ) • ((Real.sqrt Q)⁻¹ • (show SpacetimeModelVector n from Z.val))
  simpa only [Submodule.coe_smul, smul_smul, mul_comm] using hid

theorem rescalingSquareInverse_initial_vector
    {T τ : ℝ} {x y : G.Point} {Z : G.Horizontal x}
    {p : M14BackwardPath (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * 0) (Q * τ) x y}
    (R : M14SquareRootPath (rescalingTransport hM12 hM13 G Q hQ a) p)
    (hinitial : ∃ h : R.curve 0 = x,
      h ▸ R.horizontal_velocity 0 = (2 : ℝ) • rescalingInitialEquiv G.spacetime Q hQ a x Z)
    (R' : M14SquareRootPath G (rescalingPathInverse hM12 hM13 G Q hQ a p)) :
    ∃ h : R'.curve 0 = x, h ▸ R'.horizontal_velocity 0 = (2 : ℝ) • Z := by
  have h0 : 0 ∈ M14SqrtParameterInterval 0 τ := by
    simp [M14SqrtParameterInterval, Real.sqrt_nonneg]
  have hc : R'.curve 0 = x := by
    rw [R'.agrees 0 h0]
    change p.curve (Q * 0 ^ 2) = x
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using p.curve_start
  obtain ⟨hR, hZ⟩ := hinitial
  have hval : (R.horizontal_velocity 0).val =
      ((2 : ℝ) • rescalingInitialEquiv G.spacetime Q hQ a x Z).val :=
    (horizontal_cast_val (rescalingTransport hM12 hM13 G Q hQ a).spacetime
      hR (R.horizontal_velocity 0)).symm.trans
        (congrArg (fun V : (rescalingTransport hM12 hM13 G Q hQ a).Horizontal x => V.val) hZ)
  have hid := rescalingSquareInverse_initial_velocity hM12 hM13 G Q hQ a R R'
  rw [hval] at hid
  refine ⟨hc, Subtype.ext ?_⟩
  refine (horizontal_cast_val G.spacetime hc (R'.horizontal_velocity 0)).trans ?_
  change (R'.horizontal_velocity 0).val = (2 : ℝ) • Z.val
  change (R'.horizontal_velocity 0).val = Real.sqrt Q •
    ((2 : ℝ) • ((Real.sqrt Q)⁻¹ • (show SpacetimeModelVector n from Z.val))) at hid
  have hscale : Real.sqrt Q * (2 * (Real.sqrt Q)⁻¹) = 2 := by
    field_simp [(Real.sqrt_pos.mpr hQ).ne']
  simpa only [smul_smul, hscale] using hid

end PoincareConjecture.M14

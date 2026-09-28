import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Rescaling.Time
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ParabolicRescaling

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}

theorem parabolicClock_smooth (S : GeneralizedFlowSpacetime n X time I) (Q a : ℝ) :
    ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞
      (fun p : S.Point ↦ parabolicTime Q a (S.timeFunction p)) := by
  have h : ContDiff ℝ ∞ (parabolicTime Q a) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  exact h.contMDiff.comp S.time_smooth

theorem parabolicClock_derivative (S : GeneralizedFlowSpacetime n X time I)
    (Q a : ℝ) (p : S.Point) (Z : TangentSpace (spacetimeModel n) p) :
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
      (fun q : S.Point ↦ parabolicTime Q a (S.timeFunction q)) p Z) =
      Q * (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) S.timeFunction p Z) := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) X :=
    S.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ X := S.isManifold
  have ht : HasDerivAt (parabolicTime Q a) Q (S.timeFunction p) := by
    convert! ((hasDerivAt_id (S.timeFunction p)).sub_const a).const_mul Q using 1
    simp
  have h := ht.hasFDerivAt.hasMFDerivAt.comp p
    (S.time_smooth.mdifferentiable (by simp) p).hasMFDerivAt
  have hvalue := congrArg (fun L : SpacetimeModelVector n →L[ℝ] ℝ ↦ L Z) h.mfderiv
  change (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
      (fun q : S.Point ↦ parabolicTime Q a (S.timeFunction q)) p Z) =
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) S.timeFunction p Z) * Q at hvalue
  exact hvalue.trans (mul_comm _ _)

theorem parabolicClock_horizontal_eq (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (p : S.Point) :
    spacetimeHorizontal (n := n) (fun q : S.Point ↦ parabolicTime Q a (S.timeFunction q)) p =
      spacetimeHorizontal (n := n) S.timeFunction p := by
  ext Z
  change (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
      (fun q : S.Point ↦ parabolicTime Q a (S.timeFunction q)) p Z) = 0 ↔
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) S.timeFunction p Z) = 0
  rw [parabolicClock_derivative]
  simp only [mul_eq_zero, hQ.ne', false_or]

theorem parabolicClock_range (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    Set.range (fun p : S.Point ↦ parabolicTime Q a (S.timeFunction p)) =
      (parabolicInterval Q hQ a I).domain := by
  change Set.range (parabolicTime Q a ∘ S.timeFunction) = parabolicTime Q a '' I.domain
  rw [Set.range_comp, show Set.range S.timeFunction = I.domain from S.time_range]

theorem parabolicClock_boundary (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (spacetimeModel n).boundary S.Point =
      {p : S.Point | parabolicTime Q a (S.timeFunction p) ∈
        frontier (parabolicInterval Q hQ a I).domain} := by
  let e : ℝ ≃ₜ ℝ := {
    toEquiv := (parabolicTimeOrderIso Q hQ a).toEquiv
    continuous_toFun := continuous_const.mul (continuous_id.sub continuous_const)
    continuous_invFun := continuous_const.add (continuous_id.div_const Q) }
  have he := e.image_frontier I.domain
  change parabolicTime Q a '' frontier I.domain =
    frontier (parabolicInterval Q hQ a I).domain at he
  rw [S.boundary_eq]
  ext p
  change S.timeFunction p ∈ frontier I.domain ↔
    parabolicTime Q a (S.timeFunction p) ∈ frontier (parabolicInterval Q hQ a I).domain
  rw [← he]
  constructor
  · intro hp
    exact ⟨S.timeFunction p, hp, rfl⟩
  · rintro ⟨t, ht, heq⟩
    exact (parabolicTimeOrderIso Q hQ a).injective heq ▸ ht

theorem parabolicTimeVector_smooth (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) :
    ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun p : S.Point ↦ Bundle.TotalSpace.mk' (SpacetimeModelVector n)
        (E := (TangentSpace (spacetimeModel n) : S.Point → Type _)) p
        ((1 / Q : ℝ) • S.timeVector p)) := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) X :=
    S.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ X := S.isManifold
  exact S.timeVector_smooth.const_smul_section

theorem parabolicTimeVector_normalized (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (p : S.Point) :
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
      (fun q : S.Point ↦ parabolicTime Q a (S.timeFunction q)) p
      ((1 / Q : ℝ) • S.timeVector p)) = 1 := by
  rw [parabolicClock_derivative]
  let L : TangentSpace (spacetimeModel n) p →L[ℝ] ℝ :=
    mfderiv (spacetimeModel n) 𝓘(ℝ) S.timeFunction p
  have hnorm : L (S.timeVector p) = 1 := S.timeVector_normalized p
  change Q * L ((1 / Q : ℝ) • S.timeVector p) = 1
  rw [map_smul, hnorm]
  simp only [smul_eq_mul, mul_one, one_div, mul_inv_cancel₀ hQ.ne']

theorem parabolicClock_projection_formula (S : GeneralizedFlowSpacetime n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (p : S.Point)
    (Z : TangentSpace (spacetimeModel n) p) :
    Z - (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
      (fun q : S.Point ↦ parabolicTime Q a (S.timeFunction q)) p Z) •
      ((1 / Q : ℝ) • S.timeVector p) = (S.horizontalProjection p Z).val := by
  have hproj : (S.horizontalProjection p Z).val = Z -
      (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) S.timeFunction p Z) • S.timeVector p :=
    S.horizontalProjection_eq p Z
  rw [parabolicClock_derivative, hproj, smul_smul]
  have hfactor : (Q * (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ)
      S.timeFunction p Z)) * (1 / Q) =
      (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) S.timeFunction p Z) := by
    field_simp [hQ.ne']
  rw [hfactor]

end PoincareConjecture.ParabolicRescaling

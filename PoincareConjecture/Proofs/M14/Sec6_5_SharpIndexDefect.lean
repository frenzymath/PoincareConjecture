import PoincareConjecture.Proofs.M14.Sec6_5_SharpIndexAffine
import PoincareConjecture.Proofs.M08.IndexPositivity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  (R : M14SquareRootPath G p)

theorem pullbackIndexIntegral_eq_of_hessian_bound
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (B : LinearMap.BilinForm ℝ (G.Horizontal (R.curve (Real.sqrt b))))
    (hB : ∀ v w, B v w = B w v) (k : ℝ)
    (hbound : ∀ (W : ∀ s, G.Horizontal (R.curve s))
      (EW : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) W),
      W (Real.sqrt a) = 0 → k * B (W (Real.sqrt b)) (W (Real.sqrt b)) ≤
        ∫ s in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R EW EW s)
    {Y Z : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Y)
    (EZ : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Z)
    (hY : Y (Real.sqrt a) = 0) (hZ : Z (Real.sqrt a) = 0)
    (heq : (∫ s in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R EY EY s) =
      k * B (Y (Real.sqrt b)) (Y (Real.sqrt b))) :
    (∫ s in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R EY EZ s) =
      k * B (Y (Real.sqrt b)) (Z (Real.sqrt b)) := by
  apply sub_eq_zero.mp
  apply M08.mixedTerm_eq_zero_of_quadratic_nonneg
    (C := (∫ s in Real.sqrt a..Real.sqrt b, pullbackIndexPairDensity R EZ EZ s) -
      k * B (Z (Real.sqrt b)) (Z (Real.sqrt b)))
  intro c
  have hc := hbound (fun s => Y s + c • Z s) (affinePullbackExtension EY EZ c)
    (by simp only [hY, hZ, smul_zero, add_zero])
  rw [pullbackIndexIntegral_affine R hM04 hM12 EY EZ c, heq] at hc
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hc
  rw [hB (Z (Real.sqrt b)) (Y (Real.sqrt b))] at hc
  nlinarith only [hc]

end PoincareConjecture.M14

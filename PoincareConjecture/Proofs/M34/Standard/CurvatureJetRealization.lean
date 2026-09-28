import PoincareConjecture.Proofs.M34.Standard.CurvatureJetOperator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap CoordinateExponential

set_option synthInstance.maxHeartbeats 100000 in

theorem metric_spatialJet_mem_curvatureJetDomain {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    spatialJet (2 + m) (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      g.euclideanCoefficients p.2) (0, x) ∈ curvatureJetDomain n m := by
  change ((twoJetProjection n (baseProjection 2 m
    (spatialJet (2 + m) (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      g.euclideanCoefficients p.2) (0, x)))).1).IsInvertible
  rw [baseProjection_spatialJet, twoJetProjection_spatialJet]
  convert! g.inner_isInvertible x

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 800000 in

theorem curvatureJetComponents_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) (I : Fin (4 + m) → Fin n) :
    curvatureJetComponents n m
      (spatialJet (2 + m) (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        g.euclideanCoefficients p.2) (0, x)) I =
      coordinateCurvatureComponent D m (fun j => EuclideanSpace.basisFun (Fin n) ℝ (I j)) x := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let f := fun p : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients p.2
  induction m generalizing x with
  | zero =>
      simp only [curvatureJetComponents, Nat.add_zero, twoJetProjection_spatialJet]
      rw [jetCurvature_metricTwoJet D]
      rfl
  | succ m ih =>
      have hmem := metric_spatialJet_mem_curvatureJetDomain g m x
      have hR := (contDiffOn_curvatureJetComponents n m).contDiffAt
        ((isOpen_curvatureJetDomain n m).mem_nhds hmem)
      have hd := (hR.differentiableAt (by simp)).hasFDerivAt.comp x
        (hasFDerivAt_spatialJet (2 + m) f 0 x (g.contDiffAt_euclideanCoefficients x))
      have hscalar := (ContinuousLinearMap.proj (Fin.tail I)).hasFDerivAt.comp x hd
      have heq : (fun y => curvatureJetComponents n m (spatialJet (2 + m) f (0, y))
          (Fin.tail I)) = coordinateCurvatureComponent D m (fun j => b (Fin.tail I j)) := by
        funext y
        exact ih y (Fin.tail I)
      have hprolong : fderiv ℝ
          (coordinateCurvatureComponent D m (fun j => b (Fin.tail I j))) x (b (I 0)) =
          (prolong (2 + m) (curvatureJetComponents n m)
            (spatialJet (2 + (m + 1)) f (0, x)) (b (I 0))) (Fin.tail I) := by
        have h := congrArg (fun A => A (b (I 0))) hscalar.fderiv
        change fderiv ℝ (fun y => curvatureJetComponents n m (spatialJet (2 + m) f (0, y))
          (Fin.tail I)) x (b (I 0)) = _ at h
        rw [heq] at h
        exact h
      have hrec := fderiv_coordinateCurvatureComponent_eq_sum D b m (Fin.tail I) x (b (I 0))
      simp only [OrthonormalBasis.repr_self, PiLp.single_apply,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Fin.cons_self_tail] at hrec
      change curvatureJetComponents n (m + 1) (spatialJet (2 + (m + 1)) f (0, x)) I = _
      simp only [curvatureJetComponents]
      rw [← hprolong, baseProjection_spatialJet,
        twoJetProjection_spatialJet]
      have htruncate : truncate (2 + m) (spatialJet (2 + (m + 1)) f (0, x)) =
          spatialJet (2 + m) f (0, x) := rfl
      rw [htruncate]
      dsimp only [f, Prod.fst, Prod.snd]
      simp only [ih]
      have hΓ (u v : EuclideanSpace ℝ (Fin n)) :
          jetChristoffel (metricTwoJet g.euclideanCoefficients x) u v =
            christoffelBilinear g.euclideanCoefficients x u v := rfl
      simp only [hΓ]
      change fderiv ℝ (coordinateCurvatureComponent D m (fun j => b (Fin.tail I j))) x
        (b (I 0)) -
        ∑ i : Fin (4 + m), ∑ a : Fin n,
          b.repr (christoffelBilinear g.euclideanCoefficients x (b (I 0))
            (b (Fin.tail I i))) a *
          coordinateCurvatureComponent D m (fun j => b (Function.update (Fin.tail I) i a j)) x = _
      linarith

end PoincareConjecture.M34

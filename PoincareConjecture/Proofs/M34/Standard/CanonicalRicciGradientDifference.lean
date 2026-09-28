import PoincareConjecture.Proofs.M34.Standard.CurvatureDerivativeCoordinates
import PoincareConjecture.Proofs.M34.Standard.ConnectionDifferenceFactorization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem canonicalDomain_ricciGradient_difference
    {n dS : ℕ} (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    (U : Set (V n)) (hU : IsOpen U) [Nonempty U] :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (g0 : RiemannianMetric n U) (D0 : LeviCivitaData g0)
      (g1 : RiemannianMetric n U) (D1 : LeviCivitaData g1) (p : U) (x : V n), x ∈ U →
      ∀ (R0 R1 : V n → FS n),
        (∀ y ∈ U, raw (R0 y) = canonicalDomain_curvatureArray U hU g0 D0 p y) →
        (∀ y ∈ U, raw (R1 y) = canonicalDomain_curvatureArray U hU g1 D1 p y) →
        DifferentiableAt ℝ R0 x → DifferentiableAt ℝ R1 x →
        let C0 := fun i j k => ∑ l : Fin n,
          canonicalDomain_covariantCurvatureArray U hU g0 D0 p x i l l j k
        let C1 := fun i j k => ∑ l : Fin n,
          canonicalDomain_covariantCurvatureArray U hU g1 D1 p x i l l j k
        let A : FA n := CovariantDerivative.difference D0.connection D1.connection
          ((extChartAt (𝓡 n) p).symm x)
        C0 - C1 =
          ricciGradientCoordinates qS
            (fun beta => fderiv ℝ (fun y => qS (R0 y - R1 y) beta.1) x
              (EuclideanSpace.single beta.2 1)) +
          ricciGradientConnection (raw (R1 x)) A +
          ricciGradientCurvature
            (canonicalDomain_differenceEnergyBackground U hU g0 D0 p x).1.2 (R0 x - R1 x) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g0 D0 g1 D1 p x hx R0 R1 hR0 hR1 hd0 hd1 C0 C1 A
  let r := (extChartAt (𝓡 n) p).symm
  let S := fun y => R0 y - R1 y
  let B0 := canonicalDomain_curvatureArray U hU g0 D0 p
  let B1 := canonicalDomain_curvatureArray U hU g1 D1 p
  let gamma0 := (canonicalDomain_differenceEnergyBackground U hU g0 D0 p x).1.2
  let gamma1 := (canonicalDomain_differenceEnergyBackground U hU g1 D1 p x).1.2
  have hsraw (y : V n) (hy : y ∈ U) : raw (S y) = B0 y - B1 y := by
    have hh : raw (S y) = raw (R0 y) - raw (R1 y) := by
      funext l j k m
      simp only [S, raw, map_sub, sub_apply, Pi.sub_apply]
    rw [hh, hR0 y hy, hR1 y hy]
  have hA : ag A = gamma0 - gamma1 := by
    funext i j l
    have hY := (constantChart_contMDiff_const_field (𝓡 n) (canonicalOpen_chart_eq hU)
      (EuclideanSpace.single j (1 : ℝ))).mdifferentiableAt (x := r x) (by simp)
    have hh := IsCovariantDerivativeOn.difference_apply
      D0.connection.isCovariantDerivativeOnUniv D1.connection.isCovariantDerivativeOnUniv
      (mem_univ (r x)) hY
    have hv : A (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) =
        D0.connection (fun _ : U => EuclideanSpace.single j 1) (r x)
            (EuclideanSpace.single i 1) -
          D1.connection (fun _ : U => EuclideanSpace.single j 1) (r x)
            (EuclideanSpace.single i 1) :=
      congrArg (fun L => L (EuclideanSpace.single i 1)) hh
    change EuclideanSpace.proj l (A (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)) = _
    rw [hv, map_sub]
    rfl
  have hb0 := canonicalDomain_differentiableAt_curvatureArray U hU g0 D0 p x hx
  have hb1 := canonicalDomain_differentiableAt_curvatureArray U hU g1 D1 p x hx
  have hcomp0 (l j k : Fin n) : DifferentiableAt ℝ (fun y => B0 y l l j k) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp
      (differentiableAt_pi.mp (differentiableAt_pi.mp hb0 l) l) j) k
  have hcomp1 (l j k : Fin n) : DifferentiableAt ℝ (fun y => B1 y l l j k) x :=
    differentiableAt_pi.mp (differentiableAt_pi.mp
      (differentiableAt_pi.mp (differentiableAt_pi.mp hb1 l) l) j) k
  have hder (i l j k : Fin n) :
      fderiv ℝ (fun y => B0 y l l j k) x (EuclideanSpace.single i 1) -
          fderiv ℝ (fun y => B1 y l l j k) x (EuclideanSpace.single i 1) =
        fderiv ℝ (fun y => raw (S y) l l j k) x (EuclideanSpace.single i 1) := by
    have hgerm : (fun y => raw (S y) l l j k) =ᶠ[𝓝 x]
        (fun y => B0 y l l j k - B1 y l l j k) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact congrFun (congrFun (congrFun (congrFun (hsraw y hy) l) l) j) k
    rw [hgerm.fderiv_eq, fderiv_fun_sub (hcomp0 l j k) (hcomp1 l j k)]
    rfl
  funext i j k
  have hd : (∑ l : Fin n,
      fderiv ℝ (fun y => B0 y l l j k) x (EuclideanSpace.single i 1)) -
        (∑ l : Fin n, fderiv ℝ (fun y => B1 y l l j k) x (EuclideanSpace.single i 1)) =
      ricciGradientCoordinates qS
        (fun beta => fderiv ℝ (fun y => qS (S y) beta.1) x
          (EuclideanSpace.single beta.2 1)) i j k := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [hder]
    exact sum_fderiv_raw_eq_ricciGradientCoordinates qS (hd0.sub hd1) i j k
  have ha := curvatureAction_trace_difference gamma0 gamma1 (B0 x) (B1 x)
    A (S x) hA (hsraw x hx) i j k
  change (∑ l : Fin n, (fderiv ℝ (fun y => B0 y l l j k) x (EuclideanSpace.single i 1) +
      curvatureAction gamma0 i (B0 x) l l j k)) -
      (∑ l : Fin n, (fderiv ℝ (fun y => B1 y l l j k) x (EuclideanSpace.single i 1) +
        curvatureAction gamma1 i (B1 x) l l j k)) = _
  simp only [Finset.sum_add_distrib]
  change _ = ricciGradientCoordinates qS
      (fun beta => fderiv ℝ (fun y => qS (S y) beta.1) x
        (EuclideanSpace.single beta.2 1)) i j k +
    ricciGradientConnection (raw (R1 x)) A i j k + ricciGradientCurvature gamma0 (S x) i j k
  rw [show raw (R1 x) = B1 x from hR1 x hx]
  linarith only [hd, ha]

end PoincareConjecture.M34

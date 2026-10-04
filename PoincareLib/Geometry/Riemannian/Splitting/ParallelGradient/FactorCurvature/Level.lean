import PoincareLib.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Charts
import PoincareLib.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Normal
import PoincareLib.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Traces
import PoincareLib.Geometry.Riemannian.Connection.Construction

/-!
# Curvature identities of the actual regular-level metric

The factor metric below is `regularLevelMetric`, and its connection is the
Levi-Civita connection constructed from that metric. Normality follows by
differentiating the level equation. Zero Hessian gives a parallel normal;
Gauss restriction and the metric traces are conclusions.

References: Morgan--Tian, Lemma 2.14, pp. 28--29; Kleiner--Lott (corrected
2013), Proposition 41.13, p. 2678, dimension-reduction step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] {g : RiemannianMetric (n + 1) M}

/-- The actual zero-level factor is totally geodesic. Its retained curvature,
Ricci, scalar curvature, and full curvature norm agree with the ambient
restrictions, and its curvature operator inherits nonnegativity. -/
theorem parallelGradient_factor_curvature
    {D : LeviCivitaData g} {f : M → ℝ}
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) n 0
    let h := regularLevelMetric hf (⊤ : Opens M)
      (fun x _ => regular_of_hasUnitGradient hu x) 0 g
    let Dh := h.leviCivitaData
    ∀ y : zeroLevelSet f,
      let L := mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl f) y
      FactorCurvature.TotallyGeodesicAt g h (zeroLevelIncl f) y ∧
      (∀ u v w z, Dh.curvatureTensor y u v w z =
        D.curvatureTensor (zeroLevelIncl f y) (L u) (L v) (L w) (L z)) ∧
      (∀ u v, Dh.ricci y u v = D.ricci (zeroLevelIncl f y) (L u) (L v)) ∧
      Dh.scalarCurvature y = D.scalarCurvature (zeroLevelIncl f y) ∧
      Dh.curvatureTensorNorm y = D.curvatureTensorNorm (zeroLevelIncl f y) ∧
      (D.NonnegativeCurvatureOperator (zeroLevelIncl f y) →
        Dh.NonnegativeCurvatureOperator y) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens M)) => regular_of_hasUnitGradient hu x
  let := openLevelSetChartedSpace hf (⊤ : Opens M) hreg n 0
  let := isManifold_openLevelSet hf (⊤ : Opens M) hreg n 0
  let h := regularLevelMetric hf (⊤ : Opens M) hreg 0 g
  let Dh := h.leviCivitaData
  have hi := contMDiff_openLevelIncl hf (⊤ : Opens M) hreg n 0
  have hm := regularLevelMetric_inner hf (⊤ : Opens M) hreg 0 g
  have horth (y : zeroLevelSet f) (u : TangentSpace (𝓡 n) y) :
      g.inner (zeroLevelIncl f y) (D.gradient f (zeroLevelIncl f y))
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl f) y u) = 0 := by
    rw [D.inner_gradient]
    have hlevel : (fun z : zeroLevelSet f => f (zeroLevelIncl f z)) = fun _ => 0 :=
      funext fun z => z.2
    have he := mfderiv_comp y (hf.mdifferentiable (by simp) _)
      (hi.mdifferentiable (by simp) _)
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun z : zeroLevelSet f => f (zeroLevelIncl f z)) y =
      (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f (zeroLevelIncl f y)).comp
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl f) y) at he
    rw [hlevel, mfderiv_const] at he
    exact (congrArg (fun A => A u) he).symm
  dsimp only
  intro y
  obtain ⟨hgeo, hR⟩ := FactorCurvature.totallyGeodesic_and_curvatureTensor_of_orthogonal_parallel_gradient
    D Dh hi hm hf hu hz horth y
  obtain ⟨hRic, hscalar, hnorm⟩ := FactorCurvature.trace_identities D Dh
    (zeroLevelIncl f y) y (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl f) y).toLinearMap
    (fun u v => (hm y u v).symm) (D.gradient f (zeroLevelIncl f y))
    (hu _) (horth y) hR (curvatureTensor_gradient_slots_eq_zero hf hz _)
  exact ⟨hgeo, hR, hRic, hscalar, hnorm,
    FactorCurvature.nonnegativeCurvatureOperator_of_restriction D Dh _ _
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (zeroLevelIncl f) y).toLinearMap hR⟩

end PoincareMT.RiemannianMetric

import PoincareLib.Geometry.Riemannian.Homothety.Calculus
import PoincareLib.Geometry.RicciFlow.Pinching.Definitions
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Negative curvature under an actual unit metric homothety

The differential bijects orthonormal tangent pairs and preserves their
curvature values. Equality of these sets preserves their infima, hence
the negative part. No attainment or curvature-operator bound is needed.
Source: Morgan--Tian curvature conventions, pp. 5-7; the Chapter 4
Hamilton--Ivey quantity is the existing least-sectional-value definition.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u v

namespace PoincareMT.EpochExtension.SliceGeometry

variable {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 N}
  {f : Diffeomorph (𝓡 3) (𝓡 3) M N ∞}

theorem leastSectionalCurvature_eq_one (H : MetricHomothetyCalculus g h f 1)
    (hm : MetricHomothety g h f 1) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) : D'.leastSectionalCurvature (f x) = D.leastSectionalCurvature x := by
  let e := f.mfderivToContinuousLinearEquiv (by simp) x
  have he_apply (u : TangentSpace (𝓡 3) x) : e u = mfderiv (𝓡 3) (𝓡 3) f x u :=
    congrArg (fun A => A u) (Diffeomorph.mfderivToContinuousLinearEquiv_coe f (by simp))
  have he (u v : TangentSpace (𝓡 3) x) : h.inner (f x) (e u) (e v) = g.inner x u v := by
    simpa only [he_apply, one_mul] using hm x u v
  have horth (u v : TangentSpace (𝓡 3) x) :
      LeviCivitaData.IsOrthonormalPair h (f x) (e u) (e v) ↔
        LeviCivitaData.IsOrthonormalPair g x u v := by
    simp only [LeviCivitaData.IsOrthonormalPair, he]
  have hcurv (u v : TangentSpace (𝓡 3) x) :
      D'.curvatureTensor (f x) (e u) (e v) (e u) (e v) = D.curvatureTensor x u v u v := by
    simpa only [he_apply, one_mul] using
      H.riemann_eq D D' x u v u v
  unfold LeviCivitaData.leastSectionalCurvature
  congr 1
  ext k
  constructor
  · rintro ⟨u, v, huv, hk⟩
    refine ⟨e.symm u, e.symm v, ?_, ?_⟩
    · exact (horth _ _).mp (by simpa only [e.apply_symm_apply] using huv)
    · exact hk.trans (by simpa only [e.apply_symm_apply] using hcurv (e.symm u) (e.symm v))
  · rintro ⟨u, v, huv, hk⟩
    exact ⟨e u, e v, (horth u v).mpr huv, hk.trans (hcurv u v).symm⟩

theorem negativeCurvaturePart_eq_one (H : MetricHomothetyCalculus g h f 1)
    (hm : MetricHomothety g h f 1) (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (x : M) : D'.negativeCurvaturePart (f x) = D.negativeCurvaturePart x := by
  simp only [LeviCivitaData.negativeCurvaturePart, leastSectionalCurvature_eq_one H hm D D' x]

end PoincareMT.EpochExtension.SliceGeometry

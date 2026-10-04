import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Annular.Area
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Annular.Convergence

/-!
# Annular replacement of the original minimizing spheres

Morgan-Tian Lemma 18.10, printed pp. 424-426. The competitor retains
the homotopy class of each original sphere. Its area removes the actual
rescaled inner disk and adds the limiting complementary cap, with an
arbitrarily small annular error.

The statement below pins the exact assembly boundary. Its geometric
producer is proved in `MinimizerAnnularReplacement.lean` from the actual
cap, interpolation, convergence and relative-homotopy constructions.
-/

set_option autoImplicit false

open Set Filter Metric MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareMT.M60

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The literal annular-replacement output needed to exclude a null
bubble. All maps and integrals are the actual original sequence and
actual limiting sphere. Source: MT Lemma 18.10, annular replacement. -/
def M60SphereAnnularReplacement (g : RiemannianMetric n M) : Prop :=
  ∀ (s : ℕ → UnitTwoSphere → M)
    (hs : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (s j))
    (c : ℕ → UnitTwoSphere) (scale : ℕ → ℝ),
    (∀ j, 0 < scale j) →
    ∀ (v : UnitTwoSphere → M), ContMDiff (𝓡 2) (𝓡 n) 1 v →
    IsNullHomotopicSphere v →
    ∀ (d : ℕ) (e : M → EuclideanSpace ℝ (Fin d)),
    ContMDiff (𝓡 n) (𝓡 d) ∞ e → IsClosedEmbedding e → SUChartReadable (n := n) e →
    TendstoLocallyUniformly
      (fun j z => e (s j ((chartAt LoopPlane (c j)).symm (scale j • z))))
      (e ∘ v ∘ m60SphereParameter) atTop →
    TendstoLocallyUniformly
      (fun j => fderiv ℝ
        (fun z => e (s j ((chartAt LoopPlane (c j)).symm (scale j • z)))))
      (fderiv ℝ (e ∘ v ∘ m60SphereParameter)) atTop →
    ∀ R : ℝ, 0 < R → ∀ eta : ℝ, 0 < eta →
      ∀ᶠ j in atTop, ∃ h : UnitTwoSphere → M,
        ∃ hh : ContMDiff (𝓡 2) (𝓡 n) 1 h,
          (⟨h, hh.continuous⟩ : C(UnitTwoSphere, M)).Homotopic
            ⟨s j, (hs j).continuous⟩ ∧
          m60SphereArea g h ≤ m60SphereArea g (s j) -
            (∫ z in ball (0 : LoopPlane) R, m60AreaDensity g
              (fun z => s j ((chartAt LoopPlane (c j)).symm (scale j • z))) z) +
            (∫ z in (closedBall (0 : LoopPlane) R)ᶜ,
              m60SphereAreaDensity g v z) + eta

end PoincareMT.M60

import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularArea
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularConvergence














set_option autoImplicit false

open Set Filter Metric MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




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

end PoincareConjecture.M60

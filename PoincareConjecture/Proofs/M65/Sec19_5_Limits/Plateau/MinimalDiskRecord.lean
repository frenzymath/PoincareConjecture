import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.PlaneFirstVariation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BoundaryAngularTrace

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

structure M65MinimalDisk (g : RiemannianMetric 3 M) (connection : LeviCivitaData g)
    (γ : C1FreeLoopSpace (M := M)) where
  disk : LipschitzSpanningDisk g γ
  area_eq : disk.area = fillingArea g γ
  interior_smooth : ContMDiffOn (𝓡 2) (𝓡 3) ∞ disk.map (Metric.ball (0 : LoopPlane) 1)
  weakly_conformal : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, ∃ c : ℝ,
    m60AreaGram g disk.map z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)
  harmonic : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
    m65PlaneTension connection disk.map z = 0
  boundary_regular : ContMDiffOn (𝓡 2) (𝓡 3) 1 disk.map loopDiskSet
  finite_branches : {z : LoopPlane | z ∈ loopDiskSet ∧
    mfderivWithin (𝓡 2) (𝓡 3) disk.map loopDiskSet z = 0}.Finite

end PoincareConjecture

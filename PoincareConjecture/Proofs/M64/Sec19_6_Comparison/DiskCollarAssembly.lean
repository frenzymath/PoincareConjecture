import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.CollarGluing








set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}





structure M64DiskCollarCertificate
    {gamma0 gamma1 : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g gamma0) (q eta : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  map : LoopPlane → M
  reparameterization : CircleReparameterization
  matching : ∀ z : LoopPlane, ‖z‖ = radius →
    D.map (radius⁻¹ • z) = map z
  boundary : ∀ z : LoopCircle,
    map z = gamma1 (reparameterization.map z)
  lipschitz_constant : ℝ
  lipschitz_nonnegative : 0 ≤ lipschitz_constant
  lipschitz_on_annulus : ∀ x ∈ loopDiskSet ∩ {z | radius ≤ ‖z‖},
    ∀ y ∈ loopDiskSet ∩ {z | radius ≤ ‖z‖},
      g.edist (map x) (map y) ≤
        ENNReal.ofReal lipschitz_constant * ENNReal.ofReal ‖x - y‖
  area_integrable : IntegrableOn (m60AreaDensity g map)
    ((closedBall (0 : LoopPlane) radius)ᶜ ∩ loopDiskSet) volume
  area_bound : (∫ z in (closedBall (0 : LoopPlane) radius)ᶜ ∩ loopDiskSet,
      m60AreaDensity g map z) ≤ q + eta




theorem m64DiskWitness_of_collar
    {gamma0 gamma1 : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g gamma0) (q eta : ℝ)
    (C : M64DiskCollarCertificate (gamma1 := gamma1) D q eta) :
    ∃ D' : LipschitzSpanningDisk g gamma1,
      D'.area ≤ D.area + q + eta := by
  obtain ⟨D', _, harea⟩ := m60DiskGluing_of_collar g D
    C.radius_pos C.radius_lt_one C.map C.reparameterization
    C.matching C.boundary C.lipschitz_nonnegative C.lipschitz_on_annulus
    C.area_integrable
  refine ⟨D', ?_⟩
  linarith [harea, C.area_bound]

end PoincareConjecture

import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Projective.ProjectiveCover
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Schoenflies.SchoenfliesRadial
import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Closed.ClosedModelCapCoordinates

/-!
# The selected negative projective compact side

This record retains only projections of the actual TPC3 negative witness.
The projected manifold ball and full cover are subsequent conclusions.
Morgan--Tian A.21, pp. 510-514; the negative-assembly and exact-header
derivations in `tasks/M25/smale/derivations/` dated 2026-09-23.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M25.Topology3D

/-- Literal selected TPC3 data for the negative compact side.
MT A.21, pp. 510-514; negative-assembly derivation, sections 1-3. -/
structure NegativeProjectiveSideData
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C1 C2 : ClosedModelCapData g)
    (P2 : PoincareMT.StandardPuncturedProjectiveCover
      M C2.puncture C2.carrier) where
  v : ℝ
  v_mem : v ∈ Ioo (-C1.epsilon⁻¹) C1.epsilon⁻¹
  cuts :
    let L := C1.epsilon⁻¹
    let N := C1
    let Y := C1.carrier ∪ C2.carrier
    let K := fun s => C1.carrier \ N.region s L
    let V := fun s => interior (K s)
    let W := fun s => Y \ K s
    let Q := fun s => Y \ V s
    ∀ a b : ℝ, v < a → a < b → b < L →
      IsOpen (W a) ∧ Q a ⊆ C2.carrier ∧
      V b ∪ W a = Y ∧ V b ∩ W a = N.region a b ∧
      N.region a b = N.coordinate_map '' (univ ×ˢ Ioo a b)
  F : RoundCylinderSpace → UnitThreeSphere
  lift_eq :
    let c := (v + C1.epsilon⁻¹) / 2
    let h := (C1.epsilon⁻¹ - v) / 4
    EqOn (P2.cover ∘ F)
      (fun z => C1.coordinate_map (z.1, c + h * z.2))
      (univ ×ˢ Ioo (-1 : ℝ) 1)
  psi : RoundCylinderSpace → E3
  collar : IsCollarEmbedding psi
  S : SchoenfliesData psi (1 / 4)
  side_eq : S.side = -1
  e : OpenPartialHomeomorph E3 UnitThreeSphere
  source_eq : e.source = ball 0 (S.radial (7 / 8))
  smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source
  inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target
  disjoint : Disjoint e.target ((fun x : UnitThreeSphere => -x) '' e.target)
  ray : ∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (1 / 4) (7 / 8) →
    e (S.radial t • (S.boundary_map q).val) = F (q, S.side * t)
  ball_interior : ∀ t ∈ Icc (1 / 4 : ℝ) (7 / 8),
    interior (e '' closedBall 0 (S.radial t)) = e '' ball 0 (S.radial t)
  negative :
    let L := C1.epsilon⁻¹
    let N := C1
    let Y := C1.carrier ∪ C2.carrier
    let K := fun s => C1.carrier \ N.region s L
    let V := fun s => interior (K s)
    let W := fun s => Y \ K s
    let Q := fun s => Y \ V s
    let c := (v + L) / 2
    let h := (L - v) / 4
    let s := fun t => c + h * (S.side * t)
    let D := fun t => e '' closedBall 0 (S.radial t)
    ∀ t ∈ Icc (1 / 2 : ℝ) (13 / 16),
      projectiveCoverDomain C2.puncture ∩ P2.cover ⁻¹' Q (s t) =
        D t ∪ (fun x : UnitThreeSphere => -x) '' D t ∧
      projectiveCoverDomain C2.puncture ∩ P2.cover ⁻¹' W (s t) =
        interior (D t) ∪ (fun x : UnitThreeSphere => -x) '' interior (D t)

end PoincareMT.M25.Topology3D

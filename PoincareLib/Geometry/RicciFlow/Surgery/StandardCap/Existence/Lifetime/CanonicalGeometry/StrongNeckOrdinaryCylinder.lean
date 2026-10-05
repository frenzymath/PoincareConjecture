import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Basic.OrdinaryCylinder
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Metric.OrdinaryCylinderPullback
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.StrongNeckSpatialMap

/-!
# The actual ordinary cylinder on a transported neck carrier

An included anchor point and the actual image carrier determine an
ordinary cylinder with the same normalized scale. Its zero identity
retains the literal original anchored spatial projection. Source:
Morgan-Tian Theorem 12.28, pp. 323-324; the transported-cylinder step in
the owned strong-neck derivation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

variable {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
  {K : Set ℝ} {U : Set C.carrier}

/-- The ordinary cylinder at the included anchor, on the actual image
of the requested spatial carrier, with the original normalization scale. -/
noncomputable def ordinaryChapter11PushedCylinder
    (e : GeneralizedFlowCylinder (G) C origin scale K U)
    (base : C.carrier) (hzero : 0 ∈ K) (V : Set C.carrier)
    (K' : Set ℝ) (hK' : K' ⊆ K) :
    GeneralizedFlowCylinder (G) ((G).slice (origin + 0 / scale))
      (origin + 0 / scale) scale K' (e.forward 0 hzero '' V) :=
  ordinaryChapter11Cylinder R (e.pointMap 0 hzero base) scale e.scale_pos K'
    (e.forward 0 hzero '' V) (by
      intro s hs
      change (origin + 0 / scale) + s / scale ∈ I.domain
      have h := ordinaryChapter11Point_time_mem R (e.pointMap s (hK' hs) base)
      change origin + s / scale ∈ I.domain at h
      simpa only [zero_div, add_zero] using h)

/-- The transported ordinary cylinder is the literal identity on its
included zero slice, even outside its tested spatial carrier. -/
theorem ordinaryChapter11PushedCylinder_zero_identity
    (e : GeneralizedFlowCylinder (G) C origin scale K U)
    (base : C.carrier) (hzero : 0 ∈ K) (V : Set C.carrier)
    (K' : Set ℝ) (hK' : K' ⊆ K) (hzero' : 0 ∈ K')
    (x : ((G).slice (origin + 0 / scale)).carrier) :
    (ordinaryChapter11PushedCylinder R e base hzero V K' hK').pointMap 0 hzero' x =
      (⟨origin + 0 / scale, x⟩ : (G).point) := by
  unfold ordinaryChapter11PushedCylinder
  exact ordinaryChapter11Cylinder_zero_identity R (e.pointMap 0 hzero base)
    scale e.scale_pos K' (e.forward 0 hzero '' V) _ hzero' x

/-- Its anchored ordinary projection, composed with the actual anchor
forward map, is exactly the original cylinder's anchored projection. -/
theorem ordinaryChapter11PushedCylinder_spatialMap_comp
    (e : GeneralizedFlowCylinder (G) C origin scale K U)
    (base : C.carrier) (hzero : 0 ∈ K) (V : Set C.carrier)
    (K' : Set ℝ) (hK' : K' ⊆ K) (hzero' : 0 ∈ K') :
    ordinaryChapter11CylinderSpatialMap R
      (ordinaryChapter11PushedCylinder R e base hzero V K' hK') 0 hzero' ∘
        e.forward 0 hzero = ordinaryChapter11CylinderSpatialMap R e 0 hzero := by
  funext x
  simp only [ordinaryChapter11CylinderSpatialMap, Function.comp_apply]
  rw [ordinaryChapter11PushedCylinder_zero_identity]
  rfl

end PoincareMT.M34

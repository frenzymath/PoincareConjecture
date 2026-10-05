import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Coordinates.IncludedMetricCoordinates
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Metric.OrdinaryCylinderPullback

/-!
# Included-time regularity of actual ordinary cylinder coefficients

The zero extension in the frozen coefficient is removed only within
the included time slab. The retained spatial map identifies its value
and derivative with a fixed pullback of the original metric family.
Source: Morgan-Tian Theorems 11.8 and 12.28, pp. 276-277, 323-324;
M34 canonical-neighborhood persistence derivation, section 3.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

variable {J : Set ℝ} {L : BlowupLimitFlow.{u} J}
  {origin scale : ℝ} {K : Set ℝ} {U : Set L.sliceCarrier.carrier}

/-- Frozen pullback coefficients are jointly smooth within the actual
time slab and the captured part of a spatial chart (Theorem 12.28). -/
theorem ordinaryChapter11Cylinder_coefficient_contDiffOn
    (e : GeneralizedFlowCylinder (G) L.sliceCarrier origin scale K U)
    (hU : IsOpen U) (hK : IsPreconnected K) {s0 : ℝ} (hs0 : s0 ∈ K)
    (q : L.sliceCarrier.carrier) (a b : Fin 3) :
    ContDiffOn ℝ ∞ (blowupPullbackCoefficient e q a b)
      (K ×ˢ ((extChartAt (𝓡 3) q).target ∩ (extChartAt (𝓡 3) q).symm ⁻¹' U)) := by
  let c := extChartAt (𝓡 3) q
  let W := c.target ∩ c.symm ⁻¹' U
  let f := ordinaryChapter11CylinderSpatialMap R e s0 hs0
  let φ : EuclideanSpace ℝ (Fin 3) → M := f ∘ c.symm
  have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) hU
  have hf {x : L.sliceCarrier.carrier} (hx : x ∈ U) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x :=
    (ordinaryChapter11CylinderSpatialMap_contMDiffOn R e hs0 x hx).contMDiffAt
      (hU.mem_nhds hx)
  have hc {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ W :=
    fun y hy => ((hf hy.2).comp y (hc hy.1)).contMDiffWithinAt
  have hclock : MapsTo (fun s : ℝ => origin + s / scale) K I.domain :=
    fun s hs => ordinaryChapter11Point_time_mem (I := I) (F := F) R (e.pointMap s hs q)
  have hτ : ContDiff ℝ ∞ (fun s : ℝ => origin + s / scale) :=
    contDiff_const.add (contDiff_id.div_const scale)
  have hcoeff := (contDiffOn_const (c := scale)).mul
    (F.contDiffOn_clock_spatialPullback_inner hW hφ hτ hclock
    (EuclideanSpace.basisFun (Fin 3) ℝ a)
    (EuclideanSpace.basisFun (Fin 3) ℝ b))
  apply hcoeff.congr
  intro p hp
  simp only [blowupPullbackCoefficient, dif_pos hp.1]
  rw [ordinaryChapter11Cylinder_pullbackInner_eq R e hU hK hs0 hp.1 hp.2.2]
  have hd := mfderiv_comp p.2 ((hf hp.2.2).mdifferentiableAt (by simp))
    ((hc hp.2.1).mdifferentiableAt (by simp))
  change _ = scale * (F.metric (origin + p.1 / scale)).inner (φ p.2)
      (mfderiv (𝓡 3) (𝓡 3) φ p.2 (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (mfderiv (𝓡 3) (𝓡 3) φ p.2 (EuclideanSpace.basisFun (Fin 3) ℝ b))
  rw [hd]
  rfl

end PoincareMT.M34

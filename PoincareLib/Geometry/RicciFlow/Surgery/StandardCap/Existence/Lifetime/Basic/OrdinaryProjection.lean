import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Basic.OrdinaryRealization
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Spatial projection of every ordinary compatible cylinder

The single retained flow box makes the ordinary spatial coordinate
locally constant along every compatible cylinder. On a preconnected
source interval it is constant, including the actual terminal anchor.
Source: Morgan-Tian Theorems 12.28-12.29, pp. 323-325; the ordinary
Chapter 11 derivation in the M34 task records, section 5.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

/-- The spatial coordinate of the actual ordinary Chapter 11 spacetime
(Theorems 12.28-12.29, pp. 323-325). -/
def ordinaryChapter11Projection (z : (ordinaryChapter11Flow R).point) : M := z.2.val.2

/-- The retained slice identification has its original spatial coordinate
(Theorems 12.28-12.29, pp. 323-325). -/
theorem ordinaryChapter11Projection_identification (t : I.domain) (x : M) :
    ordinaryChapter11Projection R ⟨t.val, R.product.sliceIdentification t x⟩ = x :=
  congrArg Prod.snd (R.product.sliceIdentification_eq t x)

set_option backward.isDefEq.respectTransparency false in
/-- The actual compatibility field of an arbitrary cylinder makes its
ordinary spatial coordinate locally constant (Theorem 12.28). -/
theorem ordinaryChapter11Projection_locallyConstant
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
    {K : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (ordinaryChapter11Flow R) C origin scale K U)
    {x : C.carrier} (hx : x ∈ U) :
    IsLocallyConstant (fun s : K =>
      ordinaryChapter11Projection R (e.pointMap s.val s.property x)) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro s
  obtain ⟨b, y, delta, hdelta, hlocal⟩ := e.vertical_compatibility s.val s.property x hx
  have hv (s' : K) (hs' : |s'.val - s.val| < delta) :
      ordinaryChapter11Projection R (e.pointMap s'.val s'.property x) = y := by
    obtain ⟨hb, he⟩ := hlocal s'.val s'.property hs'
    change (e.forward s'.val s'.property x).val.2 = y
    rw [he]
    exact congrArg Prod.snd
      (R.product.sliceIdentification_eq ⟨origin + s'.val / scale, hb⟩ y)
  refine ⟨{s' : K | |s'.val - s.val| < delta},
    isOpen_lt (continuous_subtype_val.sub continuous_const).abs continuous_const,
    ?_, ?_⟩
  · simpa only [mem_ofPred_eq, sub_self, abs_zero] using hdelta
  · intro s' hs'
    exact (hv s' hs').trans (hv s (by simpa only [sub_self, abs_zero] using hdelta)).symm

/-- On a preconnected source interval every compatible cylinder has a
constant ordinary spatial coordinate (Theorem 12.28). -/
theorem ordinaryChapter11Projection_cylinder_eq
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
    {K : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (ordinaryChapter11Flow R) C origin scale K U)
    (hK : IsPreconnected K) {x : C.carrier} (hx : x ∈ U)
    {s s' : ℝ} (hs : s ∈ K) (hs' : s' ∈ K) :
    ordinaryChapter11Projection R (e.pointMap s hs x) =
      ordinaryChapter11Projection R (e.pointMap s' hs' x) := by
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  exact (ordinaryChapter11Projection_locallyConstant R e hx).apply_eq_of_preconnectedSpace
    ⟨s, hs⟩ ⟨s', hs'⟩

/-- A based compatible cylinder keeps the spatial coordinate of its
actual terminal point throughout its preconnected interval (Theorem 12.28). -/
theorem ordinaryChapter11Projection_cylinder_based
    (p : (ordinaryChapter11Flow R).point) {scale : ℝ} {K : Set ℝ}
    {U : Set ((ordinaryChapter11Flow R).slice p.1).carrier}
    (e : GeneralizedFlowCylinder (ordinaryChapter11Flow R)
      ((ordinaryChapter11Flow R).slice p.1) p.1 scale K U)
    (hK : IsPreconnected K) (hzero : 0 ∈ K)
    (hbase : ∀ x ∈ U, e.pointMap 0 hzero x = ⟨p.1, x⟩)
    {x : ((ordinaryChapter11Flow R).slice p.1).carrier} (hx : x ∈ U)
    {s : ℝ} (hs : s ∈ K) :
    ordinaryChapter11Projection R (e.pointMap s hs x) = x.val.2 := by
  rw [ordinaryChapter11Projection_cylinder_eq R e hK hx hs hzero, hbase x hx]
  rfl

end PoincareMT.M34

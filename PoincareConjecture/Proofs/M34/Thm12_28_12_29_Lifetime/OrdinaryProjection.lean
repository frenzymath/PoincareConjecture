import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryRealization
import Mathlib.Topology.LocallyConstant.Basic











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)



def ordinaryChapter11Projection (z : (ordinaryChapter11Flow R).point) : M := z.2.val.2



theorem ordinaryChapter11Projection_identification (t : I.domain) (x : M) :
    ordinaryChapter11Projection R ⟨t.val, R.product.sliceIdentification t x⟩ = x :=
  congrArg Prod.snd (R.product.sliceIdentification_eq t x)

set_option backward.isDefEq.respectTransparency false in


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

end PoincareConjecture.M34

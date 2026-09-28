import PoincareConjecture.Proofs.M12.GeneralizedCylinderMetric
import PoincareConjecture.Proofs.M13.GeneralizedSlices
import PoincareConjecture.Proofs.M11.OpenSubsetDiffeomorph
import PoincareConjecture.Proofs.M04.ShiCarrier
import PoincareConjecture.Definitions.M15Noncollapsing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M15

noncomputable def rawBallSource (F : GeneralizedRicciFlowData.{u})
    (T : ℝ) (x : (F.slice T).carrier) (r : ℝ) :
    TopologicalSpace.Opens (F.slice T).carrier :=
  ⟨(F.metric T).ball x r, M04.initial_ball_isOpen (F.metric T) x r⟩

def backwardBallInterval (r : ℝ) (hr : 0 < r) : SpacetimeInterval where
  domain := Icc (-r ^ 2) 0
  ordConnected := ordConnected_Icc
  nontrivial := ⟨-r ^ 2, ⟨le_rfl, neg_nonpos.mpr (sq_nonneg r)⟩,
    0, ⟨neg_nonpos.mpr (sq_nonneg r), le_rfl⟩,
    ne_of_lt (neg_lt_zero.mpr (sq_pos_of_pos hr))⟩

theorem backwardBallInterval_physical (T r : ℝ) (hr : 0 < r) :
    (M12.cylinderPhysicalInterval T 1 zero_lt_one (backwardBallInterval r hr)).domain =
      Icc (T - r ^ 2) T := by
  ext t
  change (∃ s ∈ Icc (-r ^ 2) 0, parabolicTimeInv 1 T s = t) ↔ _
  simp only [parabolicTimeInv, div_one, mem_Icc]
  constructor
  · rintro ⟨s, ⟨hs, hs'⟩, rfl⟩
    constructor <;> linarith
  · rintro ⟨ht, ht'⟩
    exact ⟨t - T, ⟨by linarith, by linarith⟩, by ring⟩

variable {F : GeneralizedRicciFlowData.{u}} (G : M12.FlowBoxRicciGeometry F)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} 3)
  {T r : ℝ} (x : (F.slice T).carrier) (hr : 0 < r)
  (e : GeneralizedFlowCylinder F (F.slice T) T 1 (Icc (-r ^ 2) 0)
    ((F.metric T).ball x r))
  (hI : Icc (T - r ^ 2) T ⊆ F.interval)
  (hbase : ∀ h y, y ∈ (F.metric T).ball x r →
    e.pointMap 0 h y = (⟨T, y⟩ : F.point))
  (hcurv : ∀ s hs y, y ∈ (F.metric T).ball x r →
    F.curvatureNorm (e.pointMap s hs y) ≤ r⁻¹ ^ 2)

noncomputable def rawActualBallCylinder :
    M15ActualBallCylinder G.toLGeometry T ((G.sliceIdentification T).identification x) r
      (M12.cylinderPhysicalInterval T 1 e.scale_pos (backwardBallInterval r hr))
      (rawBallSource F T x r) := by
  let J := backwardBallInterval r hr
  let K := M12.cylinderPhysicalInterval T 1 e.scale_pos J
  let U := rawBallSource F T x r
  have hK : K.domain = Icc (T - r ^ 2) T := backwardBallInterval_physical T r hr
  have htime : K.domain ⊆ F.interval := hK ▸ hI
  have hzero : (0 : ℝ) ∈ J.domain := ⟨neg_nonpos.mpr (sq_nonneg r), le_rfl⟩
  have hterminal : T ∈ K.domain := hK ▸ ⟨by nlinarith [sq_nonneg r], le_rfl⟩
  let E := M12.rawCylinderTransport G.realization (U := U) (J := J) e htime
  let f : U → (G.realization.slices T).Point :=
    (G.sliceIdentification T).identification ∘ Subtype.val
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    (G.sliceIdentification T).identification.contMDiff.comp contMDiff_subtype_val
  refine {
    radius_pos := hr
    interval_domain := hK
    base_mem := hterminal
    embedding := E
    metric := M12.rawCylinderMetric G.realization (U := U) (J := J) e htime
    source_map := f
    source_map_embedding :=
      (G.sliceIdentification T).identification.toHomeomorph.isEmbedding.comp .subtypeVal
    source_map_range := ?_
    based := ?_
    source_map_smooth := hf.contMDiffOn
    source_map_differential_injective := ?_
    curvature_bound := ?_
  }
  · have he : range f = (G.sliceIdentification T).identification '' (F.metric T).ball x r := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z.val, z.property, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, rfl⟩
    exact he.trans (M13.originalSlice_ball G hM13 T x r)
  · intro c
    have he := M12.rawCylinderMap_at_parameter G.realization (U := U) (J := J)
      e ⟨0, hzero⟩ c
    have hc : E.toSpacetime (⟨T, hterminal⟩, c) = e.pointMap 0 hzero c.val := by
      simpa [E, M12.rawCylinderTransport, M12.cylinderClockHomeomorph,
        parabolicTimeInv] using he
    exact (hc.trans (hbase hzero c.val c.property)).trans
      ((G.sliceIdentification T).identification_eq c.val).symm
  · intro c
    have hd := mfderiv_comp c
      ((G.sliceIdentification T).identification.contMDiff _ |>.mdifferentiableAt (by simp))
      (contMDiff_subtype_val (n := ∞) c |>.mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) f c = _ at hd
    rw [hd]
    exact ((G.sliceIdentification T).identification.mfderivToContinuousLinearEquiv
      (by simp) c.val).injective.comp (M11.openSubset_differential_injective U c)
  · intro t c
    let s := M12.cylinderClockHomeomorph T 1 e.scale_pos J t
    have he : E.toSpacetime (t, c) = e.pointMap s.val s.property c.val := rfl
    rw [he]
    exact (M13.originalSlice_curvatureNorm G hM13 (T + s.val / 1)
      (e.forward s.val s.property c.val)).le.trans (hcurv s.val s.property c.val c.property)

end PoincareConjecture.Proofs.M15

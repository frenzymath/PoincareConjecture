import PoincareConjecture.Proofs.M12.GeneralizedCylinderTransport
import PoincareConjecture.Proofs.M12.GeneralizedRicci

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M12

variable {F : GeneralizedRicciFlowData.{u}}
  (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))

def originalSliceMap (t : ℝ) : (F.slice t).carrier → R.spacetime.Point :=
  fun x => ⟨t, x⟩

theorem originalSliceMap_smooth (t : ℝ)
    (S : SpacetimeSliceIdentification R.spacetime t (R.slices t) (flowSliceLabel F t)) :
    ContMDiff (𝓡 3) (spacetimeModel 3) ∞ (originalSliceMap R t) := by
  let := (R.slices t).chartedSpace
  let := (R.slices t).isManifold
  have h := (R.slices t).inclusion_smooth.comp S.identification.contMDiff
  exact h.congr (fun x => (S.identification_eq x).symm)

noncomputable def realizedHorizontalForm (p : R.spacetime.Point)
    (v w : SpacetimeModelVector 3) : ℝ :=
  R.spacetime.horizontalMetric.inner p (R.spacetime.horizontalProjection p v)
    (R.spacetime.horizontalProjection p w)

theorem originalSliceMap_metric (t : ℝ)
    (S : SpacetimeSliceIdentification R.spacetime t (R.slices t) (flowSliceLabel F t))
    (x : (F.slice t).carrier) (v w : TangentSpace (𝓡 3) x) :
    realizedHorizontalForm R (originalSliceMap R t x)
      (mfderiv (𝓡 3) (spacetimeModel 3) (originalSliceMap R t) x v)
      (mfderiv (𝓡 3) (spacetimeModel 3) (originalSliceMap R t) x w) =
      (F.metric t).inner x v w := by
  have hv := S.tangent_eq x v
  have hw := S.tangent_eq x w
  change ((R.slices t).tangentEquiv (S.identification x)
      (mfderiv (𝓡 3) (𝓡 3) S.identification x v)).val =
    mfderiv (𝓡 3) (spacetimeModel 3) (originalSliceMap R t) x v at hv
  change ((R.slices t).tangentEquiv (S.identification x)
      (mfderiv (𝓡 3) (𝓡 3) S.identification x w)).val =
    mfderiv (𝓡 3) (spacetimeModel 3) (originalSliceMap R t) x w at hw
  calc
    _ = realizedHorizontalForm R (S.identification x).val
        ((R.slices t).tangentEquiv (S.identification x)
          (mfderiv (𝓡 3) (𝓡 3) S.identification x v)).val
        ((R.slices t).tangentEquiv (S.identification x)
          (mfderiv (𝓡 3) (𝓡 3) S.identification x w)).val := by
      rw [hv, hw]
      exact congrArg (fun p => realizedHorizontalForm R p
        (mfderiv (𝓡 3) (spacetimeModel 3) (originalSliceMap R t) x v)
        (mfderiv (𝓡 3) (spacetimeModel 3) (originalSliceMap R t) x w))
        (S.identification_eq x).symm
    _ = (R.slices t).metricOnPoints.inner (S.identification x)
        (mfderiv (𝓡 3) (𝓡 3) S.identification x v)
        (mfderiv (𝓡 3) (𝓡 3) S.identification x w) := by
      simp only [realizedHorizontalForm, R.spacetime.horizontalProjection_identity]
      exact ((R.slices t).metric_eq _ _ _).symm
    _ = _ := S.metric_eq x v w

variable {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)
  (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)

noncomputable def rawCylinderMetric : SpacetimeCylinderMetric (rawCylinderTransport R e hI) :=
  Classical.choice (R.compatible.cylinder_metric U _ (rawCylinderTransport R e hI))

theorem rawCylinderMetric_eq
    (M : SpacetimeCylinderMetric (rawCylinderTransport R e hI)) (s : J.domain)
    (S : SpacetimeSliceIdentification R.spacetime (a + s.val / q) (R.slices (a + s.val / q))
      (flowSliceLabel F (a + s.val / q)))
    (x : U) (v w : TangentSpace (𝓡 3) x) :
    (M.metric (a + s.val / q)).inner x v w =
      e.pullbackInner s.val s.property x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) / q := by
  let t : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point :=
    (cylinderClockHomeomorph a q e.scale_pos J).symm s
  let f := rawSpatialMap e s
  have hfun : (fun y : U => (rawCylinderTransport R e hI).toSpacetime (t, y)) =
      originalSliceMap R (a + s.val / q) ∘ f :=
    funext (rawCylinderMap_at_parameter R e s)
  have hd (z : TangentSpace (𝓡 3) x) :
      (M.spatialTangentEquiv t x z).val =
        mfderiv (𝓡 3) (spacetimeModel 3) (originalSliceMap R (a + s.val / q)) (f x)
          (mfderiv (𝓡 3) (𝓡 3) f x z) := by
    rw [M.spatialTangentEquiv_eq]
    have heq := congrArg
      (fun l : U → R.spacetime.Point =>
        (mfderiv (𝓡 3) (spacetimeModel 3) l x z : SpacetimeModelVector 3)) hfun
    exact heq.trans (mfderiv_comp_apply x
      ((originalSliceMap_smooth R _ S (f x)).mdifferentiableAt (by simp))
      ((rawSpatialMap_smooth e s x).mdifferentiableAt (by simp)) z)
  calc
    _ = realizedHorizontalForm R ((rawCylinderTransport R e hI).toSpacetime (t, x))
        (M.spatialTangentEquiv t x v).val (M.spatialTangentEquiv t x w).val := by
      simp only [realizedHorizontalForm, R.spacetime.horizontalProjection_identity]
      exact M.metric_eq t x v w
    _ = realizedHorizontalForm R (originalSliceMap R (a + s.val / q) (f x))
        (mfderiv (𝓡 3) (spacetimeModel 3) (originalSliceMap R (a + s.val / q)) (f x)
          (mfderiv (𝓡 3) (𝓡 3) f x v))
        (mfderiv (𝓡 3) (spacetimeModel 3) (originalSliceMap R (a + s.val / q)) (f x)
          (mfderiv (𝓡 3) (𝓡 3) f x w)) := by
      rw [hd, hd]
      exact congrArg (fun p => realizedHorizontalForm R p _ _) (congrFun hfun x)
    _ = (F.metric (a + s.val / q)).inner (f x)
        (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) :=
      originalSliceMap_metric R _ S (f x) _ _
    _ = _ := by
      have hf := (e.forward_smooth s.val s.property x.val x.property).contMDiffAt
        (U.isOpen.mem_nhds x.property)
      have hder := mfderiv_comp x (hf.mdifferentiableAt (by simp))
        (contMDiff_subtype_val (n := ∞) x |>.mdifferentiableAt (by simp))
      change mfderiv (𝓡 3) (𝓡 3) f x = _ at hder
      rw [hder]
      dsimp only [GeneralizedFlowCylinder.pullbackInner, ContinuousLinearMap.comp_apply]
      field_simp [e.scale_pos.ne']
      rfl

end PoincareConjecture.Proofs.M12

import PoincareConjecture.Proofs.M12.GeneralizedWorldlines
import PoincareConjecture.Proofs.M12.GeneralizedCylinderSpatial
import PoincareConjecture.Proofs.M11.WorldlineRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M12

open PoincareConjecture.Proofs.M11

variable {F : GeneralizedRicciFlowData.{u}}
  (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)

structure RawCylinderLocalFactor
    (p : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point × U) where
  interval : SpacetimeInterval
  subset : interval.domain ⊆ (cylinderPhysicalInterval a q e.scale_pos J).domain
  center_mem : p.1.val ∈ interval.domain
  relatively_open :
    IsOpen {v : (cylinderPhysicalInterval a q e.scale_pos J).domain | v.val ∈ interval.domain}
  box : F.box_index
  box_subset : interval.domain ⊆ (boxInterval F box).domain
  spatial : U → (F.box box).carrier.carrier
  spatial_smooth : ContMDiffAt (𝓡 3) (𝓡 3) ∞ spatial p.2
  spatial_injective : Injective (mfderiv (𝓡 3) (𝓡 3) spatial p.2)
  local_eq :
    (fun z : (R.timeIntervals.interval interval).Point × U =>
      rawCylinderMap R e
        (spacetimeIntervalInclusion (R.timeIntervals.interval interval)
          (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)) subset z.1,
          z.2)) =ᶠ[𝓝 (⟨p.1.val, center_mem⟩, p.2)]
    (fun z => originalBoxMap F R box
      (spacetimeIntervalInclusion (R.timeIntervals.interval interval)
        (R.timeIntervals.interval (boxInterval F box)) box_subset z.1, spatial z.2))

theorem rawCylinderLocalFactor_exists
    (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)
    (p : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point × U) :
    Nonempty (RawCylinderLocalFactor R e p) := by
  let K := cylinderPhysicalInterval a q e.scale_pos J
  let s := cylinderClockHomeomorph a q e.scale_pos J p.1
  let T := a + s.val / q
  have hT : T = p.1.val := parabolicTimeInv_parabolicTime q e.scale_pos a p.1.val
  obtain ⟨b, y, δ, hδ, hv⟩ := e.vertical_compatibility s.val s.property p.2.val p.2.property
  obtain ⟨hb0, hbase⟩ := hv s.val s.property (by simpa using hδ)
  have htbox : p.1.val ∈ (F.box b).interval := hT ▸ hb0
  obtain ⟨O, hO, hOb⟩ := (F.box b).relatively_open
  have hopen : IsOpen {t : K.domain | t.val ∈ (F.box b).interval} := by
    have he : {t : K.domain | t.val ∈ (F.box b).interval} =
        (Subtype.val : K.domain → ℝ) ⁻¹' O := by
      ext t
      simp only [hOb, mem_ofPred_eq, mem_inter_iff, mem_preimage, hI t.property, true_and]
    rw [he]
    exact hO.preimage continuous_subtype_val
  obtain ⟨L, hK, htL, ho, hLb⟩ := interval_exists_open_small_neighborhood K p.1
    (hopen.mem_nhds htbox)
  have hb : L.domain ⊆ (boxInterval F b).domain := fun t ht => hLb ⟨t, ht⟩
  let f := rawSpatialMap e s
  let k : U → (F.box b).carrier.carrier := (F.box b).inverse T hb0 ∘ f
  have hfx : f p.2 ∈ range ((F.box b).forward T hb0) := ⟨y, hbase.symm⟩
  have hrange := ((F.box b).forward_openEmbedding T hb0).isOpen_range
  have hnear : ∀ᶠ z in 𝓝 p.2, f z ∈ range ((F.box b).forward T hb0) :=
    (rawSpatialMap_smooth e s p.2).continuousAt (hrange.mem_nhds hfx)
  have hk : ContMDiffAt (𝓡 3) (𝓡 3) ∞ k p.2 :=
    ((F.box b).inverse_smooth T hb0 |>.contMDiffAt (hrange.mem_nhds hfx)).comp p.2
      (rawSpatialMap_smooth e s p.2)
  have hkleft : (F.box b).forward T hb0 ∘ k =ᶠ[𝓝 p.2] f := by
    filter_upwards [hnear] with z hz
    exact (F.box b).right_inverse T hb0 hz
  have hkdiff := hkleft.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp p.2 ((F.box b).forward_smooth T hb0 (k p.2) |>.mdifferentiableAt
    (by simp)) (hk.mdifferentiableAt (by simp))] at hkdiff
  have hinj : Injective (mfderiv (𝓡 3) (𝓡 3) k p.2) := by
    intro v w hvw
    apply rawSpatialMap_differential_injective e s p.2
    have hv' := congrArg (fun d : TangentSpace (𝓡 3) p.2 →L[ℝ]
      TangentSpace (𝓡 3) (f p.2) => d v) hkdiff
    have hw' := congrArg (fun d : TangentSpace (𝓡 3) p.2 →L[ℝ]
      TangentSpace (𝓡 3) (f p.2) => d w) hkdiff
    exact hv'.symm.trans ((congrArg (mfderiv (𝓡 3) (𝓡 3)
      ((F.box b).forward T hb0) (k p.2)) hvw).trans hw')
  refine ⟨⟨L, hK, htL, ho, b, hb, k, hk, hinj, ?_⟩⟩
  filter_upwards [continuous_snd.continuousAt hnear] with z hz
  let γ := rawCylinderWorldline R e hI z.2
  let η := embeddingWorldline (originalBoxCylinder F R b).toCompatibleSpacetimeEmbedding (k z.2)
  have hTK : T ∈ K.domain := ⟨s.val, s.property, rfl⟩
  have hstart : γ.curve ⟨T, hTK⟩ = η.curve ⟨T, hb0⟩ :=
    (rawCylinderMap_at_parameter R e s z.2).trans
      (congrArg (fun w => (⟨T, w⟩ : F.point)) ((F.box b).right_inverse T hb0 hz).symm)
  exact R.compatible.worldline_unique K (boxInterval F b) γ η T hTK hb0 hstart
    z.1.val (hK z.1.property) (hb z.1.property)

end PoincareConjecture.Proofs.M12

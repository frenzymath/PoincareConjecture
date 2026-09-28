import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.ReferenceCompatibility
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Cylinder

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularTimeReference

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
  {I : Set ℝ} {U : Set C.carrier}

theorem forward_eq_cylinder_of_eq (R : SingularTimeReference F T M)
    (e : GeneralizedFlowCylinder F C origin scale I U) (hI : OrdConnected I)
    (x : C.carrier) (hx : x ∈ U) (y : M)
    {t : ℝ} (ht : t ∈ I) (hrt : origin + t / scale ∈ Ico R.tMinus T)
    (heq : R.forward (origin + t / scale) hrt y = e.forward t ht x)
    {s : ℝ} (hs : s ∈ I) (hrs : origin + s / scale ∈ Ico R.tMinus T) :
    R.forward (origin + s / scale) hrs y = e.forward s hs x := by
  let J : Set ℝ := I ∩ (fun z => origin + z / scale) ⁻¹' Ico R.tMinus T
  have hclock : Monotone (fun z : ℝ => origin + z / scale) := by
    intro z w hzw
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hzw e.scale_pos.le)
  let : T2Space F.point := F.space_t2
  let : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp
    (hI.inter (ordConnected_Ico.preimage_mono hclock)).isPreconnected
  let r : J → F.point := fun z =>
    R.spacetime_forward (⟨origin + (z : ℝ) / scale, z.property.2⟩, y)
  let c : J → F.point := fun z => e.pointMap z z.property.1 x
  have hr : Continuous r := R.spacetime_embedding.continuous.comp
    (((continuous_const.add (continuous_subtype_val.div_const scale)).subtype_mk
      (fun z => z.property.2)).prodMk continuous_const)
  have hc : Continuous c := e.embedding.continuous.comp
    ((continuous_subtype_val.subtype_mk (fun z => z.property.1)).prodMk
      (continuous_const (y := (⟨x, hx⟩ : U))))
  have hclosed : IsClosed {z : J | r z = c z} := isClosed_eq hr hc
  have hopen : IsOpen {z : J | r z = c z} := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨b, w, δ, hδ, hloc⟩ := e.vertical_compatibility z z.property.1 x hx
    obtain ⟨hbz, hbzeq⟩ := hloc z z.property.1 (by simpa using hδ)
    have hbase : R.forward (origin + (z : ℝ) / scale) z.property.2 y =
        (F.box b).forward (origin + (z : ℝ) / scale) hbz w := by
      have hsig := hz
      change R.spacetime_forward (⟨origin + (z : ℝ) / scale, z.property.2⟩, y) = _ at hsig
      rw [R.spacetime_forward_eq] at hsig
      exact (eq_of_heq (Sigma.mk.inj_iff.mp hsig).2).trans hbzeq
    refine ⟨δ, hδ, ?_⟩
    intro v hv
    have hvδ : |(v : ℝ) - (z : ℝ)| < δ := by
      simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using hv
    obtain ⟨hbv, hbveq⟩ := hloc v v.property.1 hvδ
    change R.spacetime_forward (⟨origin + (v : ℝ) / scale, v.property.2⟩, y) = _
    rw [R.spacetime_forward_eq]
    exact congrArg (Sigma.mk (origin + (v : ℝ) / scale))
      ((R.forward_eq_of_eq b w y z.property.2 hbz hbase v.property.2 hbv).trans
        hbveq.symm)
  have hall : {z : J | r z = c z} = univ :=
    (show IsClopen {z : J | r z = c z} from ⟨hclosed, hopen⟩).eq_univ
      ⟨⟨t, ht, hrt⟩, by
        change R.spacetime_forward (⟨origin + t / scale, hrt⟩, y) = _
        rw [R.spacetime_forward_eq]
        exact congrArg (Sigma.mk (origin + t / scale)) heq⟩
  have hsig : r ⟨s, hs, hrs⟩ = c ⟨s, hs, hrs⟩ :=
    Set.eq_univ_iff_forall.mp hall ⟨s, hs, hrs⟩
  change R.spacetime_forward (⟨origin + s / scale, hrs⟩, y) = _ at hsig
  rw [R.spacetime_forward_eq] at hsig
  exact eq_of_heq (Sigma.mk.inj_iff.mp hsig).2

end PoincareConjecture.SingularTimeReference

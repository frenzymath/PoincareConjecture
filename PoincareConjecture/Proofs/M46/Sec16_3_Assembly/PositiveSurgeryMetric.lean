import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveLocalIsometry
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.SurgeryComponentLabels
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RetainedChart









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
  {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}



theorem positive_sectional_on_surgery_cap
    (event : SurgeryEventData g0 K P slice metric T)
    (D : LeviCivitaData (metric T)) (i : Fin event.cap_count)
    (hneck : ∀ x ∈ (event.necks i).neck.carrier,
      ∀ u v : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair event.limit_metric x u v →
          0 < event.limit_connection.sectionalCurvature x u v) :
    ∀ y ∈ (event.caps i).carrier, ∀ u v : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (metric T) y u v →
        0 < D.sectionalCurvature y u v := by
  have hlocal := (event.local_result i).positive_sectional_preserved
    (fun x hx => (sectional_positive_iff_connection event.limit_connection
      (event.necks i).neck.connection x).mp (hneck x hx))
  intro y hy
  rw [← event.local_cap_image i] at hy
  obtain ⟨x, _, rfl⟩ := hy
  exact (sectional_positive_iff_of_local_isometry (event.local_result i).connection D
    isOpen_univ (event.local_embed_smooth i).contMDiffOn
    (fun z _ u v => (event.local_metric i z u v).symm) (mem_univ x)).mp (hlocal x)



theorem retained_interior_of_not_in_caps
    (event : SurgeryEventData g0 K P slice metric T)
    {x : (slice event.tMinus).carrier} (hx : x ∈ event.retained_pre)
    (hcap : ∀ i, event.retention.map x ∉ (event.caps i).carrier) :
    x ∈ interior event.retained_pre := by
  by_contra hnot
  have hb : x ∈ frontier event.retained_pre := by
    rw [frontier, event.retained_pre_compact.isClosed.closure_eq]
    exact ⟨hx, hnot⟩
  rw [event.pre_boundary] at hb
  obtain ⟨i, hi⟩ := mem_iUnion.mp hb
  have hfront : event.retention.map x ∈ frontier (event.caps i).carrier :=
    event.boundary_correspondence i ▸ mem_image_of_mem event.retention.map hi
  exact hcap i ((event.caps i).carrier_compact.isClosed.frontier_subset hfront)



theorem retained_terminal_metric_identification
    (event : SurgeryEventData g0 K P slice metric T) :
    let U := event.limit_identify.inverse ⁻¹' interior event.retained_pre
    let f := event.retention.map ∘ event.limit_identify.inverse
    IsOpen U ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U ∧
      ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 3) y,
        event.limit_metric.inner y u v = (metric T).inner (f y)
          (mfderiv (𝓡 3) (𝓡 3) f y u) (mfderiv (𝓡 3) (𝓡 3) f y v) := by
  dsimp only
  let U := event.limit_identify.inverse ⁻¹' interior event.retained_pre
  have hinv : ContMDiff (𝓡 3) (𝓡 3) ∞ event.limit_identify.inverse :=
    contMDiffOn_univ.mp event.limit_identify.inverse_smooth
  have hU : IsOpen U := isOpen_interior.preimage hinv.continuous
  have hret : ContMDiffOn (𝓡 3) (𝓡 3) ∞ event.retention.map
      (interior event.retained_pre) := event.retention.map_smooth.mono interior_subset
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (event.retention.map ∘ event.limit_identify.inverse) U :=
    hret.comp hinv.contMDiffOn (fun _ hy => hy)
  refine ⟨hU, hf, ?_⟩
  intro y hy u v
  have hiy : event.limit_identify.inverse y ∈ interior event.retained_pre := hy
  have hr : event.limit_identify.inverse y ∈ event.regular_limit :=
    event.retained_pre_subset (interior_subset hiy)
  have hdret := (hret.contMDiffAt (isOpen_interior.mem_nhds hiy)).mdifferentiableAt
    (by simp)
  have hdlim := (event.limit_identify.map_smooth.contMDiffAt
    (event.regular_limit_open.mem_nhds hr)).mdifferentiableAt (by simp)
  have hdinv := (hinv y).mdifferentiableAt (by simp)
  have hright : event.limit_identify.map ∘ event.limit_identify.inverse = id :=
    funext (fun z => event.limit_identify.right_inverse (mem_univ z))
  have hpull :
      event.limit_metric.inner
          ((event.limit_identify.map ∘ event.limit_identify.inverse) y)
          (mfderiv (𝓡 3) (𝓡 3)
            (event.limit_identify.map ∘ event.limit_identify.inverse) y u)
          (mfderiv (𝓡 3) (𝓡 3)
            (event.limit_identify.map ∘ event.limit_identify.inverse) y v) =
        event.limit_metric.inner y u v := by
    rw [hright]
    simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply]
  rw [mfderiv_comp y hdlim hdinv] at hpull
  rw [mfderiv_comp y hdret hdinv]
  change event.limit_metric.inner y u v = (metric T).inner
    (event.retention.map (event.limit_identify.inverse y))
    (mfderiv (𝓡 3) (𝓡 3) event.retention.map (event.limit_identify.inverse y)
      (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.inverse y u))
    (mfderiv (𝓡 3) (𝓡 3) event.retention.map (event.limit_identify.inverse y)
      (mfderiv (𝓡 3) (𝓡 3) event.limit_identify.inverse y v))
  rw [event.retained_metric _ (interior_subset hiy)]
  exact hpull.symm


theorem positive_sectional_on_retained_interior
    (event : SurgeryEventData g0 K P slice metric T)
    (D : LeviCivitaData (metric T))
    {x : (slice event.tMinus).carrier} (hx : x ∈ interior event.retained_pre)
    (hpos : ∀ u v : TangentSpace (𝓡 3) (event.limit_identify.map x),
      LeviCivitaData.IsOrthonormalPair event.limit_metric (event.limit_identify.map x) u v →
        0 < event.limit_connection.sectionalCurvature (event.limit_identify.map x) u v) :
    ∀ u v : TangentSpace (𝓡 3) (event.retention.map x),
      LeviCivitaData.IsOrthonormalPair (metric T) (event.retention.map x) u v →
        0 < D.sectionalCurvature (event.retention.map x) u v := by
  obtain ⟨hU, hf, hm⟩ := retained_terminal_metric_identification event
  have hreg := event.retained_pre_subset (interior_subset hx)
  have hleft := event.limit_identify.left_inverse hreg
  have hy : event.limit_identify.map x ∈
      event.limit_identify.inverse ⁻¹' interior event.retained_pre := by
    change event.limit_identify.inverse (event.limit_identify.map x) ∈
      interior event.retained_pre
    rwa [hleft]
  have h := (sectional_positive_iff_of_local_isometry event.limit_connection D
    hU hf hm hy).mp hpos
  exact congrArg event.retention.map hleft ▸ h



theorem positive_sectional_on_postLabel
    (event : SurgeryEventData g0 K P slice metric T)
    (D : LeviCivitaData (metric T))
    {S : Set (slice event.tMinus).carrier} (hS : IsClopen S)
    (hterminal : ∀ x ∈ S, x ∈ event.regular_limit →
      ∀ u v : TangentSpace (𝓡 3) (event.limit_identify.map x),
        LeviCivitaData.IsOrthonormalPair event.limit_metric
          (event.limit_identify.map x) u v →
            0 < event.limit_connection.sectionalCurvature (event.limit_identify.map x) u v) :
    ∀ y ∈ surgeryPostLabel event S, ∀ u v : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (metric T) y u v →
        0 < D.sectionalCurvature y u v := by
  have hcappos (i : Fin event.cap_count) (hi : preAttachment event i ⊆ S) :
      ∀ y ∈ (event.caps i).carrier, ∀ u v : TangentSpace (𝓡 3) y,
        LeviCivitaData.IsOrthonormalPair (metric T) y u v →
          0 < D.sectionalCurvature y u v := by
    apply positive_sectional_on_surgery_cap event D i
    intro z hz
    have hlabel := inverse_neck_subset_of_attachment_label event hS i hi
      (mem_image_of_mem event.limit_identify.inverse hz)
    have hreg : event.limit_identify.inverse z ∈ event.regular_limit :=
      event.limit_identify.inverse_image.subset
        (mem_image_of_mem event.limit_identify.inverse (mem_univ z))
    have h := hterminal _ hlabel hreg
    rwa [event.limit_identify.right_inverse (mem_univ z)] at h
  intro y hy
  by_cases hcap : ∃ i, y ∈ (event.caps i).carrier
  · obtain ⟨i, hi⟩ := hcap
    rcases disjoint_or_subset_of_isClopen
        (preAttachment_isConnected event i).isPreconnected hS with hd | hl
    · have hother : preAttachment event i ⊆ Sᶜ := fun x hx hxs =>
        Set.disjoint_left.mp hd hx hxs
      exact False.elim (Set.disjoint_left.mp (surgeryPostLabel_disjoint event S)
        hy (Or.inr (mem_iUnion.mpr ⟨⟨i, hother⟩, hi⟩)))
    · exact hcappos i hl y hi
  · rcases hy with ⟨x, hx, rfl⟩ | hy
    · have hnocap : ∀ i, event.retention.map x ∉ (event.caps i).carrier :=
        fun i hi => hcap ⟨i, hi⟩
      exact positive_sectional_on_retained_interior event D
        (retained_interior_of_not_in_caps event hx.1 hnocap)
        (hterminal x hx.2 (event.retained_pre_subset hx.1))
    · obtain ⟨⟨i, _⟩, hi⟩ := mem_iUnion.mp hy
      exact False.elim (hcap ⟨i, hi⟩)



theorem positive_sectional_child_component
    (event : SurgeryEventData g0 K P slice metric T)
    (D : LeviCivitaData (metric T))
    {S : Set (slice event.tMinus).carrier} (hS : IsClopen S)
    (hterminal : ∀ x ∈ S, x ∈ event.regular_limit →
      ∀ u v : TangentSpace (𝓡 3) (event.limit_identify.map x),
        LeviCivitaData.IsOrthonormalPair event.limit_metric
          (event.limit_identify.map x) u v →
            0 < event.limit_connection.sectionalCurvature (event.limit_identify.map x) u v)
    {x : (slice event.tMinus).carrier} (hx : x ∈ event.retained_pre ∩ S) :
    ∀ y ∈ connectedComponent (event.retention.map x),
      ∀ u v : TangentSpace (𝓡 3) y,
        LeviCivitaData.IsOrthonormalPair (metric T) y u v →
          0 < D.sectionalCurvature y u v := by
  have hxLabel : event.retention.map x ∈ surgeryPostLabel event S :=
    Or.inl ⟨x, hx, rfl⟩
  have hC := (surgeryPostLabel_isClopen event hS).connectedComponent_subset hxLabel
  exact fun y hy => positive_sectional_on_postLabel event D hS hterminal y (hC hy)

end PoincareConjecture.Proofs.M46

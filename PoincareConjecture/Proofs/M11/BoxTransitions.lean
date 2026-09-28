import PoincareConjecture.Proofs.M11.BoxTopology
import PoincareConjecture.Proofs.M11.ManifoldCover





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem box_transition_smooth (A : AdaptedMetricAtlas n X) (b c : A.box_index) :
    ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞
      ((boxHomeomorph (A.box b)).trans (boxHomeomorph (A.box c)).symm)
      ((boxHomeomorph (A.box b)).trans (boxHomeomorph (A.box c)).symm).source := by
  let := intervalChartedSpace (A.box b).interval
  let := intervalChartedSpace (A.box c).interval
  intro p hp
  obtain ⟨T⟩ := box_transition_data A b c p hp.2
  have hcoords := box_transition_eventually_eq (A.box b) (A.box c) p T
  let f : boxDomain (A.box b) → boxDomain (A.box c) :=
    (boxHomeomorph (A.box c)).symm ∘ (A.box b).toSpacetime
  have ht : ContMDiffAt (spacetimeModel n) (𝓡∂ 1) ∞ (fun q ↦ (f q).1) p := by
    apply (contMDiffAt_interval_iff (A.box c).interval).mpr
    have hreal : ContMDiffAt (spacetimeModel n) 𝓘(ℝ) ∞
        (fun q : boxDomain (A.box b) ↦ q.1.val) p :=
      ((smoothInterval (A.box b).interval).inclusion_smooth p.1).comp p contMDiffAt_fst
    apply hreal.congr_of_eventuallyEq
    exact hcoords.mono fun _ h ↦ h.1
  have hx : ContMDiffAt (spacetimeModel n) (𝓡 n) ∞ (fun q ↦ (f q).2) p := by
    apply (ContMDiffAt.subtypeVal_comp_iff (A.box c).spatial _ p).mp
    have hspatial : ContMDiffAt (spacetimeModel n) (𝓡 n) ∞
        (fun q : boxDomain (A.box b) ↦ T.coordinateChange q.2.val) p :=
      (T.smooth.contDiffAt
        (T.coordinateChange.open_source.mem_nhds T.source_mem)).contMDiffAt.comp p
        (contMDiff_subtype_val.contMDiffAt.comp p contMDiffAt_snd)
    apply hspatial.congr_of_eventuallyEq
    exact hcoords.mono fun _ h ↦ h.2
  exact (ht.prodMk hx).contMDiffWithinAt

theorem box_targets_cover (A : AdaptedMetricAtlas n X) :
    ∀ p : X, ∃ b, p ∈ (boxHomeomorph (A.box b)).target := by
  intro p
  obtain ⟨b, q, rfl⟩ := A.box_covers p
  refine ⟨b, ?_⟩
  rw [boxHomeomorph_target]
  exact ⟨q, rfl⟩


noncomputable abbrev adaptedChartedSpace (A : AdaptedMetricAtlas n X) :
    ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) X :=
  coverChartedSpace (H := ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n)))
    (fun b ↦ boxHomeomorph (A.box b)) (box_targets_cover A)

theorem adapted_isManifold (A : AdaptedMetricAtlas n X) :
    letI := adaptedChartedSpace A
    IsManifold (spacetimeModel n) ∞ X :=
  cover_isManifold (fun b ↦ boxHomeomorph (A.box b)) (box_targets_cover A)
    (box_transition_smooth A)

theorem adapted_box_localDiffeomorph (A : AdaptedMetricAtlas n X) (b : A.box_index) :
    letI := intervalChartedSpace (A.box b).interval
    letI := adaptedChartedSpace A
    IsLocalDiffeomorph (spacetimeModel n) (spacetimeModel n) ∞ (A.box b).toSpacetime :=
  cover_localDiffeomorph (fun b ↦ boxHomeomorph (A.box b)) (box_targets_cover A)
    (box_transition_smooth A) b (boxHomeomorph_source (A.box b))

end PoincareConjecture.Proofs.M11

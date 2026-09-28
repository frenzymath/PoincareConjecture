import PoincareConjecture.Proofs.M28.Mathlib.OpenHeightNoncompact
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallInitialSides
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceInitialGraphIsotopy
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereSides










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 2400000 in




theorem not_isCompact_closure_retained_initial_side
    {epsilon C A : ℝ}
    {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)}
    (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
      (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (L : EpsilonNeck G.limitMetric) (X : Set G.limitCarrier.carrier),
      IsOpen X → X.Nonempty → frontier X = L.central_sphere →
      ∀ (sigma : ℕ → ℕ), StrictMono sigma →
      ∀ (f : ℕ → UnitTwoSphere → ℝ),
        (∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k)) →
        (∀ k z, |f k z| < epsilon⁻¹ / 32) →
        (∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
          W.high_index G (sigma k)) '' L.central_sphere =
            range (fun z =>
              ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                (z, f k z))) →
        ¬ IsCompact (closure X) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro L X hX hne hfront sigma hsigma f hf hbound hgraphs hcompact
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun j => subset_closure.trans (G.exhaustion_step j))
  obtain ⟨j, hj⟩ := hcompact.elim_directed_cover G.exhaustion G.exhaustion_open
    (by rw [G.exhaustion_covers]; exact subset_univ _) hmono.directed_le
  let k := sigma j
  let i := W.high_index (G.subsequence k)
  let T := W.tube i
  have hstage : closure X ⊆ G.exhaustion k := hj.trans (hmono (hsigma.id_le j))
  let F : G.limitCarrier.carrier → T.carrierOpen := fun x => (G.embedding k x).val
  have hF : ContinuousOn F (closure X) :=
    (continuous_subtype_val.comp_continuousOn
      (G.embedding_smooth k).contMDiffOn.continuousOn).mono hstage
  let e : G.exhaustion k → H.tubeCriticalRegion W.tube W.radius i :=
    fun x => G.embedding k x
  have heopen : IsOpen (e '' ((Subtype.val : G.exhaustion k → _) ⁻¹' X)) :=
    (G.embedding_open k).isOpenMap _ (hX.preimage continuous_subtype_val)
  have hFopen : IsOpen (F '' X) := by
    have hh : IsOpen
        ((Subtype.val : H.tubeCriticalRegion W.tube W.radius i → T.carrierOpen) ''
          (e '' ((Subtype.val : G.exhaustion k → _) ⁻¹' X))) :=
      (H.tubeCriticalRegion W.tube W.radius i).isOpen.isOpenMap_subtype_val _ heopen
    have heq : (Subtype.val : H.tubeCriticalRegion W.tube W.radius i → T.carrierOpen) ''
        (e '' ((Subtype.val : G.exhaustion k → _) ⁻¹' X)) = F '' X := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z.val, hz, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨G.embedding k y, ⟨⟨y, hstage (subset_closure hy)⟩, hy, rfl⟩, rfl⟩
    exact heq ▸ hh
  obtain ⟨phi, a, b, _ha, _ha', _hb, _hb', hzero, _htail⟩ :=
    T.tube.cylinder.exists_isotopic_sphere_coordinates (U := T.carrierOpen)
      (T.initial_graph_isotopic_middle (f j) (hf j) (hbound j))
  let height := cylinderSignedHeight phi ∘ F
  have hcontinuous : ContinuousOn height (closure X) :=
    (continuous_cylinderSignedHeight phi).comp_continuousOn hF
  have hopen : IsOpen (height '' X) := by
    rw [show height '' X = cylinderSignedHeight phi '' (F '' X) from
      (image_image (cylinderSignedHeight phi) F X).symm]
    exact isOpenMap_cylinderSignedHeight phi _ hFopen
  apply Poincare.not_isCompact_closure_of_open_height hX hne hcontinuous hopen
    (c := 0) _ hcompact
  intro x hx
  have hxS : x ∈ L.central_sphere := hfront ▸ hx
  have hxgraph : (F x).val ∈ range (fun z : UnitTwoSphere =>
      (T.list.node 0).2.coordinate_map (z, f j z)) := by
    rw [← hgraphs j]
    exact mem_image_of_mem _ hxS
  have hh := (hzero (F x)).mpr hxgraph
  exact sub_eq_zero.mpr hh

end PoincareConjecture.M28.CounterexampleNeckFamily

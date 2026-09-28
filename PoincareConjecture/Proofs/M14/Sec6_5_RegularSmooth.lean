import PoincareConjecture.Proofs.M14.Sec6_3_JointMap
import PoincareConjecture.Proofs.M14.Sec6_3_ActionSmooth
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem reducedLengthAt_jointEndpoint (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hz : (Z, s) ∈ M14JointDomain G E) :
    M14ReducedLengthAt G T 0 x (E.gamma Z s) = E.action Z s / (2 * s) := by
  have hs := jointDomain_time_pos E hz
  have hsurv := jointDomain_subset_domain E hz
  obtain ⟨_, _, _, _, _, hlength⟩ := jointDomain_action_branch E hz
  unfold M14ReducedLengthAt
  rw [E.clock Z s hsurv, sub_sub_cancel, ← hlength, E.reduced_length_eq Z s hsurv hs]

theorem reducedLengthAt_jointInverse (E : M14ExponentialFamily G T x) {q : G.Point}
    (hq : q ∈ range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)) :
    M14ReducedLengthAt G T 0 x q =
      E.action (jointEndpointInverse E q).1 (jointEndpointInverse E q).2 /
        (2 * (jointEndpointInverse E q).2) := by
  obtain ⟨hmem, heq⟩ := jointEndpointInverse_spec E hq
  exact (congrArg (M14ReducedLengthAt G T 0 x) heq).symm.trans
    (reducedLengthAt_jointEndpoint E (Z := (jointEndpointInverse E q).1)
      (s := (jointEndpointInverse E q).2) hmem)

theorem reducedLengthAt_contMDiffOn_jointImage
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) :
    ContMDiffOn (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ (M14ReducedLengthAt G T 0 x)
      (range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hinv : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, G.Horizontal x × ℝ)) ∞
      (jointEndpointInverse E)
      (range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)) :=
    jointEndpointInverse_smooth E
  have ha : ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
      (fun z => E.action z.1 z.2) (E.domain ∩ {z | 0 < z.2}) :=
    exponentialFamily_action_smooth hM04 hM12 E
  have hinv' : ContMDiffOn (spacetimeModel n)
      ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ))) ∞ (jointEndpointInverse E)
      (range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hinv
  have hmap : MapsTo (jointEndpointInverse E)
      (range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2))
      (E.domain ∩ {z | 0 < z.2}) := by
    intro q hq
    have hz := (jointEndpointInverse_spec E hq).1
    exact ⟨jointDomain_subset_domain E hz, jointDomain_time_pos E hz⟩
  have haction := ha.comp hinv' hmap
  have htime := (ContinuousLinearMap.snd ℝ (G.Horizontal x) ℝ).contMDiff.comp_contMDiffOn hinv
  have hnorm := haction.div₀ ((contMDiffOn_const (c := (2 : ℝ))).mul htime)
    (fun q hq => mul_ne_zero (by norm_num) (jointDomain_time_pos E
      (jointEndpointInverse_spec E hq).1).ne')
  exact hnorm.congr (fun q hq => reducedLengthAt_jointInverse E hq)

theorem reducedLengthAt_slice_contMDiffAt
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {t : ℝ} (q : (G.slices t).Point)
    (hq : q.val ∈ range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun r : (G.slices t).Point => M14ReducedLengthAt G T 0 x r.val) q := by
  have h := ((reducedLengthAt_contMDiffOn_jointImage hM04 hM12 E) q.val hq).contMDiffAt
    ((jointMap_range_isOpen E).mem_nhds hq)
  have hi : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (fun r : (G.slices t).Point => r.val) := (G.slices t).inclusion_smooth
  exact h.comp q hi.contMDiffAt

end PoincareConjecture.M14

import PoincareConjecture.Proofs.M11.IntervalMaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J' : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

theorem interval_family_smoothOn (I : SpacetimeInterval)
    {f : (smoothInterval I).Point × M → N} {g : ℝ × M → N}
    (hf : ContMDiff ((𝓡∂ 1).prod J) J' ∞ f)
    (hg : ∀ (t : (smoothInterval I).Point) (x : M), g (t.val, x) = f (t, x)) :
    ContMDiffOn (𝓘(ℝ).prod J) J' ∞ g (I.domain ×ˢ univ) := by
  let := intervalChartedSpace I
  intro p hp
  let D := intervalSegmentAt I ⟨p.1, hp.1⟩
  let : Fact (D.left < D.right) := ⟨D.lt⟩
  let U : Set (ℝ × M) := D.window ×ˢ univ
  let S : Set (ℝ × M) := (I.domain ×ˢ univ) ∩ U
  have hpU : p ∈ U := ⟨intervalSegmentAt_mem I ⟨p.1, hp.1⟩, mem_univ _⟩
  have hU : U ∈ 𝓝 p := (D.open_window.prod isOpen_univ).mem_nhds hpU
  apply (contMDiffWithinAt_inter hU).mp
  have hinc : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ D.toSegment.symm := by
    apply (contMDiff_interval_iff I).mpr
    exact contMDiff_subtypeVal_Icc
  have hpseg : p.1 ∈ Icc D.left D.right := D.window_subset ⟨hpU.1, hp.1⟩
  have hproj : ContMDiffWithinAt (𝓘(ℝ).prod J) (𝓡∂ 1) ∞
      (fun q : ℝ × M ↦ projIcc D.left D.right D.lt.le q.1) S p := by
    apply (contMDiffOn_projIcc p.1 hpseg).comp p contMDiffWithinAt_fst
    intro q hq
    exact D.window_subset ⟨hq.2.1, hq.1.1⟩
  have hs := (hf.comp (hinc.prodMap contMDiff_id)).contMDiffAt.comp_contMDiffWithinAt p
    (hproj.prodMk contMDiffWithinAt_snd)
  apply hs.congr_of_mem _ ⟨hp, hpU⟩
  intro q hq
  change g q = f (D.toSegment.symm (projIcc D.left D.right D.lt.le q.1), q.2)
  rw [hg ⟨q.1, hq.1.1⟩ q.2]
  congr 1
  apply Prod.ext
  · apply Subtype.ext
    exact (congrArg Subtype.val
      (projIcc_of_mem D.lt.le (D.window_subset ⟨hq.2.1, hq.1.1⟩))).symm
  · rfl

end PoincareConjecture.Proofs.M11

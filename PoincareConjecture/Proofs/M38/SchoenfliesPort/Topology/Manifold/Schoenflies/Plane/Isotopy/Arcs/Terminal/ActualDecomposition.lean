import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualEndDisk







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel SphereSurgeryCoreCap
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev S1 := sphere (0 : E2) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_flatten_height (d : TerminalSaddleGeometry M P p e) (y : E3) :
    d.flatten y 2 = inner Real (M.v : E3) y := by
  change d.frame (d.D y) 2 = _
  rw [d.frame_height, d.D_height]

theorem terminal_actualBand_eq_image_height_band (d : TerminalSaddleGeometry M P p e) :
    d.actualBand = (d.flatten ∘ g) ''
      {q | inner Real (M.v : E3) (g q) ∈ d.I} := by
  have hcoord (y : E3) : Saddle.toE3 (Saddle.toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  ext y
  constructor
  · intro hy
    obtain ⟨z, hy⟩ := mem_iUnion.mp hy
    obtain ⟨hz, hy⟩ := mem_iUnion.mp hy
    change Saddle.toE3 (Saddle.toE2 y) z ∈ d.flatten '' range g ∧ y 2 = z at hy
    obtain ⟨w, ⟨q, rfl⟩, hw⟩ := hy.1
    have heq : d.flatten (g q) = y := by
      rw [← hy.2] at hw
      exact hw.trans (hcoord y)
    refine ⟨q, ?_, heq⟩
    change inner Real (M.v : E3) (g q) ∈ d.I
    rw [← terminal_flatten_height d, heq, hy.2]
    exact hz
  · rintro ⟨q, hq, rfl⟩
    refine mem_iUnion_of_mem (d.flatten (g q) 2) (mem_iUnion_of_mem ?_ ?_)
    · rwa [terminal_flatten_height]
    · change Saddle.toE3 (Saddle.toE2 (d.flatten (g q))) (d.flatten (g q) 2) ∈
        d.flatten '' range g ∧ _
      exact ⟨hcoord _ ▸ mem_image_of_mem _ (mem_range_self q), rfl⟩

theorem terminal_height_band_eq_middleRegion (d : TerminalSaddleGeometry M P p e) :
    {q | inner Real (M.v : E3) (g q) ∈ d.I} = d.ends.middleRegion := by
  ext q
  constructor
  · intro hq
    have hcore : q ∈ P.core := by
      rw [d.ends.core_complement]
      intro hqcap
      obtain ⟨D, hD, x, hx, rfl⟩ := by simpa only [mem_iUnion, mem_image] using hqcap
      have hout := d.ends.cap_height_outside_middle D hD x (ball_subset_closedBall hx)
      rw [← D.parametrization_eq x (ball_subset_closedBall hx)] at hout
      rcases hout with hl | hu
      · exact (not_lt_of_ge hq.1) hl
      · exact (not_lt_of_ge hq.2) hu
    refine ⟨hcore, ?_⟩
    change d.ends.height q ∈ Icc d.ends.lowerCut d.ends.upperCut
    rw [(d.ends.height_germ q hcore).eq_of_nhds]
    exact hq
  · rintro ⟨hcore, hq⟩
    change d.ends.height q ∈ Icc d.ends.lowerCut d.ends.upperCut at hq
    rw [(d.ends.height_germ q hcore).eq_of_nhds] at hq
    exact hq

theorem terminal_actualBand_eq_image_middleRegion (d : TerminalSaddleGeometry M P p e) :
    d.actualBand = (d.flatten ∘ g) '' d.ends.middleRegion := by
  rw [terminal_actualBand_eq_image_height_band, terminal_height_band_eq_middleRegion]



theorem terminal_actual_decomposition (d : TerminalSaddleGeometry M P p e) :
    d.flatten '' range g = d.actualBand ∪ ⋃ i, d.C i := by
  rw [terminal_actualBand_eq_image_middleRegion]
  apply Subset.antisymm
  · rintro y ⟨w, ⟨q, rfl⟩, rfl⟩
    have hcap (i : d.ends.EndIndex) (hq : q ∈ terminalEndCap d.ends i) :
        d.flatten (g q) ∈ ⋃ j, d.C j := by
      refine mem_iUnion_of_mem (d.labels.symm i) ?_
      change d.flatten (g q) ∈ (d.flatten ∘ g) ''
        terminalEndCap d.ends (d.labels (d.labels.symm i))
      rw [d.labels.apply_symm_apply]
      exact mem_image_of_mem _ hq
    by_cases hq : q ∈ P.core
    · rw [d.ends.core_eq_middle_union_ends] at hq
      rcases hq with hm | he
      · exact Or.inl (mem_image_of_mem _ hm)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp he
        exact Or.inr (hcap i (Or.inl hi))
    · have hqcap : q ∈ ⋃ D ∈ d.ends.caps, D.chart '' ball (0 : E2) 1 := by
        by_contra hqcap
        exact hq (d.ends.core_complement.symm ▸ hqcap)
      obtain ⟨D, hD, x, hx, rfl⟩ := by simpa only [mem_iUnion, mem_image] using hqcap
      rcases d.ends.cap_side D hD with hl | hu
      · exact Or.inr (hcap (.inl ⟨⟨D, hD⟩, hl⟩)
          (Or.inr (mem_image_of_mem _ (ball_subset_closedBall hx))))
      · exact Or.inr (hcap (.inr ⟨⟨D, hD⟩, hu⟩)
          (Or.inr (mem_image_of_mem _ (ball_subset_closedBall hx))))
  · rintro y (⟨q, _, rfl⟩ | hy)
    · exact mem_image_of_mem _ (mem_range_self q)
    · obtain ⟨i, q, _, rfl⟩ := by
        simpa only [mem_iUnion, TerminalSaddleGeometry.C, mem_image] using hy
      exact mem_image_of_mem _ (mem_range_self q)

theorem terminal_endCap_inter_height_band (d : TerminalSaddleGeometry M P p e)
    (i : d.ends.EndIndex) :
    terminalEndCap d.ends i ∩ {q | inner Real (M.v : E3) (g q) ∈ d.I} =
      match i with
      | .inl j => range (d.ends.lowerCutCircle j)
      | .inr j => range (d.ends.upperCutCircle j) := by
  rcases i with j | j
  · let A := d.ends.lower j.1.1 j.1.2 j.2
    ext q
    constructor
    · rintro ⟨hq, hheight⟩
      rcases hq with hregion | hcap
      · obtain ⟨⟨x, t⟩, ⟨_, ht⟩, rfl⟩ := hregion
        have hh := A.actual_height x t ht
        have heq : t = d.ends.lowerCut := by
          change inner Real (M.v : E3) (g (A.chart (x, t))) ∈ d.I at hheight
          rw [hh] at hheight
          exact le_antisymm ht.2 hheight.1
        subst t
        exact mem_range_self x
      · have hh := A.height_le_center_of_mem_cap hcap
        exact (not_le_of_gt j.2) (hheight.1.trans hh) |>.elim
    · rintro ⟨x, rfl⟩
      refine ⟨Or.inl (mem_image_of_mem A.chart ⟨mem_univ x, j.2.le, le_rfl⟩), ?_⟩
      change inner Real (M.v : E3) (g (A.chart (x, d.ends.lowerCut))) ∈ d.I
      rw [A.actual_height x _ ⟨j.2.le, le_rfl⟩]
      exact ⟨le_rfl, d.ends.cuts_lt.le⟩
  · let A := d.ends.upper j.1.1 j.1.2 j.2
    ext q
    constructor
    · rintro ⟨hq, hheight⟩
      rcases hq with hregion | hcap
      · change q ∈ A.region at hregion
        rw [A.region_eq_image] at hregion
        obtain ⟨⟨x, t⟩, ⟨_, ht⟩, rfl⟩ := hregion
        have hh := A.actual_height x t ht
        have heq : t = d.ends.upperCut := by
          change inner Real (M.v : E3) (g (A.chart (x, t))) ∈ d.I at hheight
          rw [hh] at hheight
          exact le_antisymm hheight.2 ht.1
        subst t
        exact mem_range_self x
      · obtain ⟨x, hx, rfl⟩ := hcap
        have hh := mul_nonneg (j.1.1.normalized_height_nonneg hx) A.scale_pos.le
        rw [div_mul_cancel₀ _ j.1.1.scale_ne_zero] at hh
        have hle := hheight.2
        rw [j.1.1.parametrization_eq x hx] at hle
        linarith [j.2]
    · rintro ⟨x, rfl⟩
      refine ⟨Or.inl ?_, ?_⟩
      · change A.chart (x, d.ends.upperCut) ∈ A.region
        rw [A.region_eq_image]
        exact mem_image_of_mem _ ⟨mem_univ x, le_rfl, j.2.le⟩
      · change inner Real (M.v : E3) (g (A.chart (x, d.ends.upperCut))) ∈ d.I
        rw [A.actual_height x _ ⟨le_rfl, j.2.le⟩]
        exact ⟨d.ends.cuts_lt.le, le_rfl⟩



theorem exists_terminal_actual_disks_with_band_boundary
    (d : TerminalSaddleGeometry M P p e) (hg : g ∈ M.tree.leaves) :
    ∃ m : Fin 3 → OpenPartialHomeomorph E2 S2, ∀ i,
      closedBall 0 1 ⊆ (m i).source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ (m i) (m i).source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ (m i).symm (m i).target ∧
      m i '' closedBall 0 1 = terminalEndCap d.ends (d.labels i) ∧
      d.C i ∩ d.actualBand = (d.flatten ∘ g ∘ m i) '' sphere (0 : E2) 1 := by
  obtain ⟨m, hm⟩ := exists_terminal_actual_end_disks d
  refine ⟨m, fun i => ⟨(hm i).1, (hm i).2.1, (hm i).2.2.1, (hm i).2.2.2.1, ?_⟩⟩
  rw [terminal_actualBand_eq_image_height_band]
  change (d.flatten ∘ g) '' terminalEndCap d.ends (d.labels i) ∩
    (d.flatten ∘ g) '' {q | inner Real (M.v : E3) (g q) ∈ d.I} = _
  have hinj : Injective (d.flatten ∘ g) := d.flatten.injective.comp
    (M.tree.embedding_of_mem_leaves hg).isEmbedding.injective
  rw [← image_inter hinj, terminal_endCap_inter_height_band]
  exact (congrArg (fun S => (d.flatten ∘ g) '' S) (hm i).2.2.2.2.symm).trans
    (by rw [image_image]; rfl)

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies

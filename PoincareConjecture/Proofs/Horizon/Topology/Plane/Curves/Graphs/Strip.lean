import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false
open Set
open scoped ContDiff

namespace Poincare.Topology.Plane.Curves

def graphStripMap (lo hi : ℝ → ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1, lo q.1 + q.2 * (hi q.1 - lo q.1))

noncomputable def graphStripInv (lo hi : ℝ → ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1, (q.2 - lo q.1) / (hi q.1 - lo q.1))

@[simp] theorem graphStripMap_lower (lo hi : ℝ → ℝ) (t : ℝ) :
    graphStripMap lo hi (t, 0) = (t, lo t) := by simp [graphStripMap]

@[simp] theorem graphStripMap_upper (lo hi : ℝ → ℝ) (t : ℝ) :
    graphStripMap lo hi (t, 1) = (t, hi t) := by simp [graphStripMap]

theorem contDiffOn_graphStripMap {lo hi : ℝ → ℝ} {U : Set ℝ}
    (hlo : ContDiffOn ℝ ∞ lo U) (hhi : ContDiffOn ℝ ∞ hi U) :
    ContDiffOn ℝ ∞ (graphStripMap lo hi) (U ×ˢ (univ : Set ℝ)) := by
  have hl : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => lo q.1) (U ×ˢ univ) :=
    hlo.comp contDiffOn_fst (fun _ h => h.1)
  have hh : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => hi q.1) (U ×ˢ univ) :=
    hhi.comp contDiffOn_fst (fun _ h => h.1)
  exact contDiffOn_fst.prodMk (hl.add (contDiffOn_snd.mul (hh.sub hl)))

theorem contDiffOn_graphStripInv {lo hi : ℝ → ℝ} {U : Set ℝ}
    (hlo : ContDiffOn ℝ ∞ lo U) (hhi : ContDiffOn ℝ ∞ hi U)
    (hgap : ∀ t ∈ U, lo t < hi t) :
    ContDiffOn ℝ ∞ (graphStripInv lo hi) (U ×ˢ (univ : Set ℝ)) := by
  have hl : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => lo q.1) (U ×ˢ univ) :=
    hlo.comp contDiffOn_fst (fun _ h => h.1)
  have hh : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => hi q.1) (U ×ˢ univ) :=
    hhi.comp contDiffOn_fst (fun _ h => h.1)
  exact contDiffOn_fst.prodMk ((contDiffOn_snd.sub hl).div (hh.sub hl)
    (fun q hq => ne_of_gt (sub_pos.mpr (hgap q.1 hq.1))))

noncomputable def graphStripCoordinates {lo hi : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hlo : ContDiffOn ℝ ∞ lo U) (hhi : ContDiffOn ℝ ∞ hi U)
    (hgap : ∀ t ∈ U, lo t < hi t) : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun := graphStripMap lo hi
  invFun := graphStripInv lo hi
  source := U ×ˢ univ
  target := U ×ˢ univ
  map_source' q hq := ⟨hq.1, mem_univ _⟩
  map_target' q hq := ⟨hq.1, mem_univ _⟩
  left_inv' q hq := by
    refine Prod.ext rfl ?_
    dsimp [graphStripInv, graphStripMap]
    have hn : hi q.1 - lo q.1 ≠ 0 := ne_of_gt (sub_pos.mpr (hgap q.1 hq.1))
    field_simp [hn]
    ring
  right_inv' q hq := by
    refine Prod.ext rfl ?_
    dsimp [graphStripInv, graphStripMap]
    have hn : hi q.1 - lo q.1 ≠ 0 := ne_of_gt (sub_pos.mpr (hgap q.1 hq.1))
    rw [div_mul_cancel₀ _ hn]
    ring
  open_source := hU.prod isOpen_univ
  open_target := hU.prod isOpen_univ
  continuousOn_toFun := (contDiffOn_graphStripMap hlo hhi).continuousOn
  continuousOn_invFun := (contDiffOn_graphStripInv hlo hhi hgap).continuousOn

theorem graphStripMap_image_rectangle {lo hi : ℝ → ℝ} {a b : ℝ}
    (hgap : ∀ t ∈ Icc a b, lo t < hi t) :
    graphStripMap lo hi '' (Icc a b ×ˢ Icc (0 : ℝ) 1) =
      {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1} := by
  ext q
  constructor
  · rintro ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
    dsimp [graphStripMap]
    have hg := hgap t ht
    exact ⟨ht, by nlinarith [mul_nonneg hs.1 (sub_pos.mpr hg).le],
      by nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_pos.mpr hg).le]⟩
  · rintro ⟨ht, hlow, hupp⟩
    have hg : 0 < hi q.1 - lo q.1 := sub_pos.mpr (hgap q.1 ht)
    refine ⟨graphStripInv lo hi q, ⟨ht, ?_⟩, ?_⟩
    · exact ⟨div_nonneg (sub_nonneg.mpr hlow) hg.le,
        (div_le_one hg).mpr (sub_le_sub_right hupp _)⟩
    · refine Prod.ext rfl ?_
      dsimp [graphStripMap, graphStripInv]
      rw [div_mul_cancel₀ _ (ne_of_gt hg)]
      ring

end Poincare.Topology.Plane.Curves

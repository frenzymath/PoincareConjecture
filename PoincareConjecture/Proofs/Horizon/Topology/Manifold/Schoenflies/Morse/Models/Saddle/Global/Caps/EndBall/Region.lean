import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.UpperFamily








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.LowerAnnularEnd

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real}
  {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}


def cappedRegion (A : LowerAnnularEnd D C h a b) (c : Real) : Set S2 :=
  (D.chart '' closedBall 0 1) ∪ A.chart '' (univ ×ˢ Icc D.center c)

theorem terminal_subset_cappedRegion (A : LowerAnnularEnd D C h a b)
    {c : Real} (hDc : D.center ≤ c) :
    range (fun q : S1 => A.chart (q, c)) ⊆ A.cappedRegion c := by
  rintro p ⟨q, rfl⟩
  exact Or.inr (mem_image_of_mem _ ⟨mem_univ _, hDc, le_rfl⟩)

theorem cappedRegion_mono (A : LowerAnnularEnd D C h a b)
    {c d : Real} (hcd : c ≤ d) : A.cappedRegion c ⊆ A.cappedRegion d :=
  union_subset_union_right _ (image_mono (prod_mono Subset.rfl (Icc_subset_Icc_right hcd)))

theorem isCompact_cappedRegion (A : LowerAnnularEnd D C h a b)
    (haD : a ≤ D.center) {c : Real} (hcb : c ≤ b) :
    IsCompact (A.cappedRegion c) := by
  apply IsCompact.union
  · exact (isCompact_closedBall 0 1).image_of_continuousOn
      (D.chart.continuousOn.mono D.source)
  · apply (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    apply A.chart.continuousOn.mono
    rintro ⟨q, t⟩ ⟨_, ht⟩
    rw [A.source]
    exact ⟨mem_univ _, by linarith [ht.1, A.delta_pos],
      by linarith [ht.2, A.delta_pos]⟩

theorem height_le_center_of_mem_cap (A : LowerAnnularEnd D C h a b)
    {p : S2} (hp : p ∈ D.chart '' closedBall (0 : E2) 1) :
    inner Real v (g p) ≤ D.center := by
  obtain ⟨x, hx, rfl⟩ := hp
  rw [D.parametrization_eq x hx]
  have hh := mul_nonpos_of_nonneg_of_nonpos (D.normalized_height_nonneg hx) A.scale_neg.le
  rw [div_mul_cancel₀ _ D.scale_ne_zero] at hh
  linarith

theorem annulus_inter_cap (A : LowerAnnularEnd D C h a b)
    {c : Real} (hDc : D.center ≤ c) (hcb : c ≤ b) :
    (A.chart '' (univ ×ˢ Icc D.center c)) ∩ (D.chart '' closedBall (0 : E2) 1) =
      D.chart '' sphere (0 : E2) 1 := by
  apply Subset.antisymm
  · rintro p ⟨⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, hp⟩
    have hh := A.height_le_center_of_mem_cap hp
    rw [A.actual_height q t ⟨ht.1, ht.2.trans hcb⟩] at hh
    have heq : t = D.center := le_antisymm hh ht.1
    rw [← A.boundary, heq]
    exact mem_range_self q
  · intro p hp
    refine ⟨?_, image_mono sphere_subset_closedBall hp⟩
    rw [← A.boundary] at hp
    obtain ⟨q, rfl⟩ := hp
    exact mem_image_of_mem _ ⟨mem_univ _, le_rfl, hDc⟩


theorem exists_physical_terminal_collar (A : LowerAnnularEnd D C h a b)
    {c : Real} (hDc : D.center < c) (hcb : c < b) :
    ∃ ε : Real, 0 < ε ∧ Icc (c - ε) (c + ε) ⊆ Ioo D.center b ∧
      A.chart '' (univ ×ˢ Icc (c - ε) (c + ε)) ⊆ _root_.interior C ∧
      ∀ q t, t ∈ Icc (c - ε) (c + ε) →
        inner Real v (g (A.chart (q, t))) = t := by
  let ε := min (c - D.center) (b - c) / 2
  have hε : 0 < ε := half_pos (lt_min (sub_pos.mpr hDc) (sub_pos.mpr hcb))
  have hsub : Icc (c - ε) (c + ε) ⊆ Ioo D.center b := by
    intro t ht
    dsimp [ε] at ht
    constructor
    · linarith [ht.1, min_le_left (c - D.center) (b - c)]
    · linarith [ht.2, min_le_right (c - D.center) (b - c)]
  refine ⟨ε, hε, hsub, ?_, ?_⟩
  · exact (image_mono (prod_mono Subset.rfl hsub)).trans A.interior
  · intro q t ht
    exact A.actual_height q t ⟨(hsub ht).1.le, (hsub ht).2.le⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.LowerAnnularEnd

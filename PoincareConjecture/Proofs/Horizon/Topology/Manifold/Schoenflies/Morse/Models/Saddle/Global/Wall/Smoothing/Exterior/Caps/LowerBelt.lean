import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Rim
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Regular.Range



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

open SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)



theorem exists_lower_end_truncated_cap_decomposition
    {v : E3} {g : S2 → E3} {P : Set Real}
    {D : SphereSurgeryCoreCap v g P} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (haD : a ≤ D.center)
    {c : Real} (hDc : D.center < c) (hcb : c < b)
    (hgerm : ∀ p ∈ D.chart '' sphere (0 : E2) 1,
      h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    ∃ δ η : Real, 0 < δ ∧ 0 < η ∧ η < 1 ∧
      ∃ T : OpenPartialHomeomorph (S1 × Real) S2,
        T.source = univ ×ˢ Ioo (D.center - δ) (c + δ) ∧
        ContMDiffOn IP (𝓡 2) ∞ T T.source ∧
        ContMDiffOn (𝓡 2) IP ∞ T.symm T.target ∧
        (∀ z, T z = A.chart z) ∧
        (∀ q t, t ∈ Ioo (D.center - δ) (c + δ) →
          inner Real v (g (T (q, t))) = t) ∧
        D.center + D.scale * η ∈ Ioo (D.center - δ) (c + δ) ∧
        g '' A.cappedRegion c = D.truncatedImage η ∪
          g '' (T '' (univ ×ˢ Icc (D.center + D.scale * η) c)) ∧
        ∀ θ ∈ Icc (0 : Real) η,
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto
            (g (T (q, D.center + D.scale * θ)))) =
              D.planeMap '' sphere (0 : Hemisphere.Plane v) 1 := by
  obtain ⟨δ, hδ, T, hTs, hT, hTi, hTA, hheight, hboundary⟩ :=
    exists_lower_physical_annulus_across_rim A haD hDc hcb hgerm
  have hcenter : D.center ∈ Ioo (D.center - δ) (c + δ) := by
    constructor <;> linarith
  have htarget : D.chart '' sphere (0 : E2) 1 ⊆ T.target := by
    rw [← hboundary]
    rintro p ⟨q, rfl⟩
    apply T.map_source
    rw [hTs]
    exact ⟨mem_univ _, hcenter⟩
  obtain ⟨η, hη, hη1, hbelt⟩ := D.exists_annular_cap_belt hg T hTs hT hTi
    hheight hcenter htarget
  have hcut : D.center + D.scale * η < D.center := by nlinarith [A.scale_neg]
  refine ⟨δ, η, hδ, hη, hη1, T, hTs, hT, hTi, hTA, hheight,
    (hbelt η ⟨hη.le, le_rfl⟩).1, ?_,
    fun θ hθ => D.projected_slice_eq_circle T _ (hbelt θ hθ).2.2⟩
  apply Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    rcases hp with hpCap | ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    · by_cases hlarge : η ≤ (inner Real v (g p) - D.center) / D.scale
      · exact Or.inl ⟨D.image_closedBall ▸ mem_image_of_mem g hpCap, hlarge⟩
      · obtain ⟨x, hx, rfl⟩ := hpCap
        let θ := (inner Real v (g (D.chart x)) - D.center) / D.scale
        have hθ : θ ∈ Icc (0 : Real) η := by
          refine ⟨?_, (lt_of_not_ge hlarge).le⟩
          dsimp [θ]
          rw [D.parametrization_eq x hx]
          exact D.normalized_height_nonneg hx
        have hlevel : inner Real v (g (D.chart x)) = D.center + D.scale * θ := by
          dsimp [θ]
          field_simp [D.scale_ne_zero]
          ring
        have hpSlice : D.chart x ∈ range (fun q : S1 => T (q, D.center + D.scale * θ)) :=
          (hbelt θ hθ).2.1 ▸ ⟨mem_image_of_mem D.chart hx, hlevel⟩
        obtain ⟨q, hq⟩ := hpSlice
        refine Or.inr ⟨D.chart x, ⟨(q, D.center + D.scale * θ), ?_, hq⟩, rfl⟩
        exact ⟨mem_univ _, by nlinarith [A.scale_neg, hθ.2],
          by nlinarith [A.scale_neg, hθ.1]⟩
    · refine Or.inr ⟨A.chart (q, t), ⟨(q, t), ?_, hTA (q, t)⟩, rfl⟩
      exact ⟨mem_univ _, hcut.le.trans ht.1, ht.2⟩
  · rintro y (hyCap | ⟨p, ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, rfl⟩)
    · have hy := D.image_closedBall.symm ▸ hyCap.1
      obtain ⟨p, hp, rfl⟩ := hy
      exact ⟨p, Or.inl hp, rfl⟩
    · refine ⟨T (q, t), ?_, rfl⟩
      by_cases htD : D.center ≤ t
      · exact Or.inr ⟨(q, t), ⟨mem_univ _, htD, ht.2⟩, (hTA (q, t)).symm⟩
      · let θ := (t - D.center) / D.scale
        have hθ : θ ∈ Icc (0 : Real) η := by
          refine ⟨div_nonneg_of_nonpos (by linarith) A.scale_neg.le, ?_⟩
          apply (div_le_iff_of_neg A.scale_neg).mpr
          linarith [ht.1]
        have heq : D.center + D.scale * θ = t := by
          dsimp [θ]
          field_simp [D.scale_ne_zero]
          ring
        have hpSlice : T (q, t) ∈ (D.chart '' closedBall 0 1) ∩
            {p : S2 | inner Real v (g p) = D.center + D.scale * θ} := by
          rw [(hbelt θ hθ).2.1, heq]
          exact mem_range_self q
        exact Or.inl hpSlice.1

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

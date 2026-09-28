import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripArmCharts



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem exists_horizontal_square_edge_parameter
    {E : Set P2} (H : Sq ≃ₜ E) (hH : H.IsFinitePL) {k : ℝ} (hk : k ∈ I) :
    ∃ q : I ≃ₜ range (fun t : I ↦ (H ⟨(t, k), t.property, hk⟩ : P2)),
      q.IsFinitePL ∧ ∀ t : I, (q t : P2) = H ⟨(t, k), t.property, hk⟩ := by
  obtain ⟨p, hp, hpval⟩ := hH
  have hsub : arm k ⊆ Sq := by
    intro z hz
    exact ⟨hz.1, hz.2.symm ▸ hk⟩
  have hpi : InjOn p Sq := by
    intro x hx y hy hxy
    have he : H ⟨x, hx⟩ = H ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hpval] using hxy
    exact congrArg Subtype.val (H.injective he)
  obtain ⟨hW, q, hq, hqval⟩ := exists_arm_parameter k
  have hcopy := hW
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hpW : FinitePiecewiseAffineOn p (arm k) := by
    rw [← hKs]
    exact hp.restrict K hK (hKs.subset.trans hsub)
  obtain ⟨j, hj, hjval⟩ := hpW.exists_homeomorph_image (hpi.mono hsub)
  have him : p '' arm k = range (fun t : I ↦ (H ⟨(t, k), t.property, hk⟩ : P2)) := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      refine ⟨⟨z.1, hz.1⟩, ?_⟩
      exact (hpval ⟨(z.1, k), hz.1, hk⟩).trans
        (congrArg p (show (z.1, k) = z from Prod.ext rfl hz.2.symm))
    · rintro x ⟨t, rfl⟩
      exact ⟨(t, k), ⟨t.property, rfl⟩, (hpval ⟨(t, k), t.property, hk⟩).symm⟩
  let Q := (q.trans j).trans (Homeomorph.setCongr him)
  refine ⟨Q, (hq.trans hj).setCongr rfl him, ?_⟩
  intro t
  change (j (q t) : P2) = H ⟨(t, k), t.property, hk⟩
  rw [hjval, hqval, hpval]

end PoincareConjecture.M76.Dehn

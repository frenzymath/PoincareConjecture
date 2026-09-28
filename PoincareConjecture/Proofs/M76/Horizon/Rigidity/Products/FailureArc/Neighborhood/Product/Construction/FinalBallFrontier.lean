import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FinalBallFromEndDisks



set_option autoImplicit false
open Set Metric Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductConstruction

local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : P2) 1
local notation "I" => Icc (0 : ℝ) 1

theorem final_ball_original_frontier_iff
    {X : Type*} [TopologicalSpace X] {R B D₀ D₁ : Set X}
    (hB : IsClosed B) (hBR : B ⊆ R)
    {k a : P2 × ℝ → X}
    (hi : InjOn k (Disk ×ˢ I)) (himage : k '' (Disk ×ˢ I) = B)
    (hann : EqOn k a (Rim ×ˢ I))
    (hbottom : k '' (Disk ×ˢ {(0 : ℝ)}) = D₀)
    (htop : ∀ p ∈ Disk ×ˢ I, k p ∈ D₁ ↔ p.2 = 1)
    (hside : ∀ p ∈ Disk ×ˢ I, k p ∈ a '' (Rim ×ˢ I) ↔ p.1 ∈ Rim)
    (hboundary : frontier B = a '' (Rim ×ˢ I) ∪ (D₀ ∪ D₁))
    (hold₀ : D₀ ⊆ frontier R) (hold₁ : D₁ ⊆ frontier R)
    (harim : ∀ z ∈ Rim, ∀ t ∈ I, a (z, t) ∈ frontier R ↔ t = 0 ∨ t = 1)
    {z : P2} (hz : z ∈ Disk) {t : ℝ} (ht : t ∈ I) :
    k (z, t) ∈ frontier R ↔ t = 0 ∨ t = 1 := by
  constructor
  · intro hx
    have hxB : k (z, t) ∈ B := himage.subset ⟨(z, t), ⟨hz, ht⟩, rfl⟩
    have hxfront : k (z, t) ∈ frontier B := by
      exact ⟨hB.closure_eq.symm ▸ hxB,
        fun h => hx.2 (interior_mono hBR h)⟩
    rcases hboundary.subset hxfront with ha | hd | hd
    · have hzr := (hside _ ⟨hz, ht⟩).mp ha
      exact (harim z hzr t ht).mp ((hann ⟨hzr, ht⟩) ▸ hx)
    · obtain ⟨⟨w, s⟩, ⟨hw, hs⟩, hws⟩ := hbottom.symm.subset hd
      have hs0 : s = 0 := hs
      subst s
      exact Or.inl (congrArg Prod.snd (hi ⟨hz, ht⟩ ⟨hw, by norm_num⟩ hws.symm))
    · exact Or.inr ((htop _ ⟨hz, ht⟩).mp hd)
  · rintro (rfl | rfl)
    · exact hold₀ (hbottom.subset ⟨(z, 0), ⟨hz, rfl⟩, rfl⟩)
    · exact hold₁ ((htop _ ⟨hz, ht⟩).mpr rfl)

end PoincareConjecture.M76.Dehn.Annuli.ProductConstruction

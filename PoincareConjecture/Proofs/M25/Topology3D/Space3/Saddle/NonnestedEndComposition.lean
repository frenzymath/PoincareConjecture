import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport











set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞






theorem image_trans_union_of_nonnested_exchanges
    (g h : D3) (R E₀ E₁ S₀ S₁ : Set E3)
    (hg₀ : g '' E₀ = S₀) (hgR : g '' R = R) (hg₁ : g '' E₁ = E₁)
    (hh₀ : h '' S₀ = S₀) (hhR : h '' R = R) (hh₁ : h '' E₁ = S₁) :
    (g.trans h) '' (R ∪ E₀ ∪ E₁) = R ∪ S₀ ∪ S₁ := by
  calc
    (g.trans h) '' (R ∪ E₀ ∪ E₁) = h '' (g '' (R ∪ E₀ ∪ E₁)) := by
      rw [Diffeomorph.coe_trans, Set.image_comp]
    _ = h '' (g '' R ∪ g '' E₀ ∪ g '' E₁) := by
      simp only [image_union]
    _ = h '' (R ∪ S₀ ∪ E₁) := by rw [hgR, hg₀, hg₁]
    _ = h '' R ∪ h '' S₀ ∪ h '' E₁ := by
      rw [image_union, image_union]
    _ = R ∪ S₀ ∪ S₁ := by rw [hhR, hh₀, hh₁]



theorem image_trans_symm_union_of_nonnested_exchanges
    (g h : D3) (R E₀ E₁ S₀ S₁ : Set E3)
    (hg₀ : g.symm '' S₀ = E₀) (hgR : g.symm '' R = R)
    (hg₁ : g.symm '' E₁ = E₁) (hh₀ : h.symm '' S₀ = S₀)
    (hhR : h.symm '' R = R) (hh₁ : h.symm '' S₁ = E₁) :
    (g.trans h).symm '' (R ∪ S₀ ∪ S₁) = R ∪ E₀ ∪ E₁ := by
  calc
    (g.trans h).symm '' (R ∪ S₀ ∪ S₁) = g.symm '' (h.symm '' (R ∪ S₀ ∪ S₁)) := by
      rw [Diffeomorph.symm_trans', Diffeomorph.coe_trans, Set.image_comp]
    _ = g.symm '' (h.symm '' R ∪ h.symm '' S₀ ∪ h.symm '' S₁) := by
      simp only [image_union]
    _ = g.symm '' (R ∪ S₀ ∪ E₁) := by rw [hhR, hh₀, hh₁]
    _ = g.symm '' R ∪ g.symm '' S₀ ∪ g.symm '' E₁ := by
      rw [image_union, image_union]
    _ = R ∪ E₀ ∪ E₁ := by rw [hgR, hg₀, hg₁]

end PoincareConjecture.M25.Topology3D

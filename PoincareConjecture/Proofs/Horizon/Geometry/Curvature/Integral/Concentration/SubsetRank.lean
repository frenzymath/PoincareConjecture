import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Packing.LocalRank


open Set
namespace Poincare.Alexandrov
noncomputable def minLocalAnglePackingRankOn {X : Type*} [MetricSpace X]
    (θ : ℝ) (K : Set X) : ℕ :=
  sInf (localAnglePackingRank θ '' K)

theorem minLocalAnglePackingRankOn_spec
    {X : Type*} [MetricSpace X] {θ : ℝ} {K : Set X} {N : ℕ}
    (hK : K.Nonempty) (hpack : ComparisonAnglePackingBound X θ N) :
    (∃ p ∈ K, localAnglePackingRank θ p = minLocalAnglePackingRankOn θ K) ∧
      (∀ p ∈ K, minLocalAnglePackingRankOn θ K ≤ localAnglePackingRank θ p) ∧
      minLocalAnglePackingRankOn θ K ≤ N := by
  have hattain := Nat.sInf_mem (hK.image (localAnglePackingRank θ))
  obtain ⟨p,hp,heq⟩ := hattain
  refine ⟨⟨p,hp,heq⟩, ?_, ?_⟩
  · intro q hq
    exact Nat.sInf_le (Set.mem_image_of_mem _ hq)
  · change sInf (localAnglePackingRank θ '' K) ≤ N
    rw [← heq]
    exact (localAnglePackingRank_spec hpack p).2.1

theorem minLocalAnglePackingRankOn_univ
    {X : Type*} [MetricSpace X] (θ : ℝ) :
    minLocalAnglePackingRankOn θ (univ : Set X) = minLocalAnglePackingRank X θ := by
  simp only [minLocalAnglePackingRankOn, minLocalAnglePackingRank, Set.image_univ]

theorem minLocalAnglePackingRankOn_antitone
    {X : Type*} [MetricSpace X] {θ : ℝ} {K L : Set X}
    (hK : K.Nonempty) (hKL : K ⊆ L) :
    minLocalAnglePackingRankOn θ L ≤ minLocalAnglePackingRankOn θ K := by
  obtain ⟨p,hp,heq⟩ := Nat.sInf_mem (hK.image (localAnglePackingRank θ))
  change sInf (localAnglePackingRank θ '' L) ≤ sInf (localAnglePackingRank θ '' K)
  rw [← heq]
  exact Nat.sInf_le (Set.mem_image_of_mem _ (hKL hp))

theorem lt_minLocalAnglePackingRankOn_of_pointwise_growth
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {θ : ℝ}
    {K : Set X} {L : Set Y} {p : X} {NX NY : ℕ}
    (hp : p ∈ K) (hL : L.Nonempty)
    (hpackX : ComparisonAnglePackingBound X θ NX)
    (hpackY : ComparisonAnglePackingBound Y θ NY)
    (hgrowth : ∀ k : ℕ, HasSmallAngleConfiguration θ p k →
      ∀ y ∈ L, HasSmallAngleConfiguration θ y (k+1)) :
    minLocalAnglePackingRankOn θ K < minLocalAnglePackingRankOn θ L := by
  have hK : K.Nonempty := ⟨p,hp⟩
  have hold := (localAnglePackingRank_spec hpackX p).1.mono
    ((minLocalAnglePackingRankOn_spec hK hpackX).2.1 p hp)
  obtain ⟨y,hy,hrank⟩ := (minLocalAnglePackingRankOn_spec hL hpackY).1
  have hs := hgrowth _ hold y hy
  have hb := (localAnglePackingRank_spec hpackY y).2.2 _ |>.mp hs
  omega
end Poincare.Alexandrov

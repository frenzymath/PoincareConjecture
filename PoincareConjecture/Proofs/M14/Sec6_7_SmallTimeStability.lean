import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeDifferential
import PoincareConjecture.Proofs.M14.Sec6_7_BackwardStable











set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}




theorem smallTime_stability_of_open_uniqueMinimizing
    (E : M14ExponentialFamily G T x)
    {B : Set (G.Horizontal x)} (hB : IsCompact B) {K : Set G.Point}
    (hK : ∃ O : Set G.Point, IsOpen O ∧ x ∈ O ∧ O ⊆ K)
    {δ : ℝ} (hδ : 0 < δ) (hwindow : Icc (T - δ) T ⊆ I.domain)
    {N : Set (G.Horizontal x)} (hN : IsOpen N) (hBN : B ⊆ N)
    {η : ℝ} (hη : 0 < η) (hηδ : η ≤ δ)
    (hunique : ∀ Z ∈ N, ∀ τ ∈ Ioc 0 η, M14UniqueMinimizingBranch G T τ x E Z) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ δ ∧
      ∀ τ, 0 < τ → τ < τ₀ →
        ∃ H : M14StableSet G T τ x E, B ⊆ H.carrier ∧
          ∀ Z ∈ B, ∀ s ∈ Icc 0 τ, E.gamma Z (Real.sqrt s) ∈ K := by
  obtain ⟨τD, hτD, _, hdifferential⟩ :=
    compact_initial_smallTime_differential_bijective E hB hδ hwindow
  obtain ⟨τK, hτK, _, hcapture⟩ := compact_initial_survival_and_capture E hB hK hδ hwindow
  let τ₀ := min η (min τD τK)
  have hτ₀ : 0 < τ₀ := lt_min hη (lt_min hτD hτK)
  have hτ₀δ : τ₀ ≤ δ := (min_le_left _ _).trans hηδ
  refine ⟨τ₀, hτ₀, hτ₀δ, ?_⟩
  intro τ hτ hτsmall
  have hτη : τ ≤ η := hτsmall.le.trans (min_le_left _ _)
  have hτD' : τ ≤ τD :=
    hτsmall.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτK' : τ ≤ τK :=
    hτsmall.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨H⟩ := stableSet_nonempty_of_allowed E hτ
    (hwindow ⟨sub_le_sub_left (hτsmall.le.trans hτ₀δ) T, sub_le_self T hτ.le⟩)
  refine ⟨H, ?_, ?_⟩
  · intro Z hZ
    obtain ⟨hs, hbij⟩ := hdifferential Z hZ τ ⟨hτ, hτD'⟩
    exact (H.carrier_exact Z).mpr
      ⟨hs, hbij, N, hN, hBN hZ, fun W hW => hunique W hW τ ⟨hτ, hτη⟩⟩
  · intro Z hZ s hs
    exact (hcapture Z hZ s ⟨hs.1, hs.2.trans hτK'⟩).2

end PoincareConjecture.M14

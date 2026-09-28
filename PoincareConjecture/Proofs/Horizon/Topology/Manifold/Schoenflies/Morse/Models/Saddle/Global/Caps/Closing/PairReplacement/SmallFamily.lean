import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.PairReplacement.Canonical

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_supported_small_cap_family_replacement_of_canonical_normalizations
    {ι : Type*} [Finite ι] (hcard : Nat.card ι = 1 ∨ Nat.card ι = 2)
    {v : E3} (hv : ‖v‖ = 1) (b : Real)
    (A : ι → (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (E M : ι → Set E3)
    (hEdis : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hMdis : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hEheight : ∀ i, ∀ y ∈ E i, inner Real v y ≤ b)
    (hMheight : ∀ i, ∀ y ∈ M i, inner Real v y ≤ b)
    (a s : ι → Real) (ha : ∀ i, a i < b) (hs : ∀ i, s i < 0)
    (N P : ι → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (η : ι → Real) (hη : ∀ i, 0 < η i)
    (hN : ∀ i, EqOn (N i) Q {y | b - η i ≤ inner Real v y})
    (hP : ∀ i, EqOn (P i) Q {y | b - η i ≤ inner Real v y})
    (hNc : ∀ i, ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, N i y = y)
    (hPc : ∀ i, ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, P i y = y)
    (hNE : ∀ i, N i '' E i =
      liftPlaneDiffeomorph hv (a i) (s i) (hs i).ne (A i) '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A i '' sphere (0 : Hemisphere.Plane v) 1) (a i) b)
    (hPM : ∀ i, P i '' M i =
      liftPlaneDiffeomorph hv (a i) (s i) (hs i).ne (A i) '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A i '' sphere (0 : Hemisphere.Plane v) 1) (a i) b)
    {C : Set E3} (hC : IsClosed C) (hCheight : ∀ y ∈ C, b ≤ inner Real v y)
    (havoid : ∀ i, (∀ j, j ≠ i →
      Disjoint (A i '' closedBall (0 : Hemisphere.Plane v) 1) (A j '' closedBall 0 1) ∨
        A i '' closedBall (0 : Hemisphere.Plane v) 1 ⊆ A j '' ball 0 1) →
      ∃ R : Real, 0 < R ∧ ∀ y ∈ C, inner Real v y ≤ b + 2 * R →
        (Hemisphere.Plane v).orthogonalProjectionOnto (Q y) ∉ A i '' ball 0 1) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, G y = y) ∧ EqOn G id C ∧ ∀ i, G '' E i = M i := by
  classical
  rcases hcard with hone | htwo
  · obtain ⟨i, hi⟩ := Nat.card_eq_one_iff_exists.mp hone
    obtain ⟨KN, hKN, hNfix⟩ := hNc i
    obtain ⟨KP, hKP, hPfix⟩ := hPc i
    refine ⟨KN ∪ KP, hKN.union hKP, (N i).trans (P i).symm, ?_, ?_, ?_⟩
    · intro y hy
      change (P i).symm (N i y) = y
      rw [hNfix y (fun h => hy (Or.inl h))]
      apply (P i).injective
      change P i ((P i).symm y) = P i y
      rw [(P i).apply_symm_apply, hPfix y (fun h => hy (Or.inr h))]
    · intro y hy
      change (P i).symm (N i y) = y
      have hh : b - η i ≤ inner Real v y := by linarith [hCheight y hy, hη i]
      rw [hN i hh, ← hP i hh, (P i).symm_apply_apply]
    · intro j
      rw [hi j]
      change ((P i).symm ∘ N i) '' E i = M i
      rw [image_comp, hNE, ← hPM, image_image]
      simp only [Diffeomorph.symm_apply_apply, image_id']
  · let := Fintype.ofFinite ι
    let σ : Fin 2 ≃ ι := (Fintype.equivFinOfCardEq
      (by simpa only [← Nat.card_eq_fintype_card] using htwo)).symm
    let ε := min (η (σ 0)) (η (σ 1))
    have hε : 0 < ε := lt_min (hη _) (hη _)
    have hεle (j : Fin 2) : ε ≤ η (σ j) := by
      fin_cases j
      · exact min_le_left _ _
      · exact min_le_right _ _
    obtain ⟨K, hK, G, hGoff, hGC, hGcap⟩ :=
      exists_supported_cap_pair_replacement_of_canonical_normalizations hv b (A ∘ σ)
        (E ∘ σ) (M ∘ σ)
        (fun _ _ hij => hEdis (fun heq => hij (σ.injective heq)))
        (fun _ _ hij => hMdis (fun heq => hij (σ.injective heq)))
        (fun j => hEheight (σ j)) (fun j => hMheight (σ j))
        (a ∘ σ) (a ∘ σ) (s ∘ σ) (s ∘ σ)
        (fun j => ha (σ j)) (fun j => ha (σ j))
        (fun j => hs (σ j)) (fun j => hs (σ j))
        (N ∘ σ) (P ∘ σ) Q hQ hε
        (fun j y hy => hN (σ j) (by change b - ε ≤ inner Real v y at hy; change b - η (σ j) ≤ inner Real v y; linarith [hεle j]))
        (fun j y hy => hP (σ j) (by change b - ε ≤ inner Real v y at hy; change b - η (σ j) ≤ inner Real v y; linarith [hεle j]))
        (fun j => hNc (σ j)) (fun j => hPc (σ j))
        (fun j => hNE (σ j)) (fun j => hPM (σ j)) hC hCheight
        (by
          intro j hj
          apply havoid (σ j)
          intro k hk
          have hne : σ.symm k ≠ j := fun heq => hk (by rw [← σ.apply_symm_apply k, heq])
          simpa only [comp_apply, σ.apply_symm_apply] using hj (σ.symm k) hne)
    refine ⟨K, hK, G, hGoff, hGC, fun i => ?_⟩
    simpa only [comp_apply, σ.apply_symm_apply] using hGcap (σ.symm i)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

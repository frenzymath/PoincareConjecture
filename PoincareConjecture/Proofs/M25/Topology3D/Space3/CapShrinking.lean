import PoincareConjecture.Proofs.M25.Topology3D.Space3.CapPreservation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothFlow

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem exists_cap_shrinking_isotopy (u : E) (hu : ‖u‖ = 1)
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    {U : Set E} (hU : IsOpen U) (hballU : closedBall (0 : E) 1 ⊆ U) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ t : ℝ, 0 ≤ t → MapsTo (Φ t) (closedBall 0 1) (closedBall 0 1)) ∧
      (∀ t : ℝ, 0 ≤ t → MapsTo (Φ t)
        {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ} {x | ‖x‖ = 1 ∧ a ≤ ⟪u, x⟫_ℝ}) ∧
      (∀ eps : ℝ, 0 < eps → ∃ T : ℝ, 0 ≤ T ∧
        ∀ t : ℝ, T ≤ t → MapsTo (Φ t) (closedBall 0 1) (ball u eps)) ∧
      ∃ C : Set E, IsCompact C ∧ C ⊆ U ∧ ∀ t x, x ∉ C → Φ t x = x := by
  obtain ⟨χ, hχ, hrange, hzero, hone⟩ := exists_capContraction_cutoff a ha.1
  obtain ⟨W, hW, hWs, hsupp, hnear⟩ := exists_compactField_extension
    (isCompact_closedBall (0 : E) 1) hU hballU (capContractionField χ u)
    (capContractionField_contDiff χ hχ u).contDiffOn
  have hag : EqOn W (capContractionField χ u) (closedBall 0 1) := by
    intro x hx
    exact (eventually_nhdsSet_iff_forall.mp hnear x hx).self_of_nhds
  obtain ⟨k, l, hk, hl⟩ := compactField_bounds W hW hWs
  let Φ := fun t => boundedFlowDiffeomorph W hk hl hW hWs t
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_, tsupport W, hWs.isCompact, hsupp, ?_⟩
  · exact (boundedFlow_contDiff W hk hl hW hWs).comp
      (contDiff_snd.prodMk contDiff_fst)
  · intro x
    exact boundedFlow_zero W hk hl x
  · intro t ht
    exact capFlow_mapsTo_closedBall χ hrange hzero u hu W hk hl hag t ht
  · intro t ht
    exact capFlow_mapsTo_cap χ hrange hzero u hu W hk hl hag a (by linarith [ha.1]) hone t ht
  · intro eps heps
    exact capFlow_eventually_mapsTo_ball χ hrange hzero u hu W hk hl hag eps heps
  · intro t x hx
    exact boundedFlow_eq_self W hk hl x (image_eq_zero_of_notMem_tsupport hx) t

end PoincareConjecture.M25.Topology3D

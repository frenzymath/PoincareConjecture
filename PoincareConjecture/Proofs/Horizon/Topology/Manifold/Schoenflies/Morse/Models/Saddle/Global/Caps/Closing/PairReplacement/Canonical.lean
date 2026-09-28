import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.PairReplacement.CanonicalBalls
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.CurvedCapFamily
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.RelativeAlignment

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

theorem exists_supported_cap_pair_replacement_of_canonical_normalizations
    {v : E3} (hv : ‖v‖ = 1) (b : Real)
    (A : Fin 2 → (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (E M : Fin 2 → Set E3)
    (hEdis : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hMdis : Pairwise (fun i j => Disjoint (M i) (M j)))
    (hEheight : ∀ i, ∀ y ∈ E i, inner Real v y ≤ b)
    (hMheight : ∀ i, ∀ y ∈ M i, inner Real v y ≤ b)
    (a d s t : Fin 2 → Real) (ha : ∀ i, a i < b) (hd : ∀ i, d i < b)
    (hs : ∀ i, s i < 0) (ht : ∀ i, t i < 0)
    (N P : Fin 2 → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    {η : Real} (hη : 0 < η)
    (hN : ∀ i, EqOn (N i) Q {y | b - η ≤ inner Real v y})
    (hP : ∀ i, EqOn (P i) Q {y | b - η ≤ inner Real v y})
    (hNc : ∀ i, ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, N i y = y)
    (hPc : ∀ i, ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, P i y = y)
    (hNE : ∀ i, N i '' E i =
      liftPlaneDiffeomorph hv (a i) (s i) (hs i).ne (A i) '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A i '' sphere (0 : Hemisphere.Plane v) 1) (a i) b)
    (hPM : ∀ i, P i '' M i =
      liftPlaneDiffeomorph hv (d i) (t i) (ht i).ne (A i) '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A i '' sphere (0 : Hemisphere.Plane v) 1) (d i) b)
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
  let J : E2 ≃ₗᵢ[Real] Hemisphere.Plane v :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by intro hz; simp [hz] at hv)).repr.symm
  let γ (i : Fin 2) : S1 → Hemisphere.Plane v := fun q => A i (J q)
  have hγ (i : Fin 2) :
      _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ (γ i) := by
    let D := J.toContinuousLinearEquiv.toDiffeomorph.trans (A i)
    have hc := contMDiff_coe_sphere (n := 1) (m := ∞) (E := E2)
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (D.contMDiff.comp hc) (D.injective.comp Subtype.val_injective)
    intro q
    change Injective (mfderiv (𝓡 1) 𝓘(Real, Hemisphere.Plane v)
      (D ∘ (fun q : S1 => (q : E2))) q)
    rw [mfderiv_comp q (D.contMDiff.mdifferentiable (by simp) _)
      (hc.mdifferentiable (by simp) q)]
    exact (D.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (by convert! injective_mvfderiv_subtypeVal_sphere q)
  have hA (i : Fin 2) : A i '' sphere (0 : Hemisphere.Plane v) 1 = range (γ i) := by
    change A i '' sphere (0 : Hemisphere.Plane v) 1 =
      range (A i ∘ J ∘ (fun q : S1 => (q : E2)))
    rw [range_comp, range_comp, Subtype.range_coe_subtype, ofPred_mem_eq,
      J.image_sphere, map_zero]
  have hNhalf (i : Fin 2) : EqOn (N i) Q {y | b ≤ inner Real v y} := by
    intro y hy
    exact hN i (by change b - η ≤ inner Real v y; change b ≤ inner Real v y at hy; linarith)
  have hPhalf (i : Fin 2) : EqOn (P i) Q {y | b ≤ inner Real v y} := by
    intro y hy
    exact hP i (by change b - η ≤ inner Real v y; change b ≤ inner Real v y at hy; linarith)
  have hrim (i : Fin 2) (z : Hemisphere.Plane v) (hz : z ∈ A i '' sphere 0 1) :
      Q.symm (b • v + (z : E3)) ∈ E i := by
    have hp : b • v + (z : E3) ∈ N i '' E i := by
      rw [hNE i]
      apply Or.inr
      rw [terminalCylinder_eq_height_product]
      exact ⟨(b, z), ⟨⟨(ha i).le, le_rfl⟩, hz⟩, rfl⟩
    obtain ⟨x, hx, heq⟩ := hp
    have hh : inner Real v (Q.symm (b • v + (z : E3))) = b := by
      rw [← hQ (Q.symm _), Q.apply_symm_apply]
      exact inner_heightCoordinates hv (b, z)
    have hn : N i (Q.symm (b • v + (z : E3))) = b • v + (z : E3) := by
      rw [hNhalf i hh.ge, Q.apply_symm_apply]
    exact (N i).injective (heq.trans hn.symm) ▸ hx
  have hcircles : Pairwise (fun i j => Disjoint
      (A i '' sphere (0 : Hemisphere.Plane v) 1) (A j '' sphere 0 1)) := by
    intro i j hij
    exact disjoint_left.mpr (fun z hi hj => disjoint_left.mp (hEdis hij) (hrim i z hi) (hrim j z hj))
  obtain ⟨σ, horder⟩ := exists_ordered_planar_cap_pair hv A (hcircles (by decide : (0 : Fin 2) ≠ 1))
  have hminimal : ∀ j, j ≠ σ 1 →
      Disjoint (A (σ 1) '' closedBall (0 : Hemisphere.Plane v) 1) (A j '' closedBall 0 1) ∨
        A (σ 1) '' closedBall (0 : Hemisphere.Plane v) 1 ⊆ A j '' ball 0 1 := by
    intro j hj
    obtain ⟨k, rfl⟩ := σ.surjective j
    fin_cases k
    · exact horder.elim Or.inr Or.inl
    · exact (hj rfl).elim
  obtain ⟨R, hR, hinneravoid⟩ := havoid (σ 1) hminimal
  obtain ⟨w, hw, hwR, hscale, _⟩ := exists_disjoint_curved_closing_cap_family hv b A hcircles hR
  have hσ : σ 0 ≠ σ 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (σ.injective h)
  obtain ⟨B, hB, hBposition⟩ := exists_ordered_canonical_closing_balls hv (A ∘ σ) b (w ∘ σ)
    (fun i => hw (σ i)) horder (hscale (σ 1) (σ 0)) (E ∘ σ) (hEdis hσ)
    (fun i => hEheight (σ i)) (a ∘ σ) (s ∘ σ) (fun i => ha (σ i)) (fun i => hs (σ i))
    (N ∘ σ) Q hQ hη (fun i => hN (σ i)) (fun i => hNE (σ i))
  obtain ⟨L, hL, hLposition⟩ := exists_ordered_canonical_closing_balls hv (A ∘ σ) b (w ∘ σ)
    (fun i => hw (σ i)) horder (hscale (σ 1) (σ 0)) (M ∘ σ) (hMdis hσ)
    (fun i => hMheight (σ i)) (d ∘ σ) (t ∘ σ) (fun i => hd (σ i)) (fun i => ht (σ i))
    (P ∘ σ) Q hQ hη (fun i => hP (σ i)) (fun i => hPM (σ i))
  have hex (i : Fin 2) := exists_buffered_relative_cap_alignment_of_compatible_normalizations
    hv (γ i) (hγ i) (A i) (A i) (hA i) (hA i) (ha i) (hd i) (hs i) (ht i)
    (N i) (P i) (hNc i) (hPc i) hη
    (fun y hy => (hN i hy).trans (hP i hy).symm)
    (fun y hy => by rw [hN i hy, hQ])
    (by simpa only [hA i] using hNE i) (by simpa only [hA i] using hPM i)
  choose K hK F hFoff hbuffer hFcap using hex
  choose ε hε hFfix using hbuffer
  let ε₀ := min (ε (σ 0)) (ε (σ 1))
  have hε₀ : 0 < ε₀ := lt_min (hε _) (hε _)
  have hεle (i : Fin 2) : ε₀ ≤ ε (σ i) := by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hFcommon (i : Fin 2) : EqOn (F (σ i)) id {y | b - ε₀ ≤ inner Real v y} := by
    intro y hy
    apply hFfix (σ i)
    change b - ε (σ i) ≤ inner Real v y
    change b - ε₀ ≤ inner Real v y at hy
    linarith [hεle i]
  have hBC : (B 1 '' closedBall (0 : E3) 1) ∩ C ⊆ Q.symm ''
      (liftPlaneDiffeomorph hv b (w (σ 1)) (hw (σ 1)).ne' (A (σ 1)) '' boundedCylinderNorthernCap v) := by
    apply normalized_curved_closing_ball_inter_band hv (A (σ 1)) (ha _) (hs _) (hw _)
      (B 1) (N (σ 1)) Q hQ (hNhalf _) (hEheight _) (hNE _) (hB 1) hCheight
    intro y hy hheight
    exact hinneravoid y hy (by linarith [hwR (σ 1)])
  have hLC : (L 1 '' closedBall (0 : E3) 1) ∩ C ⊆ Q.symm ''
      (liftPlaneDiffeomorph hv b (w (σ 1)) (hw (σ 1)).ne' (A (σ 1)) '' boundedCylinderNorthernCap v) := by
    apply normalized_curved_closing_ball_inter_band hv (A (σ 1)) (hd _) (ht _) (hw _)
      (L 1) (P (σ 1)) Q hQ (hPhalf _) (hMheight _) (hPM _) (hL 1) hCheight
    intro y hy hheight
    exact hinneravoid y hy (by linarith [hwR (σ 1)])
  obtain ⟨J, hJ, G, hGoff, hGC, hGcap⟩ :=
    exists_simultaneous_curved_lower_cap_pair_replacement hv (A ∘ σ) b (w ∘ σ)
      (fun i => hw (σ i)) Q hQ (E ∘ σ) (M ∘ σ) B L (F ∘ σ) hB hL
      (fun i => hFcap (σ i)) ⟨K (σ 0), hK _, hFoff _⟩ hε₀ hFcommon hBposition hLposition
      (hEheight _) (hMheight _) ![a (σ 1), d (σ 1)] ![s (σ 1), t (σ 1)]
      (by intro j; fin_cases j; exact ha _; exact hd _)
      (by intro j; fin_cases j; exact hs _; exact ht _)
      ![N (σ 1), P (σ 1)] hη
      (by intro j; fin_cases j; exact hN _; exact hP _)
      (hNE _) (hPM _) hC hCheight hBC hLC
  refine ⟨J, hJ, G, hGoff, hGC, fun i => ?_⟩
  simpa only [Function.comp_apply, σ.apply_symm_apply] using hGcap (σ.symm i)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

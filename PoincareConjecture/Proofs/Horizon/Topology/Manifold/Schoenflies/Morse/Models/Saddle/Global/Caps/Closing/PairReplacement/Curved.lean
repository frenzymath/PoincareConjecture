import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.PairReplacement.Dynamic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.ClosingDisk
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Belt

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem closing_rim_subset_of_canonical_cylinder
    {v : E3} (hv : ‖v‖ = 1)
    (A : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    {a b w η : Real} (hab : a < b) (hw : 0 < w) (hη : 0 < η)
    (N Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (hN : EqOn N Q {y | b - η ≤ inner Real v y}) {E : Set E3}
    (hcyl : terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) a b ⊆ N '' E) :
    (Q.symm '' (liftPlaneDiffeomorph hv b w hw.ne' A '' boundedCylinderNorthernCap v)) ∩
      {y | inner Real v y = b} ⊆ E := by
  rintro y ⟨⟨z, hz, rfl⟩, hh⟩
  have hzh : inner Real v z = b := by rw [← Q.apply_symm_apply z, hQ]; exact hh
  have hrim : z ∈ (fun x : Hemisphere.Plane v => b • v + (A x : E3)) '' sphere 0 1 := by
    have heq := lifted_cap_slice_eq_circle hv b w hw.ne' A
      (show (0 : Real) ∈ Ico 0 1 by constructor <;> norm_num)
    simp only [mul_zero, add_zero] at heq
    rw [← heq]
    exact ⟨hz, hzh⟩
  have hzN : z ∈ N '' E := by
    apply hcyl
    rw [terminalCylinder_eq_height_product]
    obtain ⟨q, hq, rfl⟩ := hrim
    exact ⟨(b, A q), ⟨⟨hab.le, le_rfl⟩, mem_image_of_mem A hq⟩, rfl⟩
  obtain ⟨x, hx, heq⟩ := hzN
  have hn : N (Q.symm z) = z := by
    rw [hN (by change b - η ≤ inner Real v (Q.symm z); rw [hh]; linarith), Q.apply_symm_apply]
  exact N.injective (heq.trans hn.symm) ▸ hx

private theorem complementary_cap_sdiff
    {v : E3} {b : Real} {E Δ D S : Set E3}
    (hS : S = E ∪ Δ) (hD : D = Δ \ {y | inner Real v y = b})
    (hE : ∀ y ∈ E, inner Real v y ≤ b)
    (hΔ : ∀ y ∈ Δ, b ≤ inner Real v y)
    (hrim : Δ ∩ {y | inner Real v y = b} ⊆ E) : S \ D = E := by
  rw [hS, hD]
  apply Subset.antisymm
  · rintro y ⟨hyE | hyΔ, hyD⟩
    · exact hyE
    · exact hrim ⟨hyΔ, by by_contra h; exact hyD ⟨hyΔ, h⟩⟩
  · intro y hy
    exact ⟨Or.inl hy, fun hh => hh.2 (le_antisymm (hE y hy) (hΔ y hh.1))⟩

theorem exists_simultaneous_curved_lower_cap_pair_replacement
    {v : E3} (hv : ‖v‖ = 1)
    (A : Fin 2 → (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (b : Real) (w : Fin 2 → Real) (hw : ∀ i, 0 < w i)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real v (Q y) = inner Real v y)
    (E M : Fin 2 → Set E3)
    (B L F : Fin 2 → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : ∀ i, B i '' sphere (0 : E3) 1 = E i ∪
      Q.symm '' (liftPlaneDiffeomorph hv b (w i) (hw i).ne' (A i) '' boundedCylinderNorthernCap v))
    (hL : ∀ i, L i '' sphere (0 : E3) 1 = M i ∪
      Q.symm '' (liftPlaneDiffeomorph hv b (w i) (hw i).ne' (A i) '' boundedCylinderNorthernCap v))
    (hFcap : ∀ i, F i '' E i = M i)
    (hFcompact : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, F 0 y = y)
    {ε : Real} (hε : 0 < ε)
    (hFfix : ∀ i, EqOn (F i) id {y | b - ε ≤ inner Real v y})
    (hsource : B 1 '' closedBall (0 : E3) 1 ⊆ B 0 '' ball (0 : E3) 1 ∨
      Disjoint (B 1 '' closedBall (0 : E3) 1) (B 0 '' closedBall (0 : E3) 1))
    (htarget : L 1 '' closedBall (0 : E3) 1 ⊆ L 0 '' ball (0 : E3) 1 ∨
      Disjoint (L 1 '' closedBall (0 : E3) 1) (L 0 '' closedBall (0 : E3) 1))
    (hEheight : ∀ y ∈ E 1, inner Real v y ≤ b)
    (hMheight : ∀ y ∈ M 1, inner Real v y ≤ b)
    (a s : Fin 2 → Real) (ha : ∀ j, a j < b) (hs : ∀ j, s j < 0)
    (N : Fin 2 → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {η : Real} (hη : 0 < η)
    (hN : ∀ j, EqOn (N j) Q {y | b - η ≤ inner Real v y})
    (hNE : N 0 '' E 1 =
      liftPlaneDiffeomorph hv (a 0) (s 0) (hs 0).ne (A 1) '' boundedCylinderNorthernCap v ∪
      terminalCylinder (A 1 '' sphere (0 : Hemisphere.Plane v) 1) (a 0) b)
    (hNM : N 1 '' M 1 =
      liftPlaneDiffeomorph hv (a 1) (s 1) (hs 1).ne (A 1) '' boundedCylinderNorthernCap v ∪
      terminalCylinder (A 1 '' sphere (0 : Hemisphere.Plane v) 1) (a 1) b)
    {C : Set E3} (hC : IsClosed C) (hCheight : ∀ y ∈ C, b ≤ inner Real v y)
    (hBC : (B 1 '' closedBall (0 : E3) 1) ∩ C ⊆
      Q.symm '' (liftPlaneDiffeomorph hv b (w 1) (hw 1).ne' (A 1) '' boundedCylinderNorthernCap v))
    (hLC : (L 1 '' closedBall (0 : E3) 1) ∩ C ⊆
      Q.symm '' (liftPlaneDiffeomorph hv b (w 1) (hw 1).ne' (A 1) '' boundedCylinderNorthernCap v)) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, G y = y) ∧ EqOn G id C ∧ ∀ i, G '' E i = M i := by
  let Δ (i : Fin 2) := Q.symm ''
    (liftPlaneDiffeomorph hv b (w i) (hw i).ne' (A i) '' boundedCylinderNorthernCap v)
  have hΔheight (i : Fin 2) : ∀ y ∈ Δ i, b ≤ inner Real v y := by
    rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    have hQi (z : E3) : inner Real v (Q.symm z) = inner Real v z := by
      rw [← hQ (Q.symm z), Q.apply_symm_apply]
    rw [hQi, inner_liftPlaneDiffeomorph]
    exact le_add_of_nonneg_right (mul_nonneg (hw i).le
      (height_nonneg_of_mem_boundedCylinderNorthernCap hx))
  have hFΔ (i : Fin 2) : EqOn (F i) id (Δ i) := by
    intro y hy
    exact hFfix i (by change b - ε ≤ inner Real v y; linarith [hΔheight i y hy])
  have hFball (i : Fin 2) : F i '' (B i '' closedBall (0 : E3) 1) = L i '' closedBall (0 : E3) 1 :=
    (image_closing_ball_of_cap_image (F i) (B i) (L i) (hB i) (hL i) (hFcap i) (hFΔ i)).1
  let E' : Fin 2 → Set E3 := ![E 1, M 1]
  let B' : Fin 2 → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := ![B 1, L 1]
  have hNimages (j : Fin 2) : N j '' E' j =
      liftPlaneDiffeomorph hv (a j) (s j) (hs j).ne (A 1) '' boundedCylinderNorthernCap v ∪
        terminalCylinder (A 1 '' sphere (0 : Hemisphere.Plane v) 1) (a j) b := by
    fin_cases j
    · exact hNE
    · exact hNM
  have hboundaries (j : Fin 2) : B' j '' sphere (0 : E3) 1 = E' j ∪ Δ 1 := by
    fin_cases j
    · exact hB 1
    · exact hL 1
  obtain ⟨g, r, hg, hgi, hgd, hr, hgclosed, hgopen, hmarks⟩ :=
    exists_common_enlarged_curved_closing_disk hv (A 1) (hw 1) hη a s ha hs N Q hQ hN
      E' hNimages B' hboundaries
  have hunitU : g '' closedBall (0 : E2) 1 ⊆ {y | b - ε < inner Real v y} := by
    rw [hgclosed]
    intro y hy
    change b - ε < inner Real v y
    linarith [hΔheight 1 y hy]
  have hErim : Δ 1 ∩ {y | inner Real v y = b} ⊆ E 1 :=
    closing_rim_subset_of_canonical_cylinder hv (A 1) (ha 0) (hw 1) hη (N 0) Q hQ (hN 0)
      (by rw [hNE]; exact subset_union_right)
  have hMrim : Δ 1 ∩ {y | inner Real v y = b} ⊆ M 1 :=
    closing_rim_subset_of_canonical_cylinder hv (A 1) (ha 1) (hw 1) hη (N 1) Q hQ (hN 1)
      (by rw [hNM]; exact subset_union_right)
  have hEcompl : (B 1 '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) = E 1 :=
    complementary_cap_sdiff (hB 1) hgopen hEheight (hΔheight 1) hErim
  have hMcompl : (L 1 '' sphere (0 : E3) 1) \ (g '' ball (0 : E2) 1) = M 1 :=
    complementary_cap_sdiff (hL 1) hgopen hMheight (hΔheight 1) hMrim
  obtain ⟨K, G, _, _, _, hGid, _, hGcap, ⟨J, hJ, hJfix⟩, hGC, _⟩ :=
    exists_supported_moving_pair_replacement (B 0) (B 1) (L 0) (L 1) (F 0) (F 1)
      (hFball 0) (hFball 1) hFcompact
      (isOpen_lt continuous_const (continuous_const.inner continuous_id)) hC
      (fun y hy => by change b - ε < inner Real v y; linarith [hCheight y hy])
      (fun y hy => hFfix 0 (le_of_lt hy)) (fun y hy => hFfix 1 (le_of_lt hy))
      hsource htarget g hg hgi hgd hr (hmarks 0) (hmarks 1) hunitU
      (by rw [hgclosed]; exact hBC) (by rw [hgclosed]; exact hLC)
  refine ⟨J, hJ, (F 0).trans G, hJfix, hGC, ?_⟩
  intro i
  fin_cases i
  · change (G ∘ F 0) '' E 0 = M 0
    rw [image_comp, hFcap 0]
    have hfix : EqOn G id (M 0) := by
      intro y hy
      apply hGid
      exact Or.inl (Or.inr ((hL 0).symm ▸ Or.inl hy))
    rw [image_congr hfix, image_id]
  · change (G ∘ F 0) '' E 1 = M 1
    rw [image_comp]
    simpa only [hEcompl, hMcompl] using hGcap

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

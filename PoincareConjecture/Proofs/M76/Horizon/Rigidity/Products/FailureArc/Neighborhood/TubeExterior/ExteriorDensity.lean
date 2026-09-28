import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Geometry
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

private theorem exists_lateral_exterior_box {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {z : C3} (hz : z ∈ lateral r) :
    ∃ B bd : Set C3, IsFinitePLBallPair C3 B bd ∧ z ∈ B ∧ B ⊆ tube ∧
      Disjoint B (openTube r) := by
  have hclosed := lateral_subset r hz
  have hbounds := closedTube_subset hr1.le hclosed
  have hnot : ¬ (-r < z.1.1 ∧ z.1.1 < r ∧ -r < z.1.2 ∧ z.1.2 < r) := by
    intro h
    apply hz.1.2
    simpa only [transverseSquare, interior_prod_eq, interior_Icc, mem_prod, mem_Ioo] using
      (show (-r < z.1.1 ∧ z.1.1 < r) ∧ (-r < z.1.2 ∧ z.1.2 < r) from
        ⟨⟨h.1, h.2.1⟩, h.2.2⟩)
  have hsides : z.1.1 ≤ -r ∨ r ≤ z.1.1 ∨ z.1.2 ≤ -r ∨ r ≤ z.1.2 := by
    by_contra h
    push Not at h
    exact hnot ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  have hbox {a b c d : ℝ} (hab : a < b) (hcd : c < d)
      (hlo : -1 ≤ a ∧ -1 ≤ c) (hhi : b ≤ 1 ∧ d ≤ 1)
      (hzB : z.1.1 ∈ Icc a b ∧ z.1.2 ∈ Icc c d)
      (hout : b ≤ -r ∨ r ≤ a ∨ d ≤ -r ∨ r ≤ c) :
      ∃ B bd : Set C3, IsFinitePLBallPair C3 B bd ∧ z ∈ B ∧ B ⊆ tube ∧
        Disjoint B (openTube r) := by
    have hball := ((isFinitePLBallPair_Icc hab).prod (isFinitePLBallPair_Icc hcd)).prod
      (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
    refine ⟨_, _, hball, ⟨hzB, hbounds.2⟩, ?_, Set.disjoint_left.mpr ?_⟩
    · intro w hw
      exact ⟨⟨⟨hlo.1.trans hw.1.1.1, hw.1.1.2.trans hhi.1⟩,
        ⟨hlo.2.trans hw.1.2.1, hw.1.2.2.trans hhi.2⟩⟩, hw.2⟩
    · intro w hw ho
      have hi : (-r < w.1.1 ∧ w.1.1 < r) ∧ (-r < w.1.2 ∧ w.1.2 < r) := by
        simpa only [transverseSquare, interior_prod_eq, interior_Icc, mem_prod, mem_Ioo] using ho.1
      rcases hout with h | h | h | h
      · linarith [hw.1.1.2, hi.1.1]
      · linarith [hw.1.1.1, hi.1.2]
      · linarith [hw.1.2.2, hi.2.1]
      · linarith [hw.1.2.1, hi.2.2]
  rcases hsides with h | h | h | h
  · exact hbox (a := -1) (b := -r) (c := -1) (d := 1)
      (by linarith) (by norm_num) ⟨le_rfl, le_rfl⟩ ⟨by linarith, le_rfl⟩
      ⟨⟨hbounds.1.1.1, h⟩, hbounds.1.2⟩ (Or.inl le_rfl)
  · exact hbox (a := r) (b := 1) (c := -1) (d := 1)
      hr1 (by norm_num) ⟨by linarith, le_rfl⟩ ⟨le_rfl, le_rfl⟩
      ⟨⟨h, hbounds.1.1.2⟩, hbounds.1.2⟩ (Or.inr (Or.inl le_rfl))
  · exact hbox (a := -1) (b := 1) (c := -1) (d := -r)
      (by norm_num) (by linarith) ⟨le_rfl, le_rfl⟩ ⟨le_rfl, by linarith⟩
      ⟨hbounds.1.1, hbounds.1.2.1, h⟩ (Or.inr (Or.inr (Or.inl le_rfl)))
  · exact hbox (a := -1) (b := 1) (c := r) (d := 1)
      (by norm_num) hr1 ⟨le_rfl, by linarith⟩ ⟨le_rfl, le_rfl⟩
      ⟨hbounds.1.1, h, hbounds.1.2.2⟩ (Or.inr (Or.inr (Or.inr le_rfl)))

theorem OriginalIntervalTube.closure_interior_exterior
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
    {S T C D : Set P2} {f₀ f₁ : P2 → X}
    (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (hR : IsCompact R) (he : PLDomain e R)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    closure (interior (R \ U.map '' openTube r)) = R \ U.map '' openTube r := by
  have hclosed := (TubeExterior.OriginalIntervalTube.isCompact_exterior U hR he hr hr1.le).isClosed
  apply Subset.antisymm hclosed.closure_interior_subset
  intro x hx
  by_cases hxt : x ∈ U.map '' closedTube r
  · have hlat : x ∈ U.map '' lateral r :=
      (TubeExterior.OriginalIntervalTube.closedTube_sdiff_openTube U hr hr1.le).subset ⟨hxt, hx.2⟩
    obtain ⟨z, hz, rfl⟩ := hlat
    obtain ⟨B, bd, hB, hzB, hBt, hBo⟩ := exists_lateral_exterior_box hr hr1 hz
    have hi : InjOn U.map tube := by
      intro a ha b hb hab
      exact congrArg Subtype.val (U.embedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
    obtain ⟨ball⟩ := exists_chartwisePLBall_image hB
      (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) : C3 ≃L[ℝ] V3)
      U.pl hBt hi
    have hBext : U.map '' B ⊆ R \ U.map '' openTube r := by
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨U.mapsTo_region (hBt hw), ?_⟩
      rintro ⟨v, hv, hvw⟩
      have heq := hi (closedTube_subset hr1.le (openTube_subset r hv)) (hBt hw) hvw
      exact Set.disjoint_left.mp hBo hw (heq ▸ hv)
    exact closure_mono (interior_mono hBext)
      (ball.closure_interior.symm.subset (mem_image_of_mem U.map hzB))
  · have htc : IsClosed (U.map '' closedTube r) :=
      ((isCompact_closedTube r).image_of_continuousOn
        (TubeExterior.OriginalIntervalTube.restrict_closedTube U hr hr1.le).1.continuousOn).isClosed
    have hdense : x ∈ closure ((U.map '' closedTube r)ᶜ ∩ interior R) :=
      htc.isOpen_compl.inter_closure ⟨hxt, he.closure_interior.symm.subset hx.1⟩
    apply closure_mono (t := interior (R \ U.map '' openTube r)) ?_ hdense
    apply (htc.isOpen_compl.inter isOpen_interior).subset_interior_iff.mpr
    intro y hy
    exact ⟨interior_subset hy.2, fun ho => hy.1 ((image_mono (openTube_subset r)) ho)⟩

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior

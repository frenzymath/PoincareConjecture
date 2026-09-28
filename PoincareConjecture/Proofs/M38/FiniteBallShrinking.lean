import PoincareConjecture.Proofs.M38.SurgeryBallNeighborhood











set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38


theorem exists_disjoint_open_of_finite_compact
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {ι : Type*} [Finite ι] (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (K i) (K j)) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i)) ∧ (∀ i, K i ⊆ U i) ∧
      ∀ i j, i ≠ j → Disjoint (U i) (U j) := by
  classical
  have hpair (i j : ι) : ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ K i ⊆ U ∧ K j ⊆ V ∧ (i ≠ j → Disjoint U V) := by
    by_cases hij : i = j
    · exact ⟨univ, univ, isOpen_univ, isOpen_univ, subset_univ _, subset_univ _,
        fun h => (h hij).elim⟩
    · obtain ⟨U, V, hU, hV, hKU, hKV, hUV⟩ :=
        SeparatedNhds.of_isCompact_isCompact (hK i) (hK j) (hdisjoint i j hij)
      exact ⟨U, V, hU, hV, hKU, hKV, fun _ => hUV⟩
  choose U V hU hV hKU hKV hUV using hpair
  refine ⟨fun i => (⋂ j, U i j) ∩ (⋂ j, V j i), ?_, ?_, ?_⟩
  · intro i
    exact (isOpen_iInter_of_finite (hU i)).inter
      (isOpen_iInter_of_finite (fun j => hV j i))
  · intro i x hx
    exact ⟨mem_iInter.mpr (fun j => hKU i j hx),
      mem_iInter.mpr (fun j => hKV j i hx)⟩
  · intro i j hij
    exact (hUV i j hij).mono
      (inter_subset_left.trans (iInter_subset _ j))
      (inter_subset_right.trans (iInter_subset _ i))



theorem exists_disjoint_surgeryBall_widths
    {A : GeneralizedSliceCarrier.{u}} {ι : Type*} [Finite ι]
    (B : ι → SurgeryBallEmbedding A)
    (hB : ∀ i j, i ≠ j → Disjoint (B i).closedBall (B j).closedBall) :
    ∃ a : ι → ℝ, (∀ i, 0 < a i) ∧ (∀ i, a i < 1) ∧
      ∀ i j, i ≠ j → Disjoint
        ((B i).map '' Metric.ball 0 (1 + a i))
        ((B j).map '' Metric.ball 0 (1 + a j)) := by
  obtain ⟨U, hU, hBU, hsep⟩ := exists_disjoint_open_of_finite_compact
    (fun i => (B i).closedBall)
    (fun i => surgeryBall_closedImage_compact (B i) 1 (by norm_num)) hB
  have hwidth (i : ι) : ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      (B i).map '' Metric.ball 0 (1 + a) ⊆ U i := by
    let V : Set StandardCapSpace := Metric.ball 0 2 ∩ (B i).map ⁻¹' U i
    have hV : IsOpen V := (surgeryBallPartialHomeomorph (B i)).isOpen_inter_preimage (hU i)
    have hBV : Metric.closedBall (0 : StandardCapSpace) 1 ⊆ V := by
      intro z hz
      exact ⟨Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hz,
        hBU i (mem_image_of_mem _ hz)⟩
    obtain ⟨a, ha, ha1, haV⟩ := exists_cap_ball_width (by norm_num : (0 : ℝ) < 1) hV hBV
    exact ⟨a, ha, ha1, by rintro _ ⟨z, hz, rfl⟩; exact (haV hz).2⟩
  choose a ha ha1 haU using hwidth
  exact ⟨a, ha, ha1, fun i j hij => (hsep i j hij).mono (haU i) (haU j)⟩

end PoincareConjecture.M38

import PoincareConjecture.Proofs.M25.Mathlib.CompactBallChart











set_option autoImplicit false

open Set Metric

universe u v

namespace OpenPartialHomeomorph





theorem exists_buffered_ball_cover_of_compact_union
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {M : Type v} [TopologicalSpace M] [T2Space M]
    (D : OpenPartialHomeomorph E M) (hsource : D.source = univ)
    (O : Set M) (hO : IsOpen O) (hcompact : IsCompact (D.target ∪ O)) :
    let Y := D.target ∪ O
    let K : ℝ → Set M := fun r => D '' closedBall (0 : E) r
    let V : ℝ → Set M := fun r => D '' ball (0 : E) r
    let W : ℝ → Set M := fun r => Y \ K r
    let S : ℝ → Set M := fun r => D '' sphere (0 : E) r
    ∃ r0 : ℝ, 0 < r0 ∧ Y \ O ⊆ V r0 ∧
      ∀ a b : ℝ, r0 < a → a < b →
        IsOpen (V b) ∧ IsOpen (W a) ∧
        closure (V a) = K a ∧ interior (K a) = V a ∧
        closure (W a) = Y \ V a ∧ interior (Y \ V a) = W a ∧
        IsCompact (Y \ V a) ∧ Y \ V a ⊆ O ∧
        frontier (W a) = S a ∧ frontier (V b) = S b ∧
        V b ∪ W a = Y ∧
        V b ∩ W a = D '' {z : E | a < ‖z‖ ∧ ‖z‖ < b} ∧
        D '' {z : E | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} ⊆ O := by
  classical
  let Y := D.target ∪ O
  let K : ℝ → Set M := fun r => D '' closedBall (0 : E) r
  let V : ℝ → Set M := fun r => D '' ball (0 : E) r
  let W : ℝ → Set M := fun r => Y \ K r
  let S : ℝ → Set M := fun r => D '' sphere (0 : E) r
  change ∃ r0 : ℝ, 0 < r0 ∧ Y \ O ⊆ V r0 ∧
    ∀ a b : ℝ, r0 < a → a < b →
      IsOpen (V b) ∧ IsOpen (W a) ∧
      closure (V a) = K a ∧ interior (K a) = V a ∧
      closure (W a) = Y \ V a ∧ interior (Y \ V a) = W a ∧
      IsCompact (Y \ V a) ∧ Y \ V a ⊆ O ∧
      frontier (W a) = S a ∧ frontier (V b) = S b ∧
      V b ∪ W a = Y ∧
      V b ∩ W a = D '' {z : E | a < ‖z‖ ∧ ‖z‖ < b} ∧
      D '' {z : E | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} ⊆ O
  have hmem (z : E) : z ∈ D.source := by rw [hsource]; exact mem_univ _
  have himage_target (A : Set E) : D '' A ⊆ D.target := by
    rintro x ⟨z, _, rfl⟩
    exact D.map_source (hmem z)
  have himage (A : Set E) : D.IsImage A (D '' A) := by
    apply IsImage.of_image_eq
    rw [hsource, univ_inter, inter_eq_right.mpr (himage_target A)]
  have hKcompact (r : ℝ) : IsCompact (K r) := by
    apply (isCompact_closedBall (0 : E) r).image_of_continuousOn
    exact D.continuousOn.mono (fun z _ => hmem z)
  have hKY (r : ℝ) : K r ⊆ Y :=
    (himage_target _).trans subset_union_left
  have hVY (r : ℝ) : V r ⊆ Y :=
    (himage_target _).trans subset_union_left
  have hdata (r : ℝ) (hr : 0 < r) :
      closure (V r) = K r ∧ interior (K r) = V r ∧
      frontier (K r) = S r ∧ frontier (V r) = S r := by
    have hi : interior (K r) = V r := by
      have h := (himage (closedBall (0 : E) r)).interior.image_eq
      rw [interior_closedBall (0 : E) hr.ne', hsource, univ_inter,
        inter_eq_right.mpr (interior_subset.trans (himage_target _))] at h
      exact h.symm
    have hcl_target : closure (V r) ⊆ D.target :=
      (closure_minimal (image_mono ball_subset_closedBall) (hKcompact r).isClosed).trans
        (himage_target _)
    have hcl : closure (V r) = K r := by
      have h := (himage (ball (0 : E) r)).closure.image_eq
      rw [closure_ball (0 : E) hr.ne', hsource, univ_inter,
        inter_eq_right.mpr hcl_target] at h
      exact h.symm
    have hfrontK : frontier (K r) = S r := by
      have h := (himage (closedBall (0 : E) r)).frontier.image_eq
      rw [frontier_closedBall (0 : E) hr.ne', hsource, univ_inter,
        inter_eq_right.mpr ((hKcompact r).isClosed.frontier_subset.trans
          (himage_target _))] at h
      exact h.symm
    have hVopen : IsOpen (V r) := hi ▸ isOpen_interior
    refine ⟨hcl, hi, hfrontK, ?_⟩
    calc
      frontier (V r) = K r \ V r := by rw [hVopen.frontier_eq, hcl]
      _ = frontier (K r) := by rw [frontier, (hKcompact r).isClosed.closure_eq, hi]
      _ = S r := hfrontK
  have hVopen (r : ℝ) (hr : 0 < r) : IsOpen (V r) :=
    (hdata r hr).2.1 ▸ isOpen_interior
  have hmono {s t : ℝ} (hst : s ≤ t) : V s ⊆ V t :=
    image_mono (ball_subset_ball hst)
  let : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by change (0 : ℝ) < 1; norm_num⟩⟩
  have hcover : Y \ O ⊆ ⋃ r : Ioi (0 : ℝ), V (r : ℝ) := by
    intro x hx
    have hxt : x ∈ D.target := hx.1.resolve_right hx.2
    let r : Ioi (0 : ℝ) := ⟨‖D.symm x‖ + 1, by
      change 0 < ‖D.symm x‖ + 1
      positivity⟩
    apply mem_iUnion.mpr
    refine ⟨r, D.symm x, ?_, D.right_inv hxt⟩
    rw [mem_ball_zero_iff]
    change ‖D.symm x‖ < ‖D.symm x‖ + 1
    linarith
  have hdirected : Directed (· ⊆ ·) (fun r : Ioi (0 : ℝ) => V (r : ℝ)) := by
    intro s t
    let w : Ioi (0 : ℝ) := ⟨max (s : ℝ) (t : ℝ), by
      change 0 < max (s : ℝ) (t : ℝ)
      exact (show 0 < (s : ℝ) from s.property).trans_le (le_max_left _ _)⟩
    exact ⟨w, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩
  obtain ⟨r0, hr0⟩ := (hcompact.diff hO).elim_directed_cover
    (fun r : Ioi (0 : ℝ) => V (r : ℝ)) (fun r => hVopen r r.property)
    hcover hdirected
  refine ⟨r0, r0.property, hr0, ?_⟩
  intro a b hr0a hab
  have ha : 0 < a := r0.property.trans hr0a
  have hb : 0 < b := ha.trans hab
  obtain ⟨hclVa, hiKa, hfrontKa, _⟩ := hdata a ha
  have hYopen : IsOpen Y := D.open_target.union hO
  have hYclosed : IsClosed Y := hcompact.isClosed
  have hWopen : IsOpen (W a) := hYopen.sdiff (hKcompact a).isClosed
  have hWclosure : closure (W a) = Y \ V a := by
    rw [← hiKa]
    apply Subset.antisymm
    · change closure (Y ∩ (K a)ᶜ) ⊆ Y ∩ (interior (K a))ᶜ
      simpa only [hYclosed.closure_eq, closure_compl] using
        (closure_inter_subset : closure (Y ∩ (K a)ᶜ) ⊆ closure Y ∩ closure (K a)ᶜ)
    · change Y ∩ (interior (K a))ᶜ ⊆ closure (Y ∩ (K a)ᶜ)
      simpa only [closure_compl] using hYopen.inter_closure (t := (K a)ᶜ)
  have hWinterior : interior (Y \ V a) = W a := by
    change interior (Y ∩ (V a)ᶜ) = Y ∩ (K a)ᶜ
    rw [interior_inter, hYopen.interior_eq, interior_compl, hclVa]
  have hside : Y \ V a ⊆ O := by
    intro x hx
    by_contra hxO
    exact hx.2 (hmono hr0a.le (hr0 ⟨hx.1, hxO⟩))
  have hWfrontier : frontier (W a) = S a := by
    calc
      frontier (W a) = (Y \ V a) \ (Y \ K a) := by
        rw [hWopen.frontier_eq, hWclosure]
      _ = K a \ V a := by
        ext x
        constructor
        · rintro ⟨⟨hxY, hxV⟩, hxW⟩
          refine ⟨?_, hxV⟩
          by_contra hxK
          exact hxW ⟨hxY, hxK⟩
        · rintro ⟨hxK, hxV⟩
          exact ⟨⟨hKY a hxK, hxV⟩, fun hxW => hxW.2 hxK⟩
      _ = frontier (K a) := by rw [frontier, (hKcompact a).isClosed.closure_eq, hiKa]
      _ = S a := hfrontKa
  have hKV : K a ⊆ V b := image_mono (closedBall_subset_ball hab)
  have hVWcover : V b ∪ W a = Y := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hVY b hx
      · exact hx.1
    · intro hx
      by_cases hxK : x ∈ K a
      · exact Or.inl (hKV hxK)
      · exact Or.inr ⟨hx, hxK⟩
  have hVWoverlap : V b ∩ W a = D '' {z : E | a < ‖z‖ ∧ ‖z‖ < b} := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hxW⟩
      refine ⟨z, ⟨?_, mem_ball_zero_iff.mp hz⟩, rfl⟩
      by_contra hn
      exact hxW.2 ⟨z, mem_closedBall_zero_iff.mpr (le_of_not_gt hn), rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, mem_ball_zero_iff.mpr hz.2, rfl⟩,
        Or.inl (D.map_source (hmem z)), ?_⟩
      rintro ⟨v, hv, heq⟩
      have hvz := D.injOn (hmem v) (hmem z) heq
      exact (not_le_of_gt hz.1) (hvz ▸ mem_closedBall_zero_iff.mp hv)
  refine ⟨hVopen b hb, hWopen, hclVa, hiKa, hWclosure, hWinterior,
    hcompact.diff (hVopen a ha), hside, hWfrontier, (hdata b hb).2.2.2,
    hVWcover, hVWoverlap, ?_⟩
  rintro x ⟨z, hz, rfl⟩
  apply hside
  refine ⟨Or.inl (D.map_source (hmem z)), ?_⟩
  rintro ⟨v, hv, heq⟩
  have hvz := D.injOn (hmem v) (hmem z) heq
  exact (not_lt_of_ge hz.1) (hvz ▸ mem_ball_zero_iff.mp hv)

end OpenPartialHomeomorph

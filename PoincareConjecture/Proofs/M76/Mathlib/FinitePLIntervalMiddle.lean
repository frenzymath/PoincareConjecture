import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc











set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem IsFinitePLBallPair.eq_image_Icc_of_subset
    {f : ℝ → E} {a b α β : ℝ} {d : Set E}
    (hd : IsFinitePLBallPair ℝ d {f α, f β})
    (hf : FinitePiecewiseAffineOn f (Icc a b)) (hi : InjOn f (Icc a b))
    (hαβ : α < β) (hsub : Icc α β ⊆ Icc a b)
    (hds : d ⊆ f '' Icc a b) : d = f '' Icc α β := by
  obtain ⟨e, _, heval⟩ := hf.exists_homeomorph_image hi
  let g : d → ℝ := fun x => (e.symm ⟨x, hds x.property⟩ : ℝ)
  have hg : Continuous g := continuous_subtype_val.comp
    (e.symm.continuous.comp (continuous_subtype_val.subtype_mk fun x => hds x.property))
  let : ConnectedSpace d := isConnected_iff_connectedSpace.mp hd.isConnected
  have hcoord (t : ℝ) (ht : t ∈ Icc a b) (hft : f t ∈ d) : t ∈ range g := by
    refine ⟨⟨f t, hft⟩, ?_⟩
    have heq : (⟨f t, hds hft⟩ : f '' Icc a b) = e ⟨t, ht⟩ :=
      Subtype.ext (heval ⟨t, ht⟩).symm
    change (e.symm ⟨f t, hds hft⟩ : ℝ) = t
    rw [heq, e.symm_apply_apply]
  have hα : α ∈ Icc a b := hsub ⟨le_rfl, hαβ.le⟩
  have hβ : β ∈ Icc a b := hsub ⟨hαβ.le, le_rfl⟩
  have hbetween : Icc α β ⊆ range g :=
    (isPreconnected_range hg).Icc_subset
      (hcoord α hα (hd.1 (by simp))) (hcoord β hβ (hd.1 (by simp)))
  have himage : f '' Icc α β ⊆ d := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨x, hx⟩ := hbetween ht
    have heq : e.symm ⟨x, hds x.property⟩ = ⟨t, hsub ht⟩ := Subtype.ext hx
    have hxt := congrArg (fun u : Icc a b => (e u : E)) heq
    rw [e.apply_symm_apply, heval] at hxt
    exact hxt ▸ x.property
  have hball : IsFinitePLBallPair ℝ (f '' Icc α β) {f α, f β} := by
    simpa only [image_pair] using
      (isFinitePLBallPair_Icc hαβ).image_of_subset hf hsub hi
  have hend : f α ≠ f β := fun h => hαβ.ne (hi hα hβ h)
  exact (hball.eq_of_subset_with_same_endpoints hd himage hend).symm






theorem IsFinitePLBallPair.exists_middle_between_disjoint_ends
    {s d₀ d₁ : Set E} {a b c₀ c₁ : E}
    (hs : IsFinitePLBallPair ℝ s {a, b})
    (hd₀ : IsFinitePLBallPair ℝ d₀ {a, c₀})
    (hd₁ : IsFinitePLBallPair ℝ d₁ {c₁, b})
    (h₀s : d₀ ⊆ s) (h₁s : d₁ ⊆ s)
    (hab : a ≠ b) (hac : a ≠ c₀) (hcb : c₁ ≠ b)
    (hdis : Disjoint d₀ d₁) :
    ∃ m : Set E, IsFinitePLBallPair ℝ m {c₀, c₁} ∧ c₀ ≠ c₁ ∧
      m ∪ (d₀ ∪ d₁) = s ∧ m ∩ d₀ = {c₀} ∧ m ∩ d₁ = {c₁} := by
  obtain ⟨e, he, hea, heb⟩ := hs.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨f, hf, heval⟩ := he
  have hi : InjOn f (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((heval ⟨x, hx⟩).trans (hxy.trans (heval ⟨y, hy⟩).symm))))
  have hfs : f '' Icc (0 : ℝ) 1 = s := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact heval ⟨t, ht⟩ ▸ (e ⟨t, ht⟩).property
    · intro x hx
      refine ⟨e.symm ⟨x, hx⟩, (e.symm ⟨x, hx⟩).property, ?_⟩
      exact (heval _).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩))
  have hf0 : f 0 = a := (heval ⟨0, ⟨le_rfl, zero_le_one⟩⟩).symm.trans hea
  have hf1 : f 1 = b := (heval ⟨1, ⟨zero_le_one, le_rfl⟩⟩).symm.trans heb
  have hc₀ : c₀ ∈ s := h₀s (hd₀.1 (by simp))
  have hc₁ : c₁ ∈ s := h₁s (hd₁.1 (by simp))
  let α : ℝ := e.symm ⟨c₀, hc₀⟩
  let β : ℝ := e.symm ⟨c₁, hc₁⟩
  have hα : α ∈ Icc (0 : ℝ) 1 := (e.symm ⟨c₀, hc₀⟩).property
  have hβ : β ∈ Icc (0 : ℝ) 1 := (e.symm ⟨c₁, hc₁⟩).property
  have hfα : f α = c₀ :=
    (heval _).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨c₀, hc₀⟩))
  have hfβ : f β = c₁ :=
    (heval _).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨c₁, hc₁⟩))
  have h0α : 0 < α := by
    by_contra h
    have hα0 : α = 0 := le_antisymm (le_of_not_gt h) hα.1
    exact hac (hf0.symm.trans (hα0 ▸ hfα))
  have hβ1 : β < 1 := by
    by_contra h
    have hβeq : β = 1 := le_antisymm hβ.2 (le_of_not_gt h)
    exact hcb (hfβ.symm.trans (hβeq.symm ▸ hf1))
  have hleft : d₀ = f '' Icc 0 α := by
    have hp : IsFinitePLBallPair ℝ d₀ {f 0, f α} := by rwa [hf0, hfα]
    exact hp.eq_image_Icc_of_subset hf hi h0α
      (fun _ hx => ⟨hx.1, hx.2.trans hα.2⟩) (h₀s.trans hfs.symm.subset)
  have hright : d₁ = f '' Icc β 1 := by
    have hp : IsFinitePLBallPair ℝ d₁ {f β, f 1} := by rwa [hfβ, hf1]
    exact hp.eq_image_Icc_of_subset hf hi hβ1
      (fun _ hx => ⟨hβ.1.trans hx.1, hx.2⟩) (h₁s.trans hfs.symm.subset)
  have hαβ : α < β := by
    by_contra h
    have hβd₀ : f β ∈ d₀ := hleft.symm ▸
      (show f β ∈ f '' Icc 0 α from ⟨β, ⟨hβ.1, le_of_not_gt h⟩, rfl⟩)
    exact disjoint_left.mp hdis hβd₀
      (hfβ.symm ▸ hd₁.1 (show c₁ ∈ ({c₁, b} : Set E) from Or.inl rfl))
  have hm : Icc α β ⊆ Icc (0 : ℝ) 1 :=
    fun _ hx => ⟨hα.1.trans hx.1, hx.2.trans hβ.2⟩
  have hball : IsFinitePLBallPair ℝ (f '' Icc α β) {c₀, c₁} := by
    simpa only [image_pair, hfα, hfβ] using
      (isFinitePLBallPair_Icc hαβ).image_of_subset hf hm hi
  have hcc : c₀ ≠ c₁ := by
    intro h
    exact hαβ.ne (hi hα hβ (hfα.trans (h.trans hfβ.symm)))
  refine ⟨f '' Icc α β, hball, hcc, ?_, ?_, ?_⟩
  · have hcover : Icc α β ∪ (Icc 0 α ∪ Icc β 1) = Icc (0 : ℝ) 1 := by
      ext t
      constructor
      · rintro (ht | ht | ht)
        · exact hm ht
        · exact ⟨ht.1, ht.2.trans hα.2⟩
        · exact ⟨hβ.1.trans ht.1, ht.2⟩
      · intro ht
        by_cases hta : t ≤ α
        · exact Or.inr (Or.inl ⟨ht.1, hta⟩)
        by_cases hbt : β ≤ t
        · exact Or.inr (Or.inr ⟨hbt, ht.2⟩)
        exact Or.inl ⟨(le_of_not_ge hta), le_of_not_ge hbt⟩
    rw [hleft, hright, ← image_union, ← image_union, hcover, hfs]
  · have hinterval : Icc α β ∩ Icc 0 α = ({α} : Set ℝ) := by
      ext t
      constructor
      · intro ht
        exact le_antisymm ht.2.2 ht.1.1
      · rintro rfl
        exact ⟨⟨le_rfl, hαβ.le⟩, ⟨hα.1, le_rfl⟩⟩
    have hinter : f '' (Icc α β ∩ Icc 0 α) = f '' Icc α β ∩ f '' Icc 0 α :=
      image_inter_on fun x hx y hy hxy => hi ⟨hx.1, hx.2.trans hα.2⟩ (hm hy) hxy
    rw [hleft, ← hinter, hinterval, image_singleton, hfα]
  · have hinterval : Icc α β ∩ Icc β 1 = ({β} : Set ℝ) := by
      ext t
      constructor
      · intro ht
        exact le_antisymm ht.1.2 ht.2.1
      · rintro rfl
        exact ⟨⟨hαβ.le, le_rfl⟩, ⟨le_rfl, hβ.2⟩⟩
    have hinter : f '' (Icc α β ∩ Icc β 1) = f '' Icc α β ∩ f '' Icc β 1 :=
      image_inter_on fun x hx y hy hxy => hi ⟨hβ.1.trans hx.1, hx.2⟩ (hm hy) hxy
    rw [hright, ← hinter, hinterval, image_singleton, hfβ]

end Set

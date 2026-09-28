import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedQuarterPrismEndMaps

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem signedTubeRadius_subset_radialRim (signs : Fin 2 → Bool) (i : Fin 2) :
    signedTubeRadius i (signs i.rev) ⊆ signedTubeRadialRim (signs 0) (signs 1) := by
  fin_cases i
  · exact subset_union_left
  · exact subset_union_right

theorem signedTubeRadius_subset_quarter (signs : Fin 2 → Bool) (i : Fin 2) :
    signedTubeRadius i (signs i.rev) ⊆ signedTubeQuarter (signs 0) (signs 1) := by
  fin_cases i
  · exact fun _ hx => (signedTube_quarter_ball (signs 0) (signs 1)).1 (Or.inr (Or.inl hx))
  · exact fun _ hx => (signedTube_quarter_ball (signs 0) (signs 1)).1 (Or.inr (Or.inr hx))

theorem exists_signed_sector_prescribed_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (signs : Fin 2 → Bool) (α β : ℝ) (hαβ : α < β)
    (F : Fin 2 → Set E) (Q : Bool → Set E) (Z : Set E)
    (f : ∀ i, ↥(signedTubeRadius i (signs i.rev) ×ˢ Icc α β) ≃ₜ F i)
    (e : ∀ j, signedTubeQuarter (signs 0) (signs 1) ≃ₜ Q j)
    (hf : ∀ i, (f i).IsFinitePL) (he : ∀ j, (e j).IsFinitePL)
    (hinter : F 0 ∩ F 1 = Z) (hdisj : Disjoint (Q false) (Q true))
    (z : Icc α β → E)
    (haxis : ∀ x : ↥(signedTubeRadius 0 (signs 1) ×ˢ Icc α β),
      (x : P2 × ℝ).1 = (0, 0) ↔ (f 0 x : E) ∈ Z)
    (hz : ∀ i (t : Icc α β),
      (f i ⟨((0, 0), t), left_mem_segment ℝ _ _, t.property⟩ : E) = z t)
    (hcontact : ∀ j i (x : signedTubeQuarter (signs 0) (signs 1)),
      (e j x : E) ∈ F i ↔ (x : P2) ∈ signedTubeRadius i (signs i.rev))
    (hkeep : ∀ i j (x : signedTubeRadius i (signs i.rev)),
      (f i ⟨(x, if j then β else α), x.property,
        by cases j <;> simp [hαβ.le]⟩ : E) =
          e j ⟨x, signedTubeRadius_subset_quarter signs i x.property⟩) :
    ∃ H : signedTubeSectorPrescribed (signs 0) (signs 1) α β ≃ₜ
        ↥((F 0 ∪ F 1) ∪ (Q false ∪ Q true)),
      H.IsFinitePL ∧
      (∀ i (x : ↥(signedTubeRadius i (signs i.rev) ×ˢ Icc α β)),
        (H ⟨x, Or.inl ⟨signedTubeRadius_subset_radialRim signs i x.property.1,
          x.property.2⟩⟩ : E) = f i x) ∧
      ∀ j (x : signedTubeQuarter (signs 0) (signs 1)),
        (H ⟨(x, if j then β else α), Or.inr ⟨x.property,
          by cases j <;> simp⟩⟩ : E) = e j x := by
  classical
  let R := signedTubeRadialRim (signs 0) (signs 1)
  let sourceQ := signedTubeQuarter (signs 0) (signs 1)
  let time := fun j : Bool => if j then β else α
  have htime (j : Bool) : time j ∈ Icc α β := by cases j <;> exact (by simpa [time] using hαβ.le)
  have hRQ : R ⊆ sourceQ :=
    fun _ hx => (signedTube_quarter_ball (signs 0) (signs 1)).1 (Or.inr hx)
  obtain ⟨r, hr, hr0, hr1⟩ := exists_signed_sector_radial_map (signs 0) (signs 1) α β
    (f 0) (f 1) (hf 0) (hf 1) hinter z haxis (hz 0) (hz 1)
  have hrad (i : Fin 2) : signedTubeRadius i (signs i.rev) ⊆ R :=
    signedTubeRadius_subset_radialRim signs i
  have hrkeep (i : Fin 2) (x : ↥(signedTubeRadius i (signs i.rev) ×ˢ Icc α β)) :
      (r ⟨x, hrad i x.property.1, x.property.2⟩ : E) = f i x := by
    fin_cases i
    · exact hr0 x
    · exact hr1 x
  have hpre (i : Fin 2) (j : Bool)
      (x : ↥(signedTubeRadius i (signs i.rev) ×ˢ Icc α β)) :
      (x : P2 × ℝ).2 = time j ↔ (f i x : E) ∈ Q j :=
    signed_half_face_end_preimage (signs 0) (signs 1) i (signs i.rev) α β
      (time j) (htime j) (signedTubeRadius_subset_quarter signs i)
      (f i) (e j) (hcontact j i) (hkeep i j) x
  have hrpre (j : Bool) (x : ↥(R ×ˢ Icc α β)) :
      (x : P2 × ℝ).2 = time j ↔ (r x : E) ∈ Q j := by
    rcases x.property.1 with hx | hx
    · have hv := hrkeep 0 ⟨x, hx, x.property.2⟩
      exact (hpre 0 j ⟨x, hx, x.property.2⟩).trans (by rw [← hv])
    · have hv := hrkeep 1 ⟨x, hx, x.property.2⟩
      exact (hpre 1 j ⟨x, hx, x.property.2⟩).trans (by rw [← hv])
  have hrend (j : Bool) (x : R) :
      (r ⟨(x, time j), x.property, htime j⟩ : E) = e j ⟨x, hRQ x.property⟩ := by
    rcases x.property with hx | hx
    · exact (hrkeep 0 ⟨(x, time j), hx, htime j⟩).trans (hkeep 0 j ⟨x, hx⟩)
    · exact (hrkeep 1 ⟨(x, time j), hx, htime j⟩).trans (hkeep 1 j ⟨x, hx⟩)
  obtain ⟨d, hd, hd0, hd1⟩ := exists_signed_sector_end_map
    (signs 0) (signs 1) α β hαβ (e false) (e true) (he false) (he true) hdisj
  have hdend (j : Bool) (x : sourceQ) :
      (d ⟨(x, time j), x.property, by cases j <;> simp [time]⟩ : E) = e j x := by
    cases j
    · exact hd0 x
    · exact hd1 x
  have hoverlap (x : ↥(R ×ˢ Icc α β)) :
      (x : P2 × ℝ) ∈ sourceQ ×ˢ ({α, β} : Set ℝ) ↔ (r x : E) ∈ Q false ∪ Q true := by
    have h0 := hrpre false x
    have h1 := hrpre true x
    simpa only [mem_prod, hRQ x.property.1, true_and, mem_insert_iff,
      mem_singleton_iff, mem_union, time, Bool.false_eq_true, if_false, if_true] using h0.or h1
  have hagree (x : P2 × ℝ) (hxR : x ∈ R ×ˢ Icc α β)
      (hxQ : x ∈ sourceQ ×ˢ ({α, β} : Set ℝ)) :
      (r ⟨x, hxR⟩ : E) = d ⟨x, hxQ⟩ := by
    rcases x with ⟨y, t⟩
    rcases hxQ.2 with h | h
    · change t = α at h
      subst t
      exact (hrend false ⟨y, hxR.1⟩).trans (hdend false ⟨y, hxQ.1⟩).symm
    · change t = β at h
      subst t
      exact (hrend true ⟨y, hxR.1⟩).trans (hdend true ⟨y, hxQ.1⟩).symm
  obtain ⟨H, hH, hHr, hHd⟩ := Homeomorph.exists_union_finitePL r d hr hd hoverlap hagree
  refine ⟨H, hH, ?_, ?_⟩
  · intro i x
    exact (hHr ⟨x, hrad i x.property.1, x.property.2⟩).trans (hrkeep i x)
  · intro j x
    exact (hHd ⟨(x, time j), x.property, by cases j <;> simp [time]⟩).trans (hdend j x)

end PoincareConjecture.M76.Dehn

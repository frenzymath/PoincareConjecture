import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Source.Rim
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.TubeArmOrientation



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

noncomputable def returningStripOrientation (positive : Bool) : P2 →ᴬ[ℝ] P2 :=
  let t := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let u := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  t.prod (if positive then u else -u)

theorem returningStripOrientation_involutive (s : Bool) :
    Function.Involutive (returningStripOrientation s) := by
  intro p
  cases s <;> simp [returningStripOrientation]

theorem returningStripOrientation_mem_source (s : Bool) (p : P2) :
    returningStripOrientation s p ∈ source ↔ p ∈ source := by
  cases s <;> simp [returningStripOrientation, source, Prod.le_def, neg_le,
    and_comm, and_left_comm, and_assoc]

theorem returningStripOrientation_image_source (s : Bool) :
    returningStripOrientation s '' source = source := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact (returningStripOrientation_mem_source s p).mpr hp
  · intro p hp
    exact ⟨returningStripOrientation s p,
      (returningStripOrientation_mem_source s p).mpr hp,
      returningStripOrientation_involutive s p⟩

theorem returningStripOrientation_mem_half (s b : Bool) (p : P2) :
    returningStripOrientation s p ∈ halfSource b ↔
      p ∈ halfSource (if s then b else !b) := by
  cases s <;> cases b <;>
    simp [returningStripOrientation, halfSource, Prod.le_def, neg_le,
      and_comm, and_left_comm, and_assoc]

theorem returningStripOrientation_image_half (s b : Bool) :
    returningStripOrientation s '' halfSource b = halfSource (if s then b else !b) := by
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    rw [returningStripOrientation_mem_half]
    cases s <;> simpa using hp
  · intro p hp
    refine ⟨returningStripOrientation s p, ?_, returningStripOrientation_involutive s p⟩
    exact (returningStripOrientation_mem_half s b p).mpr hp

theorem returningStripOrientation_image_center (s : Bool) :
    returningStripOrientation s '' arm 0 = arm 0 := by
  have hfix (p : P2) (hp : p ∈ arm 0) : returningStripOrientation s p = p := by
    have hp0 : p.2 = 0 := hp.2
    cases s <;> apply Prod.ext <;> simp [returningStripOrientation, hp0]
  apply Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    simpa only [hfix p hp] using hp
  · intro p hp
    exact ⟨p, hp, hfix p hp⟩

theorem returningStripOrientation_finitePL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : P2 → E} (hc : FinitePiecewiseAffineOn c source) (s : Bool) :
    FinitePiecewiseAffineOn (c ∘ returningStripOrientation s) source := by
  have hc' := hc
  obtain ⟨K, hK, hKs, _⟩ := hc'
  have ha : FinitePiecewiseAffineOn (returningStripOrientation s) source :=
    ⟨K, hK, hKs, K.affineOnFaces_affine (returningStripOrientation s)⟩
  exact hc.comp ha
    (fun p hp ↦ (returningStripOrientation_mem_source s p).mpr hp)

theorem returningStripOrientation_embedding
    {E : Type*} [TopologicalSpace E] {c : P2 → E}
    (hc : IsEmbedding (fun p : source ↦ c p)) (s : Bool) :
    IsEmbedding (fun p : source ↦ (c ∘ returningStripOrientation s) p) := by
  let h : source ≃ₜ source := {
    toFun := fun p ↦ ⟨returningStripOrientation s p,
      (returningStripOrientation_mem_source s p).mpr p.property⟩
    invFun := fun p ↦ ⟨returningStripOrientation s p,
      (returningStripOrientation_mem_source s p).mpr p.property⟩
    left_inv := fun p ↦ Subtype.ext (returningStripOrientation_involutive s p)
    right_inv := fun p ↦ Subtype.ext (returningStripOrientation_involutive s p)
    continuous_toFun := ((returningStripOrientation s).continuous.comp
      continuous_subtype_val).subtype_mk _
    continuous_invFun := ((returningStripOrientation s).continuous.comp
      continuous_subtype_val).subtype_mk _ }
  exact hc.comp h.isEmbedding

theorem exists_returning_strip_cut_orientation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A B QA QB : Set E} {c : P2 → E}
    (hA : IsFinitePLBallPair P2 A QA) (hB : IsFinitePLBallPair P2 B QB)
    (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcAB : c '' source ⊆ A ∪ B) (hi : A ∩ B = c '' arm 0)
    (hQA : c '' arm 0 ⊆ QA) (hQB : c '' arm 0 ⊆ QB) :
    ∃ s : Bool,
      (c ∘ returningStripOrientation s) '' halfSource true ⊆ A ∧
      (c ∘ returningStripOrientation s) '' halfSource false ⊆ B := by
  rcases strip_halves_on_opposite_cut_sides hA hB c hc hci hcAB hi hQA hQB with h | h
  · refine ⟨false, ?_, ?_⟩
    · rw [image_comp, returningStripOrientation_image_half]
      exact h.1
    · rw [image_comp, returningStripOrientation_image_half]
      exact h.2
  · refine ⟨true, ?_, ?_⟩
    · rw [image_comp, returningStripOrientation_image_half]
      exact h.2
    · rw [image_comp, returningStripOrientation_image_half]
      exact h.1

end PoincareConjecture.M76.Dehn.Annuli

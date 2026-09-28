import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedPrismReparametrization
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedCoordinateSectors









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem signed_prism_end_preimage
    {E : Type*} [TopologicalSpace E] {D J : Set E} {α β t : ℝ}
    (ht : t ∈ Icc α β)
    (H : ↥(signedTubeDiamond ×ˢ Icc α β) ≃ₜ D) (G : signedTubeDiamond ≃ₜ J)
    (hkeep : ∀ x : signedTubeDiamond, (H ⟨(x, t), x.property, ht⟩ : E) = G x)
    (x : ↥(signedTubeDiamond ×ˢ Icc α β)) :
    (H x : E) ∈ J ↔ (x : P2 × ℝ).2 = t := by
  constructor
  · intro hx
    let y : signedTubeDiamond := G.symm ⟨H x, hx⟩
    have he : (H ⟨(y, t), y.property, ht⟩ : E) = H x :=
      (hkeep y).trans (congrArg Subtype.val (G.apply_symm_apply _))
    exact (congrArg (fun z : ↥(signedTubeDiamond ×ˢ Icc α β) => (z : P2 × ℝ).2)
      (H.injective (Subtype.ext he))).symm
  · intro hx
    let y : signedTubeDiamond := ⟨(x : P2 × ℝ).1, x.property.1⟩
    have he : x = ⟨(y, t), y.property, ht⟩ := Subtype.ext (Prod.ext rfl hx)
    rw [he, hkeep]
    exact (G y).property

theorem signed_prism_axis_preimage
    {E : Type*} [TopologicalSpace E] {D Z : Set E} {α β : ℝ}
    (H : ↥(signedTubeDiamond ×ˢ Icc α β) ≃ₜ D) (Q : Bool → Bool → Set E)
    (hQ : ∀ eps delta (x : ↥(signedTubeDiamond ×ˢ Icc α β)),
      (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔ (H x : E) ∈ Q eps delta)
    (hAxis : Q false false ∩ Q true true = Z)
    (x : ↥(signedTubeDiamond ×ˢ Icc α β)) :
    (x : P2 × ℝ).1 = (0, 0) ↔ (H x : E) ∈ Z := by
  rw [← mem_singleton_iff, ← signedTube_quarter_inter_opposite false false]
  change ((x : P2 × ℝ).1 ∈ signedTubeQuarter false false ∧
    (x : P2 × ℝ).1 ∈ signedTubeQuarter true true) ↔ _
  rw [hQ, hQ]
  exact Set.ext_iff.mp hAxis (H x)

theorem signed_prism_coordinate_axis_preimage
    {E : Type*} [TopologicalSpace E] {D Z : Set E} {α β : ℝ}
    (H : ↥(signedTubeDiamond ×ˢ Icc α β) ≃ₜ D) (c : Fin 2 → E → ℝ)
    (hQ : ∀ eps delta (x : ↥(signedTubeDiamond ×ˢ Icc α β)),
      (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
        (H x : E) ∈ D ∩ {z | ∀ i : Fin 2,
          if (![eps, delta] i) then 0 ≤ c i z else c i z ≤ 0})
    (hAxis : {z | z ∈ D ∧ c 0 z = 0 ∧ c 1 z = 0} = Z)
    (x : ↥(signedTubeDiamond ×ˢ Icc α β)) :
    (x : P2 × ℝ).1 = (0, 0) ↔ (H x : E) ∈ Z := by
  have hSector (eps delta : Bool) :
      D ∩ {z | ∀ i : Fin 2, if (![eps, delta] i) then 0 ≤ c i z else c i z ≤ 0} =
        signedCoordinateSector D c (fun _ => true) eps delta := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1, hz.2 0, hz.2 1⟩
    · rintro ⟨hd, h0, h1⟩
      refine ⟨hd, ?_⟩
      intro i
      fin_cases i
      · exact h0
      · exact h1
  apply signed_prism_axis_preimage H
    (fun eps delta => signedCoordinateSector D c (fun _ => true) eps delta)
    (fun eps delta y => by rw [← hSector]; exact hQ eps delta y) ?_ x
  exact (signedCoordinateSector_incidence D c (fun _ => true) false false).2.2.1.trans hAxis

theorem signed_prism_coordinate_sheet_preimage
    {E : Type*} [TopologicalSpace E] {D : Set E} {α β : ℝ}
    (H : ↥(signedTubeDiamond ×ˢ Icc α β) ≃ₜ D) (c : Fin 2 → E → ℝ)
    (hQ : ∀ eps delta (x : ↥(signedTubeDiamond ×ˢ Icc α β)),
      (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
        (H x : E) ∈ D ∩ {z | ∀ i : Fin 2,
          if (![eps, delta] i) then 0 ≤ c i z else c i z ≤ 0})
    (i : Fin 2) (x : ↥(signedTubeDiamond ×ˢ Icc α β)) :
    (x : P2 × ℝ).1 ∈ signedTubeSheet i ↔ c i (H x) = 0 := by
  have hSector (eps delta : Bool) :
      (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔
        (H x : E) ∈ signedCoordinateSector D c (fun _ => true) eps delta := by
    refine (hQ eps delta x).trans ?_
    constructor
    · intro hz
      exact ⟨hz.1, hz.2 0, hz.2 1⟩
    · rintro ⟨hd, h0, h1⟩
      refine ⟨hd, ?_⟩
      intro k
      fin_cases k
      · exact h0
      · exact h1
  have hRadius (i : Fin 2) (sign : Bool) :
      (x : P2 × ℝ).1 ∈ signedTubeRadius i sign ↔
        (H x : E) ∈ signedCoordinateFace D c (fun _ => true) i sign := by
    fin_cases i
    · change (x : P2 × ℝ).1 ∈ signedTubeRadius 0 sign ↔ _
      rw [← signedTube_quarter_inter_eps false sign]
      change ((x : P2 × ℝ).1 ∈ signedTubeQuarter false sign ∧
        (x : P2 × ℝ).1 ∈ signedTubeQuarter (!false) sign) ↔ _
      rw [hSector, hSector]
      exact Set.ext_iff.mp (signedCoordinateSector_incidence D c (fun _ => true) false sign).2.1 (H x)
    · change (x : P2 × ℝ).1 ∈ signedTubeRadius 1 sign ↔ _
      rw [← signedTube_quarter_inter_delta sign false]
      change ((x : P2 × ℝ).1 ∈ signedTubeQuarter sign false ∧
        (x : P2 × ℝ).1 ∈ signedTubeQuarter sign (!false)) ↔ _
      rw [hSector, hSector]
      exact Set.ext_iff.mp (signedCoordinateSector_incidence D c (fun _ => true) sign false).1 (H x)
  change ((x : P2 × ℝ).1 ∈ signedTubeRadius i false ∨
    (x : P2 × ℝ).1 ∈ signedTubeRadius i true) ↔ _
  rw [hRadius, hRadius]
  constructor
  · rintro (hx | hx) <;> exact hx.2.1
  · intro hx
    rcases le_total (c i.rev (H x)) 0 with hneg | hpos
    · exact Or.inl ⟨(H x).property, hx, hneg⟩
    · exact Or.inr ⟨(H x).property, hx, hpos⟩

theorem signedTubeReflection_mem_sheet (eta : Fin 2 → Bool) (i : Fin 2) (x : P2) :
    signedTubeReflection eta x ∈ signedTubeSheet i ↔ x ∈ signedTubeSheet i := by
  have h := (signedTubeReflection_mem_radius eta i false x).or
    (signedTubeReflection_mem_radius eta i true x)
  change (_ ∈ signedTubeRadius i false ∨ _ ∈ signedTubeRadius i true) ↔
    (x ∈ signedTubeRadius i false ∨ x ∈ signedTubeRadius i true)
  cases he : eta i.rev
  · simpa only [he, signedTubeReindex, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, or_comm] using h
  · simpa only [he, signedTubeReindex, ↓reduceIte] using h

end PoincareConjecture.M76.Dehn

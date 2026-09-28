import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedCoordinateSectors

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_signedTubeQuarter_point_off_radii (eps delta : Bool) :
    ∃ x ∈ signedTubeQuarter eps delta,
      x ∉ signedTubeRadius 0 delta ∧ x ∉ signedTubeRadius 1 eps := by
  let x : P2 := (1 / 2 : ℝ) • signedTubeCorner 1 eps +
    (1 / 2 : ℝ) • signedTubeCorner 0 delta
  have hc₁ : signedTubeCorner 1 eps ∈ signedTubeQuarter eps delta :=
    subset_convexHull ℝ _ ⟨1, rfl⟩
  have hc₀ : signedTubeCorner 0 delta ∈ signedTubeQuarter eps delta :=
    subset_convexHull ℝ _ ⟨2, rfl⟩
  have hx : x ∈ signedTubeQuarter eps delta :=
    (convex_convexHull ℝ _) hc₁ hc₀ (by norm_num) (by norm_num) (by norm_num)
  refine ⟨x, hx, ?_, ?_⟩
  · rintro ⟨a, b, ha, hb, hab, heq⟩
    have he := congrArg Prod.fst heq
    cases eps <;> cases delta <;> norm_num [x, signedTubeCorner] at he
  · rintro ⟨a, b, ha, hb, hab, heq⟩
    have he := congrArg Prod.snd heq
    cases eps <;> cases delta <;> norm_num [x, signedTubeCorner] at he

theorem exists_strict_point_of_signed_diamond_quarters
    {E : Type*} [TopologicalSpace E] (J : Set E)
    (c : Fin 2 → E → ℝ) (eta : Fin 2 → Bool)
    (G : signedTubeDiamond ≃ₜ J)
    (hquarter : ∀ eps delta (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter eps delta ↔
        (G x : E) ∈ signedCoordinateSector J c eta eps delta)
    (signs : Fin 2 → Bool) :
    ∃ y ∈ J, ∀ i : Fin 2, if signs i then 0 < c i y else c i y < 0 := by
  let eps := signedTubeReindex (eta 0) (signs 0)
  let delta := signedTubeReindex (eta 1) (signs 1)
  obtain ⟨x, hx, hxr₀, hxr₁⟩ := exists_signedTubeQuarter_point_off_radii eps delta
  let xd : signedTubeDiamond := ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, hx⟩⟩⟩
  have hq := (hquarter eps delta xd).mp hx
  have hn₀ : c 0 (G xd) ≠ 0 := by
    intro hz
    have hother : (G xd : E) ∈ signedCoordinateSector J c eta (!eps) delta := by
      refine ⟨(G xd).property, ?_, hq.2.2⟩
      rw [hz]
      cases signedTubeReindex (eta 0) (!eps) <;> exact le_rfl
    have hi := (signedTube_quarter_inter_eps eps delta).subset
      ⟨hx, (hquarter (!eps) delta xd).mpr hother⟩
    exact hxr₀ hi
  have hn₁ : c 1 (G xd) ≠ 0 := by
    intro hz
    have hother : (G xd : E) ∈ signedCoordinateSector J c eta eps (!delta) := by
      refine ⟨(G xd).property, hq.2.1, ?_⟩
      rw [hz]
      cases signedTubeReindex (eta 1) (!delta) <;> exact le_rfl
    have hi := (signedTube_quarter_inter_delta eps delta).subset
      ⟨hx, (hquarter eps (!delta) xd).mpr hother⟩
    exact hxr₁ hi
  have hcut₀ : signedCoordinateCut (signs 0) (c 0 (G xd)) := by
    simpa only [eps, signedTubeReindex_involutive] using hq.2.1
  have hcut₁ : signedCoordinateCut (signs 1) (c 1 (G xd)) := by
    simpa only [delta, signedTubeReindex_involutive] using hq.2.2
  refine ⟨G xd, (G xd).property, ?_⟩
  intro i
  fin_cases i
  · change if signs 0 then 0 < c 0 (G xd) else c 0 (G xd) < 0
    cases hs : signs 0 <;> simp only [signedCoordinateCut, hs,
      Bool.false_eq_true, ↓reduceIte] at hcut₀ ⊢
    · exact lt_of_le_of_ne hcut₀ hn₀
    · exact lt_of_le_of_ne hcut₀ hn₀.symm
  · change if signs 1 then 0 < c 1 (G xd) else c 1 (G xd) < 0
    cases hs : signs 1 <;> simp only [signedCoordinateCut, hs,
      Bool.false_eq_true, ↓reduceIte] at hcut₁ ⊢
    · exact lt_of_le_of_ne hcut₁ hn₁
    · exact lt_of_le_of_ne hcut₁ hn₁.symm

end PoincareConjecture.M76.Dehn

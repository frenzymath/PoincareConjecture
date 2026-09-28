import PoincareConjecture.Proofs.M76.Mathlib.AllNonzeroCappedLevels

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem IsFinitePLBallPair.exists_ordinary_terminal_level_comparisons
    {s b d : Set X} (hs : IsFinitePLBallPair E s b) (A : X →ᵃ[ℝ] ℝ)
    (hdplane : d ⊆ {x | A x = 0}) {β t : ℝ} (ht : 0 < t) (H : X ≃ₜ X)
    (hraise : ∀ x, A x ≤ A (H x))
    (hneg : ∀ x ∈ (s ∪ d) ∩ {x | A x < 0}, H x = x)
    (hhigh : ∀ x, β ≤ A x → H x = x)
    (hlevels : ∀ c ∈ Ioo (0 : ℝ) β, t ≤ c →
      ∃ F : (s ∩ {x | A x = c} : Set X) ≃ₜ
        ((H '' (s ∪ d)) ∩ {x | A x = c} : Set X), F.IsFinitePL) :
    ∀ c : ℝ, c < 0 ∨ t ≤ c →
      ∃ F : (s ∩ {x | A x = c} : Set X) ≃ₜ
        ((H '' (s ∪ d)) ∩ {x | A x = c} : Set X), F.IsFinitePL := by
  intro c hc
  have hcne : c ≠ 0 := hc.elim ne_of_lt (fun h => (ht.trans_le h).ne')
  by_cases hin : c ∈ Ioo (0 : ℝ) β
  · exact hlevels c hin (hc.resolve_left (not_lt_of_ge hin.1.le))
  have hold : (s ∪ d) ∩ {x | A x = c} = s ∩ {x | A x = c} := by
    ext x
    constructor
    · rintro ⟨hx | hx, hxA⟩
      · exact ⟨hx, hxA⟩
      · exact (hcne (hxA.symm.trans (hdplane hx))).elim
    · exact fun hx => ⟨Or.inl hx.1, hx.2⟩
  have heq : (H '' (s ∪ d)) ∩ {x | A x = c} = s ∩ {x | A x = c} := by
    by_cases hn : c < 0
    · exact (image_negative_level_eq_of_height_le A H (fun x _ => hraise x)
        (fun x hx hxA => hneg x ⟨hx, hxA⟩) hn).trans hold
    · have hpos : 0 < c := lt_of_le_of_ne (le_of_not_gt hn) hcne.symm
      have hceiling : β ≤ c := le_of_not_gt (fun h => hin ⟨hpos, h⟩)
      exact (H.injective.image_inter_eq_of_fixed (t := {x | A x = c})
        (fun x hx => hhigh x (hx ▸ hceiling))).trans hold
  have hcopy := hs
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  obtain ⟨J, hJ, hJspace⟩ := K.exists_finite_affineLevel_complex hK A c
  rw [hKs] at hJspace
  exact ⟨Homeomorph.setCongr heq.symm,
    ⟨id, ⟨J, hJ, hJspace, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ X)⟩,
      fun _ => rfl⟩⟩

end Set

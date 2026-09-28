import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubdiskUniqueness
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc











set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem IsFinitePLBallPair.boundary_attached_disk_complement
    {s q D U V W : Set E} {a b : E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (hD : IsFinitePLBallPair (ℝ × ℝ) D (U ∪ W)) (hDs : D ⊆ s)
    (hU : IsFinitePLBallPair ℝ U {a, b})
    (hV : IsFinitePLBallPair ℝ V {a, b})
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a ≠ b)
    (hUV : U ∩ V ⊆ {a, b}) (hrim : U ∪ V = q)
    (hproper : W \ {a, b} ⊆ s \ q) :
    IsFinitePLBallPair (ℝ × ℝ) (s \ (D \ W)) (W ∪ V) ∧
      D ∪ (s \ (D \ W)) = s ∧ D ∩ (s \ (D \ W)) = W ∧
      D ∩ q = U ∧ (s \ (D \ W)) ∩ q = V := by
  obtain ⟨d₀, d₁, hd₀, hd₁, hwhole, hcommon, houter₀, houter₁⟩ :=
    hs.exists_proper_arc_cut hU hV hW hab hUV hrim hproper
  have hD₀ : D = d₀ := hs.subdisks_eq_of_same_rim hD hd₀ hDs
    (subset_union_left.trans hwhole.subset)
  subst d₀
  have hactual : d₁ = s \ (D \ W) := by
    ext x
    have hc : (x ∈ D ∨ x ∈ d₁) ↔ x ∈ s := Set.ext_iff.mp hwhole x
    have hi : (x ∈ D ∧ x ∈ d₁) ↔ x ∈ W := Set.ext_iff.mp hcommon x
    change x ∈ d₁ ↔ x ∈ s ∧ ¬ (x ∈ D ∧ x ∉ W)
    tauto
  rw [hactual] at hd₁ hwhole hcommon houter₁
  exact ⟨hd₁, hwhole, hcommon, houter₀, houter₁⟩





theorem IsFinitePLBallPair.exists_boundary_attached_disk_complement
    {s q D U W : Set E} {a b : E}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s q)
    (hD : IsFinitePLBallPair (ℝ × ℝ) D (U ∪ W)) (hDs : D ⊆ s)
    (hU : IsFinitePLBallPair ℝ U {a, b}) (hUq : U ⊆ q)
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a ≠ b)
    (hproper : W \ {a, b} ⊆ s \ q) :
    ∃ V : Set E, IsFinitePLBallPair ℝ V {a, b} ∧
      U ∪ V = q ∧ U ∩ V = {a, b} ∧
      IsFinitePLBallPair (ℝ × ℝ) (s \ (D \ W)) (W ∪ V) ∧
      D ∪ (s \ (D \ W)) = s ∧ D ∩ (s \ (D \ W)) = W ∧
      D ∩ q = U ∧ (s \ (D \ W)) ∩ q = V := by
  obtain ⟨V, hV, hrim, hUV⟩ := hs.exists_boundary_arc_complement hU hUq hab
  exact ⟨V, hV, hrim, hUV,
    hs.boundary_attached_disk_complement hD hDs hU hV hW hab hUV.subset hrim hproper⟩

end Set

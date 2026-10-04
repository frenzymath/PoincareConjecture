import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLMarkedBallExtension

/-!
# Extending a prescribed map across two actual ball sides

Extend the complete central-disk map across each side ball,
using its complementary frontier disk. Exact intersection and
boundary membership permit finite PL pasting of the two maps.
See Alexander 1924, pp. 6--7, Hudson 1969, pp. 15--19 and
M76 derivation 248.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {V W X Y : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- A prescribed finite PL map of two central disks extends
across both actual ball sides. Each side's whole boundary is
the central disk union a complementary disk, and the supplied
map identifies their full rims. The glued map retains both
side memberships and the complete central-disk restriction.
See Alexander pp. 6--7 and derivation 248. -/
theorem IsFinitePLBallPair.exists_two_side_extension
    {s₀ s₁ b₀ b₁ d q : Set X} {t₀ t₁ B₀ B₁ D Q : Set Y}
    (hs₀ : IsFinitePLBallPair V s₀ (b₀ ∪ d))
    (hs₁ : IsFinitePLBallPair V s₁ (b₁ ∪ d))
    (ht₀ : IsFinitePLBallPair V t₀ (B₀ ∪ D))
    (ht₁ : IsFinitePLBallPair V t₁ (B₁ ∪ D))
    (hb₀ : IsFinitePLBallPair W b₀ q) (hb₁ : IsFinitePLBallPair W b₁ q)
    (hB₀ : IsFinitePLBallPair W B₀ Q) (hB₁ : IsFinitePLBallPair W B₁ Q)
    (hinter : s₀ ∩ s₁ = d) (hInter : t₀ ∩ t₁ = D)
    (hbd₀ : b₀ ∩ d = q) (hbd₁ : b₁ ∩ d = q)
    (hBD₀ : B₀ ∩ D = Q) (hBD₁ : B₁ ∩ D = Q)
    (e : d ≃ₜ D) (he : e.IsFinitePL)
    (hmem : ∀ x : d, (x : X) ∈ q ↔ (e x : Y) ∈ Q) :
    ∃ H : (s₀ ∪ s₁ : Set X) ≃ₜ (t₀ ∪ t₁ : Set Y), H.IsFinitePL ∧
      (∀ x : d, H ⟨x, Or.inl (hs₀.1 (Or.inr x.property))⟩ =
        ⟨e x, Or.inl (ht₀.1 (Or.inr (e x).property))⟩) ∧
      (∀ x : (s₀ ∪ s₁ : Set X), (x : X) ∈ s₀ ↔ (H x : Y) ∈ t₀) ∧
      (∀ x : (s₀ ∪ s₁ : Set X), (x : X) ∈ s₁ ↔ (H x : Y) ∈ t₁) ∧
      (∀ x : (s₀ ∪ s₁ : Set X), (x : X) ∈ d ↔ (H x : Y) ∈ D) := by
  obtain ⟨f₀, hf₀, hf₀d, _, hf₀D⟩ :=
    hs₀.exists_extension_of_boundary_piece ht₀ hb₀ hB₀ hbd₀ hBD₀ e he hmem
  obtain ⟨f₁, hf₁, hf₁d, _, _⟩ :=
    hs₁.exists_extension_of_boundary_piece ht₁ hb₁ hB₁ hbd₁ hBD₁ e he hmem
  have hcontact (x : s₀) : (x : X) ∈ s₁ ↔ (f₀ x : Y) ∈ t₁ := by
    have hx : (x : X) ∈ s₁ ↔ (x : X) ∈ d := by
      rw [← hinter]
      simp only [mem_inter_iff, x.property, true_and]
    have hy : (f₀ x : Y) ∈ D ↔ (f₀ x : Y) ∈ t₁ := by
      rw [← hInter]
      simp only [mem_inter_iff, (f₀ x).property, true_and]
    exact hx.trans ((hf₀D x).trans hy)
  have hagree (x : X) (hx₀ : x ∈ s₀) (hx₁ : x ∈ s₁) :
      (f₀ ⟨x, hx₀⟩ : Y) = f₁ ⟨x, hx₁⟩ := by
    have hxd : x ∈ d := hinter ▸ And.intro hx₀ hx₁
    exact (congrArg (fun y : t₀ => (y : Y)) (hf₀d ⟨x, hxd⟩)).trans
      (congrArg (fun y : t₁ => (y : Y)) (hf₁d ⟨x, hxd⟩)).symm
  obtain ⟨H, hH, hH₀, hH₁⟩ :=
    Homeomorph.exists_union_finitePL f₀ f₁ hf₀ hf₁ hcontact hagree
  have hkeep (x : d) : H ⟨x, Or.inl (hs₀.1 (Or.inr x.property))⟩ =
      ⟨e x, Or.inl (ht₀.1 (Or.inr (e x).property))⟩ := by
    apply Subtype.ext
    exact (hH₀ ⟨x, hs₀.1 (Or.inr x.property)⟩).trans
      (congrArg (fun y : t₀ => (y : Y)) (hf₀d x))
  have hside₀ := H.mem_subset_iff_of_extension f₀ subset_union_left subset_union_left
    (fun x => Subtype.ext (hH₀ x))
  have hside₁ := H.mem_subset_iff_of_extension f₁ subset_union_right subset_union_right
    (fun x => Subtype.ext (hH₁ x))
  refine ⟨H, hH, hkeep, hside₀, hside₁, fun x => ?_⟩
  rw [← hinter, ← hInter, mem_inter_iff, mem_inter_iff, hside₀ x, hside₁ x]

end Set

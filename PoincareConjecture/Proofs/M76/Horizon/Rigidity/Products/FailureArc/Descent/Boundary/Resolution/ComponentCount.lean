import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Strips.ComponentRetention
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.RetainedCopy
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedCounts



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem spanning_resolution_boundary_count_decrease
    {X J : Type*} [Finite J] {S Q₀ Q₁ : Set P2} {f : P2 → X} {τ : C3 → X}
    (c : Bool → P2 → P2) (hcS : ∀ i, MapsTo (c i) source S)
    (hci : ∀ i, InjOn (c i) source)
    (hdis : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfull : S ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source)
    (houter : ∀ i z, z ∈ source → (c i z ∈ Q₀ ↔ z.1 = 0))
    (E : Fin 2 → Set P2) (H : ∀ j, Sq ≃ₜ E j) (sign : Fin 2 → Bool → Bool)
    (hES : ∀ j, E j ⊆ S) (hEdis : Disjoint (E 0) (E 1))
    (hcover : (c false '' source ∪ c true '' source) ∪ (E 0 ∪ E 1) = S)
    (hcontact : ∀ j i, E j ∩ (c i '' source) = c i '' arm (farArmParameter (sign j i)))
    (hHo : ∀ j (z : Sq), (H j z : P2) ∈ Q₀ ↔ (z : P2).2 = 0)
    (hHi : ∀ j (z : Sq), (H j z : P2) ∈ Q₁ ↔ (z : P2).2 = 1)
    (U : J → Set P2) (mate : J → J) (partner : doubleLocusOn f S → doubleLocusOn f S)
    (hUcover : ⋃ k, U k = doubleLocusOn f S)
    (hcompact : ∀ k, IsCompact (U k)) (hconnected : ∀ k, IsConnected (U k))
    (hdisjoint : Pairwise (fun k l ↦ Disjoint (U k) (U l)))
    (hpartner : ∀ x : doubleLocusOn f S, f x = f (partner x))
    (hne : ∀ x : doubleLocusOn f S, (x : P2) ≠ partner x)
    (hunique : ∀ (x : doubleLocusOn f S) y, y ∈ S → f x = f y → (x : P2) ≠ y →
      y = (partner x : P2))
    (hmate : ∀ k (x : doubleLocusOn f S), (x : P2) ∈ U k → (partner x : P2) ∈ U (mate k))
    (selected : Bool → J) (hcenter : ∀ i, c i '' arm 0 = U (selected i))
    {maps : Fin 2 → Fin 2 → P2 → X} {g : Fin 2 → P2 → X}
    (C : ∀ j, AnnulusSquareCopies (maps j) (g j))
    (hdouble : ∀ j, {x : P2 | x ∈ squareAnnulus 8 1 ∧
        ∃ y ∈ squareAnnulus 8 1, y ≠ x ∧ g j y = g j x} =
      (fun z : Sq ↦ ((C j).chart 0 z : P2)) ''
        {u : Sq | ∃ v : Sq, v ≠ u ∧ f (H j v) = f (H j u)}) :
    ∀ j, doubleBoundaryComponentCount (g j) (squareAnnulus 8 1)
        {x | depth 8 x = -1 ∨ depth 8 x = 1} < doubleBoundaryComponentCount f S (Q₀ ∪ Q₁) ∧
      doubleInteriorComponentCount (g j) (squareAnnulus 8 1)
        {x | depth 8 x = -1 ∨ depth 8 x = 1} ≤ doubleInteriorComponentCount f S (Q₀ ∪ Q₁) := by
  have hU (k : J) : U k ⊆ doubleLocusOn f S := by
    rw [← hUcover]
    exact subset_iUnion U k
  obtain ⟨hwhole, hremoved⟩ := spanning_strip_whole_component_retention
    c hcS hci hdis hτ h0 h1 hfull E H sign hEdis hcover hcontact U hU
      hconnected hdisjoint selected hcenter
  have hiQ : (U (selected false) ∩ (Q₀ ∪ Q₁)).Nonempty := by
    refine ⟨c false (0, 0), ?_, Or.inl ?_⟩
    · exact (hcenter false).subset ⟨(0, 0), ⟨by norm_num, rfl⟩, rfl⟩
    · exact (houter false (0, 0) (by norm_num [source])).mpr rfl
  intro j
  exact retained_double_component_counts_decrease U mate partner rfl hUcover
    hcompact hconnected hdisjoint hpartner hne hunique hmate (hES j) (hwhole j)
    ((C j).retainedDiskCopy (H j)) ((C j).retainedDiskCopy_injective (H j))
    ((C j).retainedDiskCopy_continuous (H j))
    ((C j).double_locus_eq_original_retained (H j) f (hdouble j))
    ((C j).retainedDiskCopy_boundary_iff (H j) (hHo j) (hHi j))
    (selected false) hiQ (hremoved j false).2

end PoincareConjecture.M76.Dehn

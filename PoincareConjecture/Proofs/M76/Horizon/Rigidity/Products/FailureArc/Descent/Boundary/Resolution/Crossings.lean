import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Resolution.OpenCopy
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CrossingFamily

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem spanning_resolution_raw_source_crossings
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    {S K L : Set P2} {old g : P2 → X} {τ : C3 → X} {R : Set X}
    (c : Bool → P2 → P2)
    (hc : ∀ i, ContinuousOn (c i) source) (hcS : ∀ i, MapsTo (c i) source S)
    (hci : ∀ i, InjOn (c i) source)
    (hdis : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (h0 : ∀ p ∈ source, old (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, old (c true p) = τ ((p.2, -p.2), p.1))
    (hfull : S ∩ old ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source)
    (H : Sq ≃ₜ K) (hL : IsClosed L) (hKS : K ⊆ S) (hKL : Disjoint K L)
    (hcover : (c false '' source ∪ c true '' source) ∪ (K ∪ L) = S)
    (sign : Bool → Bool)
    (hcontact : ∀ i, K ∩ (c i '' source) = c i '' arm (farArmParameter (sign i)))
    (hleft : ∀ t : I, (H ⟨(0, t), by norm_num, t.property⟩ : P2) =
      c false (t, farArmParameter (sign false)))
    (hright : ∀ t : I, (H ⟨(1, t), by norm_num, t.property⟩ : P2) =
      c true (t, farArmParameter (sign true)))
    {f : Fin 2 → P2 → X} (C : AnnulusSquareCopies f g)
    (hval : ∀ z : Sq, f 0 z = old (H z))
    (hdouble : {x : P2 | x ∈ squareAnnulus 8 1 ∧
        ∃ y ∈ squareAnnulus 8 1, y ≠ x ∧ g y = g x} =
      (fun z : Sq ↦ (C.chart 0 z : P2)) ''
        {u : Sq | ∃ v : Sq, v ≠ u ∧ old (H v) = old (H u)})
    (hS : IsCompact S) (hold : ContinuousOn old S)
    (hg : ContinuousOn g (squareAnnulus 8 1))
    (p : doubleLocusOn old S → doubleLocusOn old S)
    (hunique : ∀ (x : doubleLocusOn old S) (y : P2), y ∈ S →
      old x = old y → (x : P2) ≠ y → y = (p x : P2))
    (hcross : ∀ x ∈ S, ∀ y ∈ S, old x = old y → x ≠ y →
      Nonempty (RawSourceCrossing e old S R x y)) :
    ∀ x ∈ squareAnnulus 8 1, ∀ y ∈ squareAnnulus 8 1, g x = g y → x ≠ y →
      Nonempty (RawSourceCrossing e g (squareAnnulus 8 1) R x y) := by
  obtain ⟨U, V, J, hUK, hVT, hU, hV, _, hkeep, _, hcontains⟩ :=
    exists_spanning_resolution_open_copy c hc hcS hci hdis hτ h0 h1 hfull
      H hL hKS hKL hcover sign hcontact hleft hright C hval hdouble
  exact Annuli.raw_source_crossings_of_retained_open_copy hS C.isCompact_source
    (hUK.trans hKS) hVT hU hV hold hg J hkeep p hunique hcontains hcross

end PoincareConjecture.M76.Dehn

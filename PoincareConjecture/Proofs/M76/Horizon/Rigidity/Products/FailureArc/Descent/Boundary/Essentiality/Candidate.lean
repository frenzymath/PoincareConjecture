import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.OriginalWord
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.PastedRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.RetainedPath
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.Map



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)
local notation "O" => (Set.ofPred (fun x : P2 ↦ x ∈ squareAnnulus 8 1 ∧ depth 8 x = -1))

theorem exists_essential_spanning_candidate
    {X : Type*} [TopologicalSpace X] {R : Set X}
    {T Q S : Set P2} (hT : IsFinitePLBallPair P2 T Q) (hQS : Q ⊆ S)
    (c : Bool → P2 → P2) (hc : ∀ i, ContinuousOn (c i) source)
    (hQ : ∀ i z, z ∈ source → (c i z ∈ Q ↔ z.1 = 0))
    (E : Fin 2 → Set P2) (hEdis : Disjoint (E 0) (E 1))
    (hcover : (c false '' source ∪ c true '' source) ∪ (E 0 ∪ E 1) = S)
    (positive : Bool → Bool)
    (H : ∀ j, Sq ≃ₜ E j) (hH : ∀ j, (H j).IsFinitePL)
    (hHQ : ∀ j (z : Sq), (H j z : P2) ∈ Q ↔ (z : P2).2 = 0)
    (hcontact : ∀ j i, E j ∩ (c i '' source) =
      c i '' arm (farArmParameter (if j = 0 then positive i else !(positive i))))
    (hleft : ∀ j (t : I), (H j ⟨(0, t), by norm_num, t.property⟩ : P2) =
      c false (t, farArmParameter (if j = 0 then positive false else !(positive false))))
    (hright : ∀ j (t : I), (H j ⟨(1, t), by norm_num, t.property⟩ : P2) =
      c true (t, farArmParameter (if j = 0 then positive true else !(positive true))))
    (old : P2 → X) (hold : ContinuousOn old Q) (holdR : MapsTo old Q R)
    (rim : C(Q, R)) (hrim : ∀ z : Q, (rim z : X) = old z)
    (hnon : ¬ rim.Nullhomotopic)
    (τ : C3 → X) (hτ : ContinuousOn τ tube) (hτR : MapsTo τ tube R)
    (h0 : ∀ p ∈ source, old (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, old (c true p) = τ ((p.2, -p.2), p.1))
    (f : Fin 2 → Fin 2 → P2 → X) (g : Fin 2 → P2 → X)
    (C : ∀ j, AnnulusSquareCopies (f j) (g j))
    (hf0 : ∀ j (z : Sq), f j 0 z = old (H j z))
    (hf1 : ∀ j (t : I), f j 1 (t, 0) = τ
      (tubeArmOrientation (!(if j = 0 then positive false else !(positive false)))
        (!(if j = 0 then positive true else !(positive true))) (resolvingSquare true (t, 0))))
    (hg : ∀ j, ContinuousOn (g j) (squareAnnulus 8 1))
    (hgR : ∀ j, MapsTo (g j) (squareAnnulus 8 1) R) :
    ∃ (j : Fin 2) (newrim : C(O, R)),
      (∀ z : O, (newrim z : X) = g j z) ∧ ¬ newrim.Nullhomotopic := by
  obtain ⟨A, hA⟩ := exists_spanning_retained_rim_path c positive (H 0) (hHQ 0)
    (hleft 0) (hright 0) old hold holdR τ hτ hτR h0 h1
  obtain ⟨B, hB⟩ := exists_spanning_retained_rim_path c (fun i ↦ !(positive i))
    (H 1) (hHQ 1) (hleft 1) (hright 1) old hold holdR τ hτ hτR h0 h1
  have hword := nonnull_spanning_word_of_original_rim hT hQS c hc hQ hEdis hcover
    positive (hcontact 0) (H 0) (hH 0) (hHQ 0) (hleft 0) (hright 0)
    (H 1) (hHQ 1) (hleft 1) (hright 1) old hold holdR rim hrim hnon
      τ hτ hτR h0 h1 A B hA hB
  rcases spanning_end_selects_nonnull_rim τ hτ hτR positive A B hword with hnonA | hnonB
  · obtain ⟨newrim, hval, hnon⟩ := (C 0).exists_nonnull_outer_rim_of_paths (hg 0) (hgR 0)
      A ((spanningResolvingEndPath positive).map (spanningEndMap τ hτ hτR).continuous)
      (fun t ↦ (hA t).trans (hf0 0 ⟨(t, 0), t.property, by norm_num⟩).symm)
      (fun t ↦ (hf1 0 t).symm) hnonA
    exact ⟨0, newrim, hval, hnon⟩
  · obtain ⟨newrim, hval, hnon⟩ := (C 1).exists_nonnull_outer_rim_of_paths (hg 1) (hgR 1)
      B ((spanningResolvingEndPath (fun i ↦ !(positive i))).map
        (spanningEndMap τ hτ hτR).continuous)
      (fun t ↦ (hB t).trans (hf0 1 ⟨(t, 0), t.property, by norm_num⟩).symm)
      (fun t ↦ (hf1 1 t).symm) hnonB
    exact ⟨1, newrim, hval, hnon⟩

end PoincareConjecture.M76.Dehn

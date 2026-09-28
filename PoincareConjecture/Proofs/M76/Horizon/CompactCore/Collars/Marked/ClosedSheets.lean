import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue








set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

private theorem mem_closed_iff_of_preconnected
    {X : Type*} [TopologicalSpace X] {s S T : Set X}
    (hs : IsPreconnected s) (hS : IsClosed S) (hT : IsClosed T)
    (hcover : s ⊆ S ∪ T) (havoid : ∀ x ∈ s, x ∉ S ∩ T)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : x ∈ S ↔ y ∈ S := by
  have transfer {a b : X} (ha : a ∈ s) (hb : b ∈ s) (haS : a ∈ S) : b ∈ S := by
    by_contra hbS
    obtain ⟨z, hzs, hzS, hzT⟩ := isPreconnected_closed_iff.mp hs S T hS hT hcover
      ⟨a, ha, haS⟩ ⟨b, hb, (hcover hb).resolve_left hbS⟩
    exact havoid z hzs ⟨hzS, hzT⟩
  exact ⟨transfer hx hy, transfer hy hx⟩



theorem exists_closed_strip_preserving_closed_sheets
    {A X : Type*} [TopologicalSpace A] [CompactSpace A] [TopologicalSpace X]
    {f : A × Icc (-1 : ℝ) 1 → X} (hf : Continuous f)
    {S T : Set X} (hS : IsClosed S) (hT : IsClosed T)
    (hcover : ∀ p, f p ∈ S ∪ T)
    {U : Set A} (hU : IsOpen U)
    (hcentral : ∀ a, f (a, ⟨0, by norm_num⟩) ∈ S ∩ T → a ∈ U)
    {r : ℝ} (hr : 0 < r)
    (hlocal : ∀ a ∈ U, ∀ t : Icc (-1 : ℝ) 1, |(t : ℝ)| ≤ r →
      (f (a, t) ∈ S ∩ T ↔ f (a, ⟨0, by norm_num⟩) ∈ S ∩ T)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ δ ≤ r ∧
      ∀ (a : A) (t : Icc (-1 : ℝ) 1), |(t : ℝ)| ≤ δ →
        (f (a, t) ∈ S ↔ f (a, ⟨0, by norm_num⟩) ∈ S) ∧
        (f (a, t) ∈ T ↔ f (a, ⟨0, by norm_num⟩) ∈ T) := by
  classical
  let I := Icc (-1 : ℝ) 1
  let zero : I := ⟨0, by dsimp [I]; norm_num⟩
  let W : Set (A × I) := Prod.fst ⁻¹' U ∪ f ⁻¹' (S ∩ T)ᶜ
  have hW : IsOpen W :=
    (hU.preimage continuous_fst).union (((hS.inter hT).isOpen_compl).preimage hf)
  have hzero (a : A) : (a, zero) ∈ W := by
    by_cases h : f (a, zero) ∈ S ∩ T
    · exact Or.inl (hcentral a h)
    · exact Or.inr h
  obtain ⟨ε, hε, hεsmall, hthin⟩ :=
    continuous_id.exists_closed_strip_subset hW hzero
  let δ := min ε r
  have hδ : 0 < δ := lt_min hε hr
  have hδε : δ ≤ ε := min_le_left _ _
  have hδr : δ ≤ r := min_le_right _ _
  have hδsmall : δ ≤ 1 / 2 := hδε.trans hεsmall
  have hseam (a : A) (t : I) (ht : |(t : ℝ)| ≤ δ) :
      f (a, t) ∈ S ∩ T ↔ f (a, zero) ∈ S ∩ T := by
    by_cases ha : a ∈ U
    · exact hlocal a ha t (ht.trans hδr)
    · have hnot : f (a, t) ∉ S ∩ T := (hthin a t (ht.trans hδε)).resolve_left ha
      exact iff_of_false hnot (fun h => ha (hcentral a h))
  refine ⟨δ, hδ, hδsmall, hδr, ?_⟩
  intro a t ht
  by_cases hcenter : f (a, zero) ∈ S ∩ T
  · have hmarked := (hseam a t ht).mpr hcenter
    exact ⟨iff_of_true hmarked.1 hcenter.1, iff_of_true hmarked.2 hcenter.2⟩
  let lo : I := ⟨-δ, by constructor <;> linarith⟩
  let hi : I := ⟨δ, by constructor <;> linarith⟩
  let g : I → X := fun v => f (a, v)
  have hg : Continuous g := hf.comp (continuous_const.prodMk continuous_id)
  have hinterval : IsPreconnected (Icc lo hi) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have himage : Subtype.val '' Icc lo hi = Icc (-δ) δ := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hv
        exact ⟨⟨v, by constructor <;> linarith [hv.1, hv.2]⟩, hv, rfl⟩
    rw [himage]
    exact isPreconnected_Icc
  have hconn : IsPreconnected (g '' Icc lo hi) := hinterval.image g hg.continuousOn
  have hcover' : g '' Icc lo hi ⊆ S ∪ T := by
    rintro _ ⟨v, _, rfl⟩
    exact hcover (a, v)
  have havoid : ∀ x ∈ g '' Icc lo hi, x ∉ S ∩ T := by
    rintro _ ⟨v, hv, rfl⟩ h
    exact hcenter ((hseam a v (abs_le.mpr hv)).mp h)
  have ht' : g t ∈ g '' Icc lo hi := mem_image_of_mem g (abs_le.mp ht)
  have hz' : g zero ∈ g '' Icc lo hi := mem_image_of_mem g ⟨by change -δ ≤ 0; linarith,
    by change (0 : ℝ) ≤ δ; linarith⟩
  exact ⟨mem_closed_iff_of_preconnected hconn hS hT hcover' havoid ht' hz',
    mem_closed_iff_of_preconnected hconn hT hS
      (by simpa only [union_comm] using hcover')
      (by simpa only [inter_comm] using havoid) ht' hz'⟩

end PoincareConjecture.M76

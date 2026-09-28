import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Strips.Construction

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

private theorem connected_subset_closed_side
    {E : Type*} [TopologicalSpace E] {A B T : Set E}
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B)
    (hT : IsPreconnected T) (hcover : T ⊆ A ∪ B)
    (hmeet : (T ∩ A).Nonempty) : T ⊆ A := by
  intro x hx
  rcases hcover hx with ha | hb
  · exact ha
  · obtain ⟨z, _, hzA, hzB⟩ :=
      isPreconnected_closed_iff.mp hT A B hA hB hcover hmeet ⟨x, hx, hb⟩
    exact (disjoint_left.mp hdis hzA hzB).elim

theorem proper_strip_separate_rims
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : (ℝ × ℝ) → E} {Q₀ Q₁ : Set E}
    (hc : ContinuousOn c source)
    (hQ₀ : IsClosed Q₀) (hQ₁ : IsClosed Q₁) (hdis : Disjoint Q₀ Q₁)
    (hfront : ∀ p ∈ source, c p ∈ Q₀ ∪ Q₁ ↔ p.1 = 0 ∨ p.1 = 1)
    (h0 : c (0, 0) ∈ Q₀) (h1 : c (1, 0) ∈ Q₁) :
    (∀ p ∈ source, c p ∈ Q₀ ↔ p.1 = 0) ∧
    (∀ p ∈ source, c p ∈ Q₁ ↔ p.1 = 1) := by
  have hend (t : ℝ) (ht : t = 0 ∨ t = 1) {A B : Set E}
      (hA : IsClosed A) (hB : IsClosed B) (hd : Disjoint A B)
      (heq : A ∪ B = Q₀ ∪ Q₁) (hcenter : c (t, 0) ∈ A) :
      ∀ y ∈ Icc (-1 : ℝ) 1, c (t, y) ∈ A := by
    have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> norm_num
    let g : Icc (-1 : ℝ) 1 → E := fun y => c (t, y)
    have hg : Continuous g := hc.comp_continuous
      (continuous_const.prodMk continuous_subtype_val) (fun y => ⟨htI, y.property⟩)
    let : PreconnectedSpace (Icc (-1 : ℝ) 1) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have hconn : IsPreconnected (g '' univ) := isPreconnected_univ.image g hg.continuousOn
    have hcover : g '' univ ⊆ A ∪ B := by
      rintro _ ⟨y, _, rfl⟩
      rw [heq]
      exact (hfront (t, y) ⟨htI, y.property⟩).mpr ht
    have hsub := connected_subset_closed_side hA hB hd hconn hcover
      (show ((g '' univ) ∩ A).Nonempty from
        ⟨c (t, 0), ⟨⟨0, by norm_num⟩, mem_univ _, rfl⟩, hcenter⟩)
    intro y hy
    exact hsub ⟨⟨y, hy⟩, mem_univ _, rfl⟩
  have hend0 := hend 0 (Or.inl rfl) hQ₀ hQ₁ hdis rfl h0
  have hend1 := hend 1 (Or.inr rfl) hQ₁ hQ₀ hdis.symm (union_comm _ _) h1
  constructor
  · intro p hp
    constructor
    · intro h
      rcases (hfront p hp).mp (Or.inl h) with ht | ht
      · exact ht
      · exact (disjoint_left.mp hdis h (by simpa only [← ht, Prod.eta] using hend1 p.2 hp.2)).elim
    · intro ht
      simpa only [← ht, Prod.eta] using hend0 p.2 hp.2
  · intro p hp
    constructor
    · intro h
      rcases (hfront p hp).mp (Or.inr h) with ht | ht
      · exact (disjoint_left.mp hdis (by simpa only [← ht, Prod.eta] using hend0 p.2 hp.2) h).elim
      · exact ht
    · intro ht
      simpa only [← ht, Prod.eta] using hend1 p.2 hp.2

end PoincareConjecture.M76.Dehn.Annuli

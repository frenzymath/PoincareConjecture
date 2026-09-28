import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.StripComplement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.EndpointOrder
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Strips.RimEnds



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem strip_complement_rim_interval
    {B Q A E : Set P2} (hB : IsFinitePLBallPair P2 B Q) (hQA : Q ⊆ A)
    {c : P2 → P2} (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    {t : ℝ} (ht : t = 0 ∨ t = 1)
    (htrace : ∀ p ∈ source, c p ∈ Q ↔ p.1 = t)
    (hcover : E ∪ c '' source = A)
    (hcontact : E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1)) :
    IsFinitePLBallPair ℝ (E ∩ Q) {c (t,-1),c (t,1)} := by
  have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht with rfl|rfl <;> norm_num
  have hendS := spanningStripEnd_subset_source htI
  have hm : (t,-1) ∈ source := ⟨htI,by norm_num⟩
  have hp : (t,1) ∈ source := ⟨htI,by norm_num⟩
  have hne : c (t,-1) ≠ c (t,1) := by
    intro h
    have hh := congrArg Prod.snd (hci hm hp h)
    norm_num at hh
  have hU : IsFinitePLBallPair ℝ (c '' spanningStripEnd t) {c (t,-1),c (t,1)} := by
    simpa only [image_pair] using (spanningStripEnd_ball t).image_of_subset hc hendS hci
  have hUQ : c '' spanningStripEnd t ⊆ Q := by
    rintro _ ⟨p,hp,rfl⟩
    exact (htrace p (hendS hp)).mpr hp.1
  obtain ⟨Z,hZ,hUZ,hmeet⟩ := hB.exists_boundary_arc_complement hU hUQ hne
  have hendsE : ({c (t,-1),c (t,1)} : Set P2) ⊆ E := by
    rintro x (rfl|rfl)
    · exact (hcontact.symm.subset ⟨(t,-1),Or.inl ⟨htI,rfl⟩,rfl⟩).1
    · exact (hcontact.symm.subset ⟨(t,1),Or.inr ⟨htI,rfl⟩,rfl⟩).1
  have hEU : E ∩ (c '' spanningStripEnd t) ⊆ {c (t,-1),c (t,1)} := by
    rintro _ ⟨hx,⟨p,hp,rfl⟩⟩
    obtain ⟨q,hq,heq⟩ := hcontact.subset ⟨hx,⟨p,hendS hp,rfl⟩⟩
    have hqS : q ∈ source := by
      rcases hq with h|h <;> exact ⟨h.1,by rw [show q.2 = _ from h.2]; norm_num⟩
    have heqp : q = p := hci hqS (hendS hp) heq
    subst q
    rcases hq with h|h
    · exact Or.inl (congrArg c (Prod.ext hp.1 h.2))
    · exact Or.inr (congrArg c (Prod.ext hp.1 h.2))
  have hEQ : E ∩ Q = Z := by
    ext x
    constructor
    · rintro ⟨hx,hxQ⟩
      rcases hUZ.symm.subset hxQ with hxU|hxZ
      · exact hZ.1 (hEU ⟨hx,hxU⟩)
      · exact hxZ
    · intro hxZ
      have hxQ := hUZ.subset (Or.inr hxZ)
      refine ⟨?_,hxQ⟩
      rcases hcover.symm.subset (hQA hxQ) with hxE|⟨p,hp,hpx⟩
      · exact hxE
      · have hpQ : c p ∈ Q := hpx.symm ▸ hxQ
        have hxU : x ∈ c '' spanningStripEnd t :=
          ⟨p,⟨(htrace p hp).mp hpQ,hp.2⟩,hpx⟩
        exact hendsE (hmeet.subset ⟨hxU,hxZ⟩)
  exact hEQ.symm ▸ hZ

theorem strip_complement_rim_markings
    {B₀ B₁ Q₀ Q₁ A E : Set P2}
    (hB₀ : IsFinitePLBallPair P2 B₀ Q₀) (hB₁ : IsFinitePLBallPair P2 B₁ Q₁)
    (hQ₀A : Q₀ ⊆ A) (hQ₁A : Q₁ ⊆ A) (hdis : Disjoint Q₀ Q₁)
    {c : P2 → P2} (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hproper : ∀ p ∈ source, c p ∈ Q₀ ∪ Q₁ ↔ p.1 = 0 ∨ p.1 = 1)
    (houter : (c '' arm 0 ∩ Q₀).Nonempty) (hinner : (c '' arm 0 ∩ Q₁).Nonempty)
    (hcover : E ∪ c '' source = A)
    (hcontact : E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1)) :
    ∃ t₀ t₁ : ℝ, ((t₀ = 0 ∧ t₁ = 1) ∨ (t₀ = 1 ∧ t₁ = 0)) ∧
      (∀ p ∈ source, c p ∈ Q₀ ↔ p.1 = t₀) ∧
      (∀ p ∈ source, c p ∈ Q₁ ↔ p.1 = t₁) ∧
      IsFinitePLBallPair ℝ (E ∩ Q₀) {c (t₀,-1),c (t₀,1)} ∧
      IsFinitePLBallPair ℝ (E ∩ Q₁) {c (t₁,-1),c (t₁,1)} := by
  have hQ₀ : IsClosed Q₀ := hB₀.frontier_eq_of_finrank_eq rfl ▸ isClosed_frontier
  have hQ₁ : IsClosed Q₁ := hB₁.frontier_eq_of_finrank_eq rfl ▸ isClosed_frontier
  rcases spanning_center_endpoint_order c hdis hproper houter hinner with horder|horder
  · obtain ⟨h0,h1⟩ := proper_strip_separate_rims hc.continuousOn hQ₀ hQ₁ hdis
      hproper horder.1 horder.2
    exact ⟨0,1,Or.inl ⟨rfl,rfl⟩,h0,h1,
      strip_complement_rim_interval hB₀ hQ₀A hc hci (Or.inl rfl) h0 hcover hcontact,
      strip_complement_rim_interval hB₁ hQ₁A hc hci (Or.inr rfl) h1 hcover hcontact⟩
  · have hp : ∀ p ∈ source, c p ∈ Q₁ ∪ Q₀ ↔ p.1 = 0 ∨ p.1 = 1 := by
      simpa only [union_comm] using hproper
    obtain ⟨h0,h1⟩ := proper_strip_separate_rims hc.continuousOn hQ₁ hQ₀ hdis.symm
      hp horder.1 horder.2
    exact ⟨1,0,Or.inr ⟨rfl,rfl⟩,h1,h0,
      strip_complement_rim_interval hB₀ hQ₀A hc hci (Or.inr rfl) h1 hcover hcontact,
      strip_complement_rim_interval hB₁ hQ₁A hc hci (Or.inl rfl) h0 hcover hcontact⟩

end PoincareConjecture.M76.Dehn.Annuli

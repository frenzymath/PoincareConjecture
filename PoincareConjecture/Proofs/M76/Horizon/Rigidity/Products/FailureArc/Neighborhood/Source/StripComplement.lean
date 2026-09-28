import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.StripBoundary

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem exists_spanning_strip_complement
    {S T : Set P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (c : P2 → P2) (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hin : MapsTo c source (T \ interior S))
    (houter : ∀ p ∈ source, c p ∈ frontier T ↔ p.1 = 0)
    (hinner : ∀ p ∈ source, c p ∈ frontier S ↔ p.1 = 1) :
    ∃ E : Set P2, IsFinitePLBallPair P2 E (frontier E) ∧
      E ∪ c '' source = T \ interior S ∧
      E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1) ∧
      E ⊆ T \ interior S ∧
      frontier E = (E ∩ (frontier T ∪ frontier S)) ∪ c '' (arm (-1) ∪ arm 1) := by
  have hsub (t : ℝ) (ht : t = 0 ∨ t = 1) : spanningStripEnd t ⊆ source :=
    spanningStripEnd_subset_source (by rcases ht with rfl|rfl <;> norm_num)
  have hball : IsFinitePLBallPair P2 (c '' source) (c '' frontier source) :=
    spanningStripSource_ball.image hc hci
  have hfront : frontier (c '' source) = c '' frontier source :=
    hball.frontier_eq_of_finrank_eq rfl
  have hD : IsFinitePLBallPair P2 (c '' source) (frontier (c '' source)) :=
    hfront ▸ hball
  have hend (t : ℝ) (ht : t = 0 ∨ t = 1) :
      IsFinitePLBallPair ℝ (c '' spanningStripEnd t) {c (t,-1),c (t,1)} := by
    simpa only [image_pair] using (spanningStripEnd_ball t).image_of_subset hc (hsub t ht) hci
  have hne (t : ℝ) (ht : t = 0 ∨ t = 1) : c (t,-1) ≠ c (t,1) := by
    intro heq
    have heq' := hci (x₁ := (t,-1)) (x₂ := (t,1))
      (hsub t ht ⟨rfl,by norm_num⟩) (hsub t ht ⟨rfl,by norm_num⟩) heq
    have := congrArg Prod.snd heq'
    norm_num at this
  have hDS : S ∩ c '' source = c '' spanningStripEnd 1 := by
    ext x
    constructor
    · rintro ⟨hx,⟨p,hp,rfl⟩⟩
      exact ⟨p,⟨(hinner p hp).mp ⟨subset_closure hx,(hin hp).2⟩,hp.2⟩,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      have hpS := hsub 1 (Or.inr rfl) hp
      exact ⟨hS.1 ((hinner p hpS).mpr hp.1),⟨p,hpS,rfl⟩⟩
  have hDU : (c '' source) ∩ frontier T = c '' spanningStripEnd 0 := by
    ext x
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hx⟩
      exact ⟨p,⟨(houter p hp).mp hx,hp.2⟩,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      have hpS := hsub 0 (Or.inl rfl) hp
      exact ⟨⟨p,hpS,rfl⟩,(houter p hpS).mpr hp.1⟩
  obtain ⟨E,hE,hcover,hmeet,hEin,hErim⟩ := exists_shell_complement_of_spanning_disk hS hT hD
    hST (fun _ hx => (hin.image_subset hx).1) (hend 0 (Or.inl rfl))
    (hend 1 (Or.inr rfl)) (hne 0 (Or.inl rfl)) (hne 1 (Or.inr rfl)) hDS
    (by rintro x ⟨p,hp,rfl⟩; exact (hinner p (hsub 1 (Or.inr rfl) hp)).mpr hp.1)
    (by rw [hfront]; exact image_mono (spanningStripEnd_subset_frontier (Or.inr rfl))) hDU
  suffices hcontact : E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1) by
    exact ⟨E,hE,hcover,hcontact,hEin,hcontact ▸ hErim⟩
  rw [hmeet,hfront]
  have hpoint {p : P2} (hp : p ∈ source) (t : ℝ) (ht : t = 0 ∨ t = 1) :
      c p ∈ ({c (t,-1),c (t,1)} : Set P2) ↔ p = (t,-1) ∨ p = (t,1) := by
    constructor
    · rintro (h|h)
      · exact Or.inl (hci hp (hsub t ht ⟨rfl,by norm_num⟩) h)
      · exact Or.inr (hci hp (hsub t ht ⟨rfl,by norm_num⟩) h)
    · rintro (rfl|rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  ext x
  constructor
  · rintro ⟨⟨p,hp,rfl⟩,havoid⟩
    obtain ⟨hpS,hpboundary⟩ := (spanningStripSource_frontier p).mp hp
    refine ⟨p,?_,rfl⟩
    have hside : p.2 = -1 ∨ p.2 = 1 := by
      rcases hpboundary with ht|ht|hu|hu
      · have hpE : p ∈ spanningStripEnd 0 := ⟨ht,hpS.2⟩
        have hpends : c p ∈ ({c (0,-1),c (0,1)} : Set P2) :=
          by_contra fun hn => havoid (Or.inr ⟨⟨p,hpE,rfl⟩,hn⟩)
        rcases (hpoint hpS 0 (Or.inl rfl)).mp hpends with h|h
        · exact Or.inl (congrArg Prod.snd h)
        · exact Or.inr (congrArg Prod.snd h)
      · have hpE : p ∈ spanningStripEnd 1 := ⟨ht,hpS.2⟩
        have hpends : c p ∈ ({c (1,-1),c (1,1)} : Set P2) :=
          by_contra fun hn => havoid (Or.inl ⟨⟨p,hpE,rfl⟩,hn⟩)
        rcases (hpoint hpS 1 (Or.inr rfl)).mp hpends with h|h
        · exact Or.inl (congrArg Prod.snd h)
        · exact Or.inr (congrArg Prod.snd h)
      · exact Or.inl hu
      · exact Or.inr hu
    exact hside.elim (fun h => Or.inl ⟨hpS.1,h⟩) (fun h => Or.inr ⟨hpS.1,h⟩)
  · rintro ⟨p,hp,rfl⟩
    have hpS : p ∈ source := by
      rcases hp with h|h <;> exact ⟨h.1,by rw [show p.2 = _ from h.2]; norm_num⟩
    have hside : p.2 = -1 ∨ p.2 = 1 := hp.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
    refine ⟨⟨p,(spanningStripSource_frontier p).mpr ⟨hpS,Or.inr (Or.inr hside)⟩,rfl⟩,?_⟩
    rintro (⟨⟨q,hq,hqp⟩,hn⟩|⟨⟨q,hq,hqp⟩,hn⟩)
    · have heq := hci (hsub 1 (Or.inr rfl) hq) hpS hqp
      have ht : p.1 = 1 := heq ▸ hq.1
      apply hn
      exact (hpoint hpS 1 (Or.inr rfl)).mpr
        (hside.elim (fun h => Or.inl (Prod.ext ht h)) (fun h => Or.inr (Prod.ext ht h)))
    · have heq := hci (hsub 0 (Or.inl rfl) hq) hpS hqp
      have ht : p.1 = 0 := heq ▸ hq.1
      apply hn
      exact (hpoint hpS 0 (Or.inl rfl)).mpr
        (hside.elim (fun h => Or.inl (Prod.ext ht h)) (fun h => Or.inr (Prod.ext ht h)))

end PoincareConjecture.M76.Dehn.Annuli

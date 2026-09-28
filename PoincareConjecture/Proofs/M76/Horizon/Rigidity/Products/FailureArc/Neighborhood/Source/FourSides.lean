import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.RimIntervals








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem strip_complement_rim_arm_inter
    {E Q : Set P2} {c : P2 → P2} {t v : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v = -1 ∨ v = 1)
    (htrace : ∀ p ∈ source, c p ∈ Q ↔ p.1 = t)
    (hcontact : E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1)) :
    (E ∩ Q) ∩ (c '' arm v) = {c (t,v)} := by
  have hvI : v ∈ Icc (-1 : ℝ) 1 := by rcases hv with rfl|rfl <;> norm_num
  ext x
  constructor
  · rintro ⟨⟨_,hxQ⟩,⟨p,hp,rfl⟩⟩
    have hpS : p ∈ source := ⟨hp.1,(hp.2 : p.2 = v) ▸ hvI⟩
    exact congrArg c (Prod.ext ((htrace p hpS).mp hxQ) hp.2)
  · rintro rfl
    have hp : (t,v) ∈ arm (-1) ∪ arm 1 :=
      hv.elim (fun h => Or.inl ⟨ht,h⟩) (fun h => Or.inr ⟨ht,h⟩)
    exact ⟨⟨(hcontact.symm.subset ⟨(t,v),hp,rfl⟩).1,
      (htrace (t,v) ⟨ht,hvI⟩).mpr rfl⟩,⟨(t,v),⟨ht,rfl⟩,rfl⟩⟩

theorem strip_far_arm_ball
    {c : P2 → P2} (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    {v : ℝ} (hv : v = -1 ∨ v = 1) :
    IsFinitePLBallPair ℝ (c '' arm v) {c (0,v),c (1,v)} := by
  have hsub : arm v ⊆ source := by
    rintro p ⟨hp,hq⟩
    refine ⟨hp,?_⟩
    rw [show p.2 = v from hq]
    rcases hv with rfl|rfl <;> norm_num
  simpa only [image_pair] using (exists_arm_parameter v).1.image_of_subset hc hsub hci

theorem strip_far_arms_disjoint
    {c : P2 → P2} (hci : InjOn c source) :
    Disjoint (c '' arm (-1)) (c '' arm 1) := by
  apply disjoint_left.mpr
  rintro _ ⟨p,hp,rfl⟩ ⟨q,hq,hqp⟩
  have hpS : p ∈ source := ⟨hp.1,by rw [show p.2 = -1 from hp.2]; norm_num⟩
  have hqS : q ∈ source := ⟨hq.1,by rw [show q.2 = 1 from hq.2]; norm_num⟩
  have hh := congrArg Prod.snd (hci hqS hpS hqp)
  have hm : p.2 = -1 := hp.2
  have hp' : q.2 = 1 := hq.2
  linarith

theorem exists_spanning_strip_four_sided_complement
    {S T : Set P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (c : P2 → P2) (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hin : MapsTo c source (T \ interior S))
    (houter : ∀ p ∈ source, c p ∈ frontier T ↔ p.1 = 0)
    (hinner : ∀ p ∈ source, c p ∈ frontier S ↔ p.1 = 1) :
    ∃ E : Set P2, IsFinitePLBallPair P2 E (frontier E) ∧
      E ∪ c '' source = T \ interior S ∧
      E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1) ∧ E ⊆ T \ interior S ∧
      frontier E = ((E ∩ frontier T) ∪ (E ∩ frontier S)) ∪
        ((c '' arm (-1)) ∪ (c '' arm 1)) ∧
      IsFinitePLBallPair ℝ (E ∩ frontier T) {c (0,-1),c (0,1)} ∧
      IsFinitePLBallPair ℝ (E ∩ frontier S) {c (1,-1),c (1,1)} ∧
      IsFinitePLBallPair ℝ (c '' arm (-1)) {c (0,-1),c (1,-1)} ∧
      IsFinitePLBallPair ℝ (c '' arm 1) {c (0,1),c (1,1)} ∧
      Disjoint (E ∩ frontier T) (E ∩ frontier S) ∧
      Disjoint (c '' arm (-1)) (c '' arm 1) ∧
      (∀ v, v = -1 ∨ v = 1 → (E ∩ frontier T) ∩ (c '' arm v) = {c (0,v)}) ∧
      (∀ v, v = -1 ∨ v = 1 → (E ∩ frontier S) ∩ (c '' arm v) = {c (1,v)}) := by
  obtain ⟨E,hE,hcover,hcontact,hEA,hfront⟩ :=
    exists_spanning_strip_complement hS hT hST c hc hci hin houter hinner
  have hTsub : frontier T ⊆ T \ interior S := by
    intro x hx
    exact ⟨hT.1 hx,fun h => hx.2 (hST (interior_subset h))⟩
  have hSsub : frontier S ⊆ T \ interior S := by
    intro x hx
    exact ⟨interior_subset (hST (hS.1 hx)),hx.2⟩
  refine ⟨E,hE,hcover,hcontact,hEA,?_,
    strip_complement_rim_interval hT hTsub hc hci (Or.inl rfl) houter hcover hcontact,
    strip_complement_rim_interval hS hSsub hc hci (Or.inr rfl) hinner hcover hcontact,
    strip_far_arm_ball hc hci (Or.inl rfl),strip_far_arm_ball hc hci (Or.inr rfl),?_,
    strip_far_arms_disjoint hci,?_,?_⟩
  · simpa only [inter_union_distrib_left,image_union] using hfront
  · exact disjoint_left.mpr (fun x hx hy => hx.2.2 (hST (hS.1 hy.2)))
  · intro v hv
    exact strip_complement_rim_arm_inter (by norm_num) hv houter hcontact
  · intro v hv
    exact strip_complement_rim_arm_inter (by norm_num) hv hinner hcontact

end PoincareConjecture.M76.Dehn.Annuli

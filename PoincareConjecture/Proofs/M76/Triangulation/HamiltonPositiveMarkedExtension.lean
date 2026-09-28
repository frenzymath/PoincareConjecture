import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProductMarkedBoundary
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnmarkedProductHalves
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedHalfBallExtension










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-(1 / 4 : ℝ)) (1 / 4)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem exists_positive_marked_half_extension {R D : Set E} {b : D2 ≃ₜ D}
    (P : HamiltonUnmarkedDiskProduct R b) (hb : b.IsFinitePL)
    (F : (V2 × ℝ) → E) (hF : FinitePiecewiseAffineOn F (Q2 ×ˢ I))
    (hFinj : InjOn F (Q2 ×ˢ I))
    (hFfront : MapsTo F (Q2 ×ˢ I) (frontier R))
    (hcenter : ∀ x ∈ Q2, F (x, 0) = P.map (x, 0))
    {w : ℝ} (hw : 0 < w) (hwsmall : w ≤ 1 / 4)
    (hband : MapsTo F (Q2 ×ˢ Icc (-w) w)
      (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1)))
    (hside : MapsTo F (Q2 ×ˢ Icc 0 w) (P.map '' (Q2 ×ˢ Ico (0 : ℝ) 1))) :
    ∃ f : (V2 × ℝ) → E,
      FinitePiecewiseAffineOn f (D2 ×ˢ Icc 0 w) ∧
      InjOn f (D2 ×ˢ Icc 0 w) ∧
      MapsTo f (D2 ×ˢ Icc 0 w) (P.map '' (D2 ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ x : D2, f ((x : V2), 0) = b x) ∧
      (∀ x ∈ Q2, ∀ t ∈ Icc 0 w, f (x, t) = F (x, t)) ∧
      ∀ p ∈ D2 ×ˢ Icc 0 w, f p ∈ frontier R ↔ p.1 ∈ Q2 := by
  let side := Q2 ×ˢ Icc (0 : ℝ) w
  let base := D2 ×ˢ ({0} : Set ℝ)
  let mark := base ∪ side
  let endDisk := D2 ×ˢ ({w} : Set ℝ)
  let endRim := Q2 ×ˢ ({w} : Set ℝ)
  let C := P.map '' (D2 ×ˢ Icc (0 : ℝ) 1)
  let S := P.map '' ((Q2 ×ˢ Icc (0 : ℝ) 1) ∪ (D2 ×ˢ ({0, 1} : Set ℝ)))
  let G := D ∪ F '' side
  obtain ⟨H, hH, hHbase, hHside, hHrim, hG⟩ :=
    exists_marked_half_boundary_parametrization P hb F hF hFinj hFfront hcenter hw hwsmall hband
  have hC : IsFinitePLBallPair (V2 × ℝ) C S :=
    P.half_ballPair zero_lt_one (by norm_num) le_rfl
  have hDS : D ⊆ S := by
    rw [← P.central_image]
    apply image_mono
    exact fun p hp => Or.inr ⟨hp.1, Or.inl hp.2⟩
  have hGS : G ⊆ S := by
    apply union_subset hDS
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨z, hz, he⟩ := hside hp
    exact ⟨z, Or.inl ⟨hz.1, hz.2.1, hz.2.2.le⟩, he⟩
  have hout : (S \ G).Nonempty := by
    let z : V2 × ℝ := (0, 1)
    have hzD : (0 : V2) ∈ D2 := mem_closedBall_self zero_le_one
    have hz : z ∈ D2 ×ˢ Icc (-1 : ℝ) 1 := ⟨hzD, by norm_num [z]⟩
    refine ⟨P.map z, ⟨z, Or.inr ⟨hzD, Or.inr rfl⟩, rfl⟩, ?_⟩
    rintro (hD | hband')
    · obtain ⟨p, hp, he⟩ := P.central_image.symm.subset hD
      have hp0 : p.2 = 0 := hp.2
      have hpC : p ∈ D2 ×ˢ Icc (-1 : ℝ) 1 := ⟨hp.1, by rw [hp0]; norm_num⟩
      have hpeq := P.injective hpC hz he
      have ht := congrArg Prod.snd hpeq
      change p.2 = 1 at ht
      linarith
    · obtain ⟨p, hp, he⟩ := hband'
      obtain ⟨q, hq, hqe⟩ := hside hp
      have hqC : q ∈ D2 ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨sphere_subset_closedBall hq.1, by linarith [hq.2.1], hq.2.2.le⟩
      have hqz := P.injective hqC hz (hqe.trans he)
      have ht := congrArg Prod.snd hqz
      change q.2 = 1 at ht
      linarith [hq.2.2]
  have hinter : endDisk ∩ mark = endRim := by
    ext p
    constructor
    · rintro ⟨hp, hb | hs⟩
      · have hpw : p.2 = w := hp.2
        have hp0 : p.2 = 0 := hb.2
        exact False.elim (hw.ne' (hpw.symm.trans hp0))
      · exact ⟨hs.1, hp.2⟩
    · intro hp
      have hpw : p.2 = w := hp.2
      exact ⟨⟨sphere_subset_closedBall hp.1, hp.2⟩,
        Or.inr ⟨hp.1, by rw [hpw]; exact ⟨hw.le, le_rfl⟩⟩⟩
  have hend : IsFinitePLBallPair (ℝ × ℝ) endDisk endRim :=
    (hamilton_half_boundary_models hw).2.2
  obtain ⟨f, hf, hfi, hfm, hfH, hcontact⟩ :=
    (positive_source_half_ballPair hw).exists_inward_extension_of_boundary_disk hC
      (by simp [Module.finrank_prod]) hend hG hGS hout hinter H hH hHrim
  have hfbase (x : D2) : f ((x : V2), 0) = b x := by
    have hx : ((x : V2), (0 : ℝ)) ∈ mark := Or.inl ⟨x.property, rfl⟩
    exact (hfH ⟨_, hx⟩).trans (hHbase x hx)
  have hfside (p : V2 × ℝ) (hp : p ∈ side) : f p = F p :=
    (hfH ⟨p, Or.inr hp⟩).trans (hHside p hp)
  refine ⟨f, hf, hfi, hfm, hfbase, fun x hx t ht => hfside (x, t) ⟨hx, ht⟩, ?_⟩
  intro p hp
  constructor
  · intro hpfront
    have hpS := P.half_frontier_contact (u := 0) (v := 1) (by norm_num) le_rfl
      ⟨hfm hp, hpfront⟩
    rcases (hcontact p hp).mp hpS with hpbase | hpside
    · have ht : p.2 = 0 := hpbase.2
      have hpe : p = (p.1, (0 : ℝ)) := Prod.ext rfl ht
      rw [hpe, hfbase ⟨p.1, hp.1⟩, ← P.central ⟨p.1, hp.1⟩] at hpfront
      exact (P.proper (p.1, 0) ⟨hp.1, by norm_num⟩).mp hpfront
    · exact hpside.1
  · intro hpQ
    rw [hfside p ⟨hpQ, hp.2⟩]
    exact hFfront ⟨hpQ, by constructor <;> linarith [hp.2.1, hp.2.2]⟩

end PoincareConjecture.M76.HamiltonIndexOne

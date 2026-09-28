import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Rims.SquareEdges



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem exists_marked_square_rim_interval
    {K Q : Set P2} (H : Sq ≃ₜ K) (hH : H.IsFinitePL)
    (hQ : ∀ z : Sq, (H z : P2) ∈ Q ↔ (z : P2).2 = 0) :
    IsFinitePLBallPair ℝ (K ∩ Q)
      {(H ⟨(0, 0), by norm_num, by norm_num⟩ : P2),
        (H ⟨(1, 0), by norm_num, by norm_num⟩ : P2)} ∧
      ∃ q : I ≃ₜ (K ∩ Q : Set P2), q.IsFinitePL ∧
        ∀ t : I, (q t : P2) = H ⟨(t, 0), t.property, by norm_num⟩ := by
  let z (t : I) : Sq := ⟨(t, 0), t.property, by norm_num⟩
  have hrange : range (fun t : I ↦ (H (z t) : P2)) = K ∩ Q := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(H (z t)).property, (hQ (z t)).mpr rfl⟩
    · rintro ⟨hx, hxQ⟩
      let w := H.symm ⟨x, hx⟩
      have hw : (H w : P2) = x := congrArg Subtype.val (H.apply_symm_apply _)
      have hw0 := (hQ w).mp (hw.symm ▸ hxQ)
      have hz : z ⟨w.val.1, w.property.1⟩ = w := Subtype.ext (Prod.ext rfl hw0.symm)
      exact ⟨⟨w.val.1, w.property.1⟩, (congrArg (fun u : Sq ↦ (H u : P2)) hz).trans hw⟩
  obtain ⟨q, hq, hqval⟩ := exists_horizontal_square_edge_parameter H hH (by norm_num : (0 : ℝ) ∈ I)
  let q' := q.trans (Homeomorph.setCongr hrange)
  have hq' : q'.IsFinitePL := hq.setCongr rfl hrange
  have hq'val (t : I) : (q' t : P2) = H (z t) := hqval t
  refine ⟨?_, q', hq', hq'val⟩
  obtain ⟨p, hp, hpval⟩ := hq'
  have hpi : InjOn p I := by
    intro x hx y hy he
    exact congrArg Subtype.val (q'.injective (Subtype.ext
      ((hpval ⟨x, hx⟩).trans (he.trans (hpval ⟨y, hy⟩).symm))))
  have him : p '' I = K ∩ Q := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact hpval ⟨t, ht⟩ ▸ (q' ⟨t, ht⟩).property
    · intro hx
      obtain ⟨t, ht⟩ := q'.surjective ⟨x, hx⟩
      exact ⟨t, t.property, (hpval t).symm.trans (congrArg Subtype.val ht)⟩
  have hb := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).image hp hpi
  rw [him, image_pair] at hb
  have h0 : p 0 = H (z 0) := (hpval 0).symm.trans (hq'val 0)
  have h1 : p 1 = H (z 1) := (hpval 1).symm.trans (hq'val 1)
  simpa [h0, h1, z] using hb

end PoincareConjecture.M76.Dehn

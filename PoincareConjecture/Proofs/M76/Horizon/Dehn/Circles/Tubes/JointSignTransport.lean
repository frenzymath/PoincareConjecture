import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.IncidentJointSigns

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.SignedJointCross

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (J : SignedJointCross E)



theorem side_iff_of_zero_and_endpoint_signs
    (mu : Fin 2 → E → ℝ) (hcont : ∀ j, ContinuousOn (mu j) J.disk)
    (hzero : ∀ j z, z ∈ J.disk → (J.coordinate j z = 0 ↔ mu j z = 0))
    (eta : Fin 2 → Bool)
    (heta : ∀ j, if eta j then
      mu j (J.endpoint j.rev false) < 0 ∧ 0 < mu j (J.endpoint j.rev true)
      else 0 < mu j (J.endpoint j.rev false) ∧ mu j (J.endpoint j.rev true) < 0)
    (j : Fin 2) (b : Bool) (z : E) (hz : z ∈ J.disk) :
    side b (J.coordinate j z) ↔ side (if eta j then b else !b) (mu j z) := by
  have hhalf (j : Fin 2) (b : Bool) :
      MapsTo (mu j) (J.disk ∩ {z | side b (J.coordinate j z)})
        {y | side (if eta j then b else !b) y} := by
    have hd := J.half_ball j b
    have hboundary : (J.disk ∩ {z | side b (J.coordinate j z)}) ∩ {z | mu j z = 0} ⊆
        (J.rim ∩ {z | side b (J.coordinate j z)}) ∪ J.axis j :=
      fun z hz => Or.inr ⟨hz.1.1, (hzero j z hz.1.1).mpr hz.2⟩
    have hw : J.endpoint j.rev b ∈ J.disk ∩ {z | side b (J.coordinate j z)} := by
      refine ⟨J.disk_ball.1 (J.endpoint_mem_rim j.rev b), ?_⟩
      change side b (J.coordinate j (J.endpoint j.rev b))
      simpa only [Fin.rev_rev] using
        J.radius_side j.rev b _ (right_mem_segment ℝ _ _)
    have hi := heta j
    cases he : eta j <;> cases b
    · change MapsTo (mu j) _ (Ici 0)
      exact hd.mapsTo_nonneg_of_zeros_in_boundary (mu j) ((hcont j).mono inter_subset_left)
        hboundary ⟨J.endpoint j.rev false, hw, (show 0 < mu j (J.endpoint j.rev false) ∧
          mu j (J.endpoint j.rev true) < 0 from by simpa [he] using hi).1⟩
    · change MapsTo (mu j) _ (Iic 0)
      exact hd.mapsTo_nonpos_of_zeros_in_boundary (mu j) ((hcont j).mono inter_subset_left)
        hboundary ⟨J.endpoint j.rev true, hw, (show 0 < mu j (J.endpoint j.rev false) ∧
          mu j (J.endpoint j.rev true) < 0 from by simpa [he] using hi).2⟩
    · change MapsTo (mu j) _ (Iic 0)
      exact hd.mapsTo_nonpos_of_zeros_in_boundary (mu j) ((hcont j).mono inter_subset_left)
        hboundary ⟨J.endpoint j.rev false, hw, (show mu j (J.endpoint j.rev false) < 0 ∧
          0 < mu j (J.endpoint j.rev true) from by simpa [he] using hi).1⟩
    · change MapsTo (mu j) _ (Ici 0)
      exact hd.mapsTo_nonneg_of_zeros_in_boundary (mu j) ((hcont j).mono inter_subset_left)
        hboundary ⟨J.endpoint j.rev true, hw, (show mu j (J.endpoint j.rev false) < 0 ∧
          0 < mu j (J.endpoint j.rev true) from by simpa [he] using hi).2⟩
  refine ⟨fun h => hhalf j b ⟨hz, h⟩, ?_⟩
  intro h
  by_cases hs : side b (J.coordinate j z)
  · exact hs
  have ho : side (!b) (J.coordinate j z) := by
    cases b <;> exact le_of_lt (lt_of_not_ge hs)
  have hw := hhalf j (!b) ⟨hz, ho⟩
  have hnot : (if eta j then !b else !(!b)) = !(if eta j then b else !b) := by
    cases eta j <;> rfl
  change side (if eta j then !b else !(!b)) (mu j z) at hw
  rw [hnot] at hw
  have hboth (c : Bool) (x : ℝ) (ha : side c x) (hb : side (!c) x) : x = 0 := by
    cases c
    · exact le_antisymm ha hb
    · exact le_antisymm hb ha
  have hm := hboth (if eta j then b else !b) (mu j z) h hw
  have hc := (hzero j z hz).mpr hm
  cases b <;> simp [side, hc]

end PoincareConjecture.M76.Dehn.SignedJointCross

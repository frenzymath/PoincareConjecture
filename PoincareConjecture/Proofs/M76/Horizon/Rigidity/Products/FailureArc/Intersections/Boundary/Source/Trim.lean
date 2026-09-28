import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Source.OrientedTube
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Enlargement.FarSeam

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem proper_strip_arm_rim_contact
    {E : Type*} {c : P2 → E} {Q : Set E} {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1)
    (hcQ : ∀ p ∈ source, c p ∈ Q ↔ p.1 = 0 ∨ p.1 = 1) :
    Q ∩ (c '' arm u) = {c (0, u), c (1, u)} := by
  ext x
  constructor
  · rintro ⟨hxQ, p, hp, rfl⟩
    have hpS : p ∈ source := ⟨hp.1, hp.2 ▸ hu⟩
    rcases (hcQ p hpS).mp hxQ with ht | ht
    · exact Or.inl (congrArg c (Prod.ext ht hp.2))
    · exact Or.inr (congrArg c (Prod.ext ht hp.2))
  · rintro (rfl | rfl)
    · exact ⟨(hcQ (0, u) ⟨by norm_num, hu⟩).mpr (Or.inl rfl),
        (0, u), ⟨by norm_num, rfl⟩, rfl⟩
    · exact ⟨(hcQ (1, u) ⟨by norm_num, hu⟩).mpr (Or.inr rfl),
        (1, u), ⟨by norm_num, rfl⟩, rfl⟩

theorem exists_trimmed_returning_disk
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {D U Q : Set E} {c : P2 → E}
    (hD : IsFinitePLBallPair P2 D (U ∪ c '' arm 0))
    (hDU : D ∩ Q = U)
    (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcQ : ∀ p ∈ source, c p ∈ Q ↔ p.1 = 0 ∨ p.1 = 1)
    (hhalf : c '' halfSource true ⊆ D) :
    ∃ B V : Set E,
      B = D \ ((c '' halfSource true) \ c '' arm 1) ∧
      IsFinitePLBallPair P2 B (V ∪ c '' arm 1) ∧
      IsFinitePLBallPair ℝ V {c (0, 1), c (1, 1)} ∧
      V ∩ (c '' arm 1) = {c (0, 1), c (1, 1)} ∧
      B ∩ Q = V ∧ B ⊆ D ∧
      (c '' halfSource true) ∪ B = D ∧ B ∩ (c '' halfSource true) = c '' arm 1 ∧
      Disjoint B (c '' arm 0) := by
  have hQA : U ∪ c '' arm 0 = (D ∩ Q) ∪ c '' arm 0 := by rw [hDU]
  obtain ⟨V, hV, hB, hcover, hcommon, hcontact⟩ :=
    exists_upper_half_strip_complement hD c hc hci hcQ hhalf hQA
  obtain ⟨_, _, _, hnoCenter, _⟩ :=
    half_strip_disk_complement hD c true hc hci hcQ hhalf hQA
  let B := D \ ((c '' halfSource true) \ c '' arm 1)
  have hBQ : B ∩ Q = V := by
    rw [← hcontact]
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, Or.inl (hDU.subset ⟨hx.1.1, hx.2⟩)⟩
    · rintro ⟨hxB, hxU | hxC⟩
      · exact ⟨hxB, (hDU.superset hxU).2⟩
      · exact (disjoint_left.mp hnoCenter hxB hxC).elim
  have hfarB : c '' arm 1 ⊆ B := hcommon.symm.subset.trans inter_subset_right
  have hVfar : V ∩ (c '' arm 1) = {c (0, 1), c (1, 1)} := by
    rw [← hBQ, inter_assoc]
    have hEq : B ∩ (Q ∩ c '' arm 1) = Q ∩ c '' arm 1 :=
      inter_eq_right.mpr (inter_subset_right.trans hfarB)
    rw [hEq]
    exact proper_strip_arm_rim_contact (by norm_num) hcQ
  refine ⟨B, V, rfl, ?_, hV, hVfar, hBQ, fun _ hx ↦ hx.1, hcover, ?_, hnoCenter⟩
  · simpa only [B, halfSource, if_true, union_comm] using hB
  · simpa only [B, halfSource, if_true, inter_comm] using hcommon

end PoincareConjecture.M76.Dehn.Annuli

import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid










set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph




theorem exists_circle_endpoint_halfspace
    {M E ι : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M E)
    (p : ℝ) [Fact (0 < p)] (q : M → AddCircle p)
    {a b theta d : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (htheta : theta = a ∨ theta = b) (hd : (d : AddCircle p) = (theta : AddCircle p))
    (ell : E →ᴬ[ℝ] ℝ) (v : E) (H : OpenPartialHomeomorph M E)
    (hv : ell.contLinear v = 1) {x : M} (hx : x ∈ H.source)
    (hzero : ell (H x) = 0)
    (hH : ∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid E)
    (hq : ∀ y ∈ H.source, q y = ((ell (H y) + d : ℝ) : AddCircle p)) :
    ∃ (ell' : E →ᴬ[ℝ] ℝ) (v' : E) (G : OpenPartialHomeomorph M E),
      ell'.contLinear v' = 1 ∧ x ∈ G.source ∧ ell' (G x) = 0 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid E) ∧
      ∀ y ∈ G.source,
        y ∈ q ⁻¹' AddCircle.closedIntervalArc p a b ↔ 0 ≤ ell' (G y) := by
  let m := min a (min (p - b) (b - a))
  let eta := m / 2
  have hm : 0 < m := lt_min ha (lt_min (sub_pos.mpr hb) (sub_pos.mpr hab))
  have heta : 0 < eta := half_pos hm
  have hetam : eta < m := half_lt_self hm
  have hea : eta < a := hetam.trans_le (min_le_left _ _)
  have heb : eta < p - b :=
    hetam.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heab : eta < b - a :=
    hetam.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let W : Set E := ell ⁻¹' Ioo (-eta) eta
  have hW : IsOpen W := isOpen_Ioo.preimage ell.continuous
  let I := OpenPartialHomeomorph.ofSet W hW
  let G := H.trans I
  have hxG : x ∈ G.source := by
    refine ⟨hx, ?_⟩
    change ell (H x) ∈ Ioo (-eta) eta
    rw [hzero]
    exact ⟨neg_neg_of_pos heta, heta⟩
  have hI : I ∈ piecewiseAffineGroupoid E :=
    ⟨locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E) hW,
      locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E) hW⟩
  have hG (i : ι) : (e i).symm.trans G ∈ piecewiseAffineGroupoid E := by
    simpa only [G, OpenPartialHomeomorph.trans_assoc] using
      (piecewiseAffineGroupoid E).trans (hH i) hI
  have hqG (y : M) (hy : y ∈ G.source) :
      q y = ((ell (G y) + theta : ℝ) : AddCircle p) := by
    change q y = ((ell (H y) + theta : ℝ) : AddCircle p)
    rw [hq y hy.1, AddCircle.coe_add, hd, ← AddCircle.coe_add]
  have hrep (y : M) (hy : y ∈ G.source) :
      ell (G y) + theta ∈ Ico (0 : ℝ) p := by
    have hyW : ell (G y) ∈ Ioo (-eta) eta := hy.2
    rcases htheta with rfl | rfl
    · constructor <;> linarith [hyW.1, hyW.2]
    · constructor <;> linarith [hyW.1, hyW.2]
  rcases htheta with rfl | rfl
  · refine ⟨ell, v, G, hv, hxG, hzero, hG, ?_⟩
    intro y hy
    change q y ∈ AddCircle.closedIntervalArc p theta b ↔ 0 ≤ ell (G y)
    rw [hqG y hy, AddCircle.coe_mem_closedIntervalArc_iff p ha.le hb (hrep y hy)]
    have hyW : ell (G y) ∈ Ioo (-eta) eta := hy.2
    constructor
    · intro h
      linarith [h.1]
    · intro h
      exact ⟨by linarith, by linarith [hyW.2]⟩
  · refine ⟨-ell, -v, G, ?_, hxG, ?_, hG, ?_⟩
    · change -(ell.contLinear (-v)) = 1
      rw [map_neg, neg_neg, hv]
    · change -ell (H x) = 0
      rw [hzero, neg_zero]
    · intro y hy
      change q y ∈ AddCircle.closedIntervalArc p a theta ↔ 0 ≤ -ell (G y)
      rw [hqG y hy, AddCircle.coe_mem_closedIntervalArc_iff p ha.le hb (hrep y hy)]
      have hyW : ell (G y) ∈ Ioo (-eta) eta := hy.2
      constructor
      · intro h
        linarith [h.2]
      · intro h
        exact ⟨by linarith [hyW.1], by linarith⟩

end OpenPartialHomeomorph

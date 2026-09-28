import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Maps.Normalization
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionTubeFibers

set_option autoImplicit false
open Set Geometry TriangleDiskModel PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.NonspanningChainAnnulus

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "Ann" => squareAnnulus 8 1
local notation "Strip" => PolygonalCrossingResolution.source
local notation "Index" => (NonspanningRetainedPiece ⊕ Bool)

open PolygonalCrossingResolution NonspanningChainHole

variable {SA SM SC D : Set P2} {pA pL pR pC : I01 → P2}
  {s : NonspanningChainGeometry SA SM SC pA pL pR pC}
  {H : NonspanningChainHole s D} (N : NonspanningChainAnnulus H)

theorem retained_target_contact {X : Type*} {f : P2 → X} {τ : C3 → X}
    (hτ : InjOn τ tube)
    (hAtube : (SA \ interior D) ∩ f ⁻¹' (τ '' tube) = range pA)
    (hMtube : (SM \ interior D) ∩ f ⁻¹' (τ '' tube) = range pL ∪ range pR)
    (hCtube : (SC \ interior D) ∩ f ⁻¹' (τ '' tube) = range pC)
    (hA : ∀ t : I01, f (pA t) = τ ((-1, 1), t))
    (hL : ∀ t : I01, f (pL t) = τ ((-1, -1), t))
    (hR : ∀ t : I01, f (pR t) = τ ((1, -1), t))
    (hC : ∀ t : I01, f (pC t) = τ ((1, 1), t))
    (i : NonspanningRetainedPiece) (b : Bool)
    (x : H.sourceSet (.inl i)) (y : Strip)
    (heq : f x = τ (alternate (1 / 4) b y)) :
    N.copy (.inl i) x = N.copy (.inr b) y := by
  have hb : (1 / 4 : ℝ) < 1 := by norm_num
  have hinjL := (replacement_target_injective hτ hb.le false).2
  have hinjR := (replacement_target_injective hτ hb.le true).2
  have hsep := alternate_target_disjoint hτ (by norm_num : (0 : ℝ) < 1 / 4) hb.le
  have hmL (y : Strip) : alternate (1 / 4) false y ∈ tube :=
    (mapsTo_tube hb.le false).2 y.property
  have hmR (y : Strip) : alternate (1 / 4) true y ∈ tube :=
    (mapsTo_tube hb.le true).2 y.property
  have hAc (t : I01) : f (pA t) = τ (alternate (1 / 4) false (plusArmPoint t)) := by
    simpa only [plusArmPoint, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.2] using hA t
  have hLc (t : I01) : f (pL t) = τ (alternate (1 / 4) false (minusArmPoint t)) := by
    simpa only [minusArmPoint, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.1] using hL t
  have hRc (t : I01) : f (pR t) = τ (alternate (1 / 4) true (minusArmPoint t)) := by
    simpa only [minusArmPoint, (arm_endpoints hb (t : ℝ)).2.2.2.2.1] using hR t
  have hCc (t : I01) : f (pC t) = τ (alternate (1 / 4) true (plusArmPoint t)) := by
    simpa only [plusArmPoint, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.1] using hC t
  apply (N.copy_eq_iff _ _ _ _).mpr
  cases i <;> cases b
  · obtain ⟨t, ⟨hx, hy⟩, _⟩ :=
      (retained_replacement_fiber hAtube hmL hinjL plusArmPoint_injective hAc x y).mp heq
    exact (s.A_left_eq_iff ⟨x, x.property.1⟩ y).mpr
      ⟨t, hx, congrArg Subtype.val hy⟩
  · exact (retained_opposite_replacement_ne
      (r' := fun y : Strip => alternate (1 / 4) false y)
        hAtube hmR hAc hsep.symm x y heq).elim
  · obtain ⟨t, ⟨hx, hy⟩, _⟩ :=
      (retained_two_replacement_fiber
        (r' := fun y : Strip => alternate (1 / 4) true y)
          hMtube hmL hinjL minusArmPoint_injective hLc hRc hsep x y).mp heq
    exact ((s.left_middle_eq_iff y ⟨x, x.property.1⟩).mpr
      ⟨t, congrArg Subtype.val hy, hx⟩).symm
  · obtain ⟨t, ⟨hx, hy⟩, _⟩ :=
      (retained_two_replacement_fiber
        (r' := fun y : Strip => alternate (1 / 4) false y)
          (hMtube.trans (union_comm _ _)) hmR hinjR minusArmPoint_injective
            hRc hLc hsep.symm x y).mp heq
    exact (s.middle_right_eq_iff ⟨x, x.property.1⟩ y).mpr
      ⟨t, hx, congrArg Subtype.val hy⟩
  · exact (retained_opposite_replacement_ne
      (r' := fun y : Strip => alternate (1 / 4) true y) hCtube hmL hCc hsep x y heq).elim
  · obtain ⟨t, ⟨hx, hy⟩, _⟩ :=
      (retained_replacement_fiber hCtube hmR hinjR plusArmPoint_injective hCc x y).mp heq
    exact ((s.right_C_eq_iff y ⟨x, x.property.1⟩).mpr
      ⟨t, congrArg Subtype.val hy, hx⟩).symm

theorem strip_target_fibers {X : Type*} {f g : P2 → X} {τ : C3 → X}
    (hkeep : ∀ i (x : H.sourceSet i), g (N.copy i x) = pieceMap f τ i x)
    (hτ : InjOn τ tube)
    (hAtube : (SA \ interior D) ∩ f ⁻¹' (τ '' tube) = range pA)
    (hMtube : (SM \ interior D) ∩ f ⁻¹' (τ '' tube) = range pL ∪ range pR)
    (hCtube : (SC \ interior D) ∩ f ⁻¹' (τ '' tube) = range pC)
    (hA : ∀ t : I01, f (pA t) = τ ((-1, 1), t))
    (hL : ∀ t : I01, f (pL t) = τ ((-1, -1), t))
    (hR : ∀ t : I01, f (pR t) = τ ((1, -1), t))
    (hC : ∀ t : I01, f (pC t) = τ ((1, 1), t))
    (b : Bool) (y : Strip) {z : P2} (hz : z ∈ Ann) :
    g z = g (N.copy (.inr b) y) ↔ z = N.copy (.inr b) y := by
  constructor
  · intro h
    obtain ⟨i, x, hx⟩ := mem_iUnion.mp (N.copy_cover.symm.subset (mem_univ (⟨z, hz⟩ : Ann)))
    have hv : (N.copy i x : P2) = z := congrArg Subtype.val hx
    rw [← hv, hkeep i x, hkeep (.inr b) y] at h
    rw [← hv]
    cases i with
    | inl i =>
      exact congrArg Subtype.val
        (N.retained_target_contact hτ hAtube hMtube hCtube hA hL hR hC i b x y h)
    | inr d =>
      by_cases hdb : d = b
      · subst d
        have hxy := (replacement_target_injective hτ (show (1 / 4 : ℝ) ≤ 1 by norm_num) b).2 h
        exact congrArg (fun v : Strip => (N.copy (.inr b) v : P2)) hxy
      · have hsep := alternate_target_disjoint hτ (by norm_num : (0 : ℝ) < 1 / 4)
          (by norm_num : (1 / 4 : ℝ) ≤ 1)
        cases d <;> cases b
        · exact (hdb rfl).elim
        · exact (disjoint_left.mp hsep ⟨x, h⟩ ⟨y, rfl⟩).elim
        · exact (disjoint_left.mp hsep ⟨y, rfl⟩ ⟨x, h⟩).elim
        · exact (hdb rfl).elim
  · rintro rfl
    rfl

end PoincareConjecture.M76.Dehn.NonspanningChainAnnulus

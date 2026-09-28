import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.IndexedCopies

set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.NonspanningChainGeometry

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "Strip" => PolygonalCrossingResolution.source
local notation "Piece" => NonspanningRetainedPiece

open PolygonalCrossingResolution

variable {SA SM SC : Set P2} {pA pL pR pC : I01 → P2}
  (s : NonspanningChainGeometry SA SM SC pA pL pR pC)

theorem retained_strip_values {X : Type*} (f : P2 → X) (τ : C3 → X)
    (hA : ∀ t : I01, f (pA t) = τ ((-1, 1), t))
    (hL : ∀ t : I01, f (pL t) = τ ((-1, -1), t))
    (hR : ∀ t : I01, f (pR t) = τ ((1, -1), t))
    (hC : ∀ t : I01, f (pC t) = τ ((1, 1), t))
    (i : Piece) (b : Bool) (x : s.retainedSet i) (y : Strip)
    (hxy : s.retainedCopy i x = s.stripCopy b y) :
    f x = τ (alternate (1 / 4) b y) := by
  have hb : (1 / 4 : ℝ) < 1 := by norm_num
  cases i <;> cases b
  · obtain ⟨t, hx, hy⟩ := (s.A_left_eq_iff x y).mp hxy
    rw [hx, hy, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.2]
    exact hA t
  · exact (s.A_ne_right x y hxy).elim
  · obtain ⟨t, hy, hx⟩ := (s.left_middle_eq_iff y x).mp hxy.symm
    rw [hx, hy, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.2.1]
    exact hL t
  · obtain ⟨t, hx, hy⟩ := (s.middle_right_eq_iff x y).mp hxy
    rw [hx, hy, (arm_endpoints hb (t : ℝ)).2.2.2.2.1]
    exact hR t
  · exact (s.left_ne_C y x hxy.symm).elim
  · obtain ⟨t, hy, hx⟩ := (s.right_C_eq_iff y x).mp hxy.symm
    rw [hx, hy, (arm_endpoints hb (t : ℝ)).2.2.2.2.2.1]
    exact hC t

theorem strip_values {X : Type*} (τ : C3 → X)
    (hdisj : Disjoint (range pL) (range pR)) (b d : Bool) (x y : Strip)
    (hxy : s.stripCopy b x = s.stripCopy d y) :
    τ (alternate (1 / 4) b x) = τ (alternate (1 / 4) d y) := by
  by_cases hbd : b = d
  · subst d
    rw [(s.stripCopy_embedding b).injective hxy]
  · cases b <;> cases d
    · exact (hbd rfl).elim
    · exact (s.left_ne_right hdisj x y hxy).elim
    · exact (s.left_ne_right hdisj y x hxy.symm).elim
    · exact (hbd rfl).elim

end PoincareConjecture.M76.Dehn.NonspanningChainGeometry

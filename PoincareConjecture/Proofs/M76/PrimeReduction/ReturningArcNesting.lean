import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningArcBigon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionNesting
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence

set_option autoImplicit false

open Set

namespace Polygon

local notation "V" => (ℝ × ℝ)
local notation "Z" => (Set.preimage (Prod.snd : (ℝ × ℝ) → ℝ) ({0} : Set ℝ))

theorem segment_subset_returning_axis {u v : V} (hu : u ∈ Z) (hv : v ∈ Z) :
    segment ℝ u v ⊆ Z := by
  have hZ : Convex ℝ Z := by
    intro x hx y hy a b _ha _hb _hab
    change a * x.2 + b * y.2 = 0
    rw [show x.2 = 0 from hx, show y.2 = 0 from hy, mul_zero, mul_zero, add_zero]
  exact hZ.segment_subset hu hv

theorem returning_closed_inside_axis {n : ℕ} (P : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hup : ∀ i, 0 ≤ (P i).2) {A : Set V} {u v : V}
    (hboundary : P.boundary ℝ = A ∪ segment ℝ u v)
    (haxis : A ∩ Z = {u, v}) :
    closure P.inside ∩ Z = segment ℝ u v := by
  have hu : u ∈ Z := (haxis.symm.subset (by simp)).2
  have hv : v ∈ Z := (haxis.symm.subset (by simp)).2
  have hcontact : closure P.inside ∩ Z = P.boundary ℝ ∩ Z :=
    P.closed_inside_axis_contact hP hi hup
  rw [hcontact, hboundary,
    union_inter_distrib_right, haxis,
    inter_eq_left.mpr (segment_subset_returning_axis hu hv)]
  exact union_eq_right.mpr (by
    intro x hx
    rcases hx with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _)

theorem inside_disjoint_returning_axis {n : ℕ} (P : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hi : Function.Injective P)
    (hup : ∀ i, 0 ≤ (P i).2) : Disjoint P.inside Z := by
  exact disjoint_left.mpr fun _ hx hz =>
    hx.1 (((P.closed_inside_axis_contact hP hi hup).subset ⟨subset_closure hx, hz⟩).1)

theorem returning_inside_subset_or_disjoint {m n : ℕ}
    (P : Polygon V (m + 3)) (Q : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hiP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hiQ : Function.Injective Q)
    (hup : ∀ i, 0 ≤ (P i).2)
    {A B : Set V} {u v a b : V}
    (hPB : P.boundary ℝ = A ∪ segment ℝ u v)
    (hQB : Q.boundary ℝ = B ∪ segment ℝ a b)
    (hAz : A ∩ Z = {u, v}) (hBz : B ∩ Z = {a, b})
    (hB : IsFinitePLBallPair ℝ B {a, b}) (hAB : Disjoint A B) :
    Q.inside ⊆ P.inside ∨ Disjoint P.inside (Q.boundary ℝ) := by
  have hu : u ∈ Z := (hAz.symm.subset (by simp)).2
  have hv : v ∈ Z := (hAz.symm.subset (by simp)).2
  have ha : a ∈ Z := (hBz.symm.subset (by simp)).2
  have hb : b ∈ Z := (hBz.symm.subset (by simp)).2
  have havoid : B \ {a, b} ⊆ (P.boundary ℝ)ᶜ := by
    intro x hx hxP
    rcases hPB ▸ hxP with hxA | hxseg
    · exact disjoint_left.mp hAB hxA hx.1
    · exact hx.2 (hBz.subset ⟨hx.1, segment_subset_returning_axis hu hv hxseg⟩)
  have hside := hB.isConnected_sdiff.isPreconnected.subset_or_subset
    (P.isOpen_inside hP hiP) (P.isOpen_outside hP hiP) P.disjoint_inside_outside
    (by rw [← P.compl_boundary_eq_inside_union_outside]; exact havoid)
  rcases hside with hin | hout
  · have hBcl : B ⊆ closure P.inside := by
      rw [← hB.closure_sdiff]
      exact closure_mono hin
    have haxis := P.returning_closed_inside_axis hP hiP hup hPB hAz
    have haP : a ∈ segment ℝ u v := haxis.subset ⟨hBcl (hB.1 (by simp)), ha⟩
    have hbP : b ∈ segment ℝ u v := haxis.subset ⟨hBcl (hB.1 (by simp)), hb⟩
    have hseg : segment ℝ a b ⊆ closure P.inside := by
      intro x hx
      exact (haxis.symm.subset ((convex_segment u v).segment_subset haP hbP hx)).1
    apply Or.inl (P.inside_subset_inside_of_boundary_subset Q hP hiP hQ hiQ ?_)
    rw [hQB]
    exact union_subset hBcl hseg
  · have hBcl : B ⊆ closure P.outside := by
      rw [← hB.closure_sdiff]
      exact closure_mono hout
    right
    rw [hQB, disjoint_union_right]
    exact ⟨(P.disjoint_inside_outside.closure_right (P.isOpen_inside hP hiP)).mono_right hBcl,
      (P.inside_disjoint_returning_axis hP hiP hup).mono_right
        (segment_subset_returning_axis ha hb)⟩

end Polygon

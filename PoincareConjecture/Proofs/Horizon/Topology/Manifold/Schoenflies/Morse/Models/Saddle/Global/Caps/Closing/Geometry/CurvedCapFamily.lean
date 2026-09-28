import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.CurvedCapSeparation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Nesting

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

private theorem exists_separated_positive_scales
    {ι X : Type*} [Finite ι] (D : ι → Set X) {R : Real} (hR : 0 < R) :
    ∃ w : ι → Real, (∀ i, 0 < w i ∧ w i < R) ∧
      ∀ i j, D i ⊂ D j → 2 * w i < w j := by
  classical
  let := Fintype.ofFinite ι
  let S (i : ι) := Finset.univ.filter (fun j => D j ⊆ D i)
  let n (i : ι) := (S i).card
  let c : Real := R / 3 ^ (Fintype.card ι + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hn (i : ι) : n i ≤ Fintype.card ι := Finset.card_le_card (Finset.filter_subset _ _)
  have horder (i j : ι) (hij : D i ⊂ D j) : n i < n j := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hk).2.trans hij.subset⟩
    · intro heq
      have hj : j ∈ S j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subset.rfl⟩
      rw [← heq] at hj
      exact hij.not_superset (Finset.mem_filter.mp hj).2
  refine ⟨fun i => c * 3 ^ n i, ?_, ?_⟩
  · intro i
    refine ⟨mul_pos hc (by positivity), ?_⟩
    have hp : (3 : Real) ^ n i < 3 ^ (Fintype.card ι + 1) :=
      pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_of_le (hn i))
    have hh := mul_lt_mul_of_pos_left hp hc
    have heq : c * 3 ^ (Fintype.card ι + 1) = R := by
      dsimp [c]
      exact div_mul_cancel₀ R (by positivity)
    rwa [heq] at hh
  · intro i j hij
    have hp : (3 : Real) ^ (n i + 1) ≤ 3 ^ n j :=
      pow_le_pow_right₀ (by norm_num) (horder i j hij)
    rw [pow_succ] at hp
    have hpos : 0 < c * 3 ^ n i := mul_pos hc (by positivity)
    have hm := mul_le_mul_of_nonneg_left hp hc.le
    nlinarith

theorem exists_disjoint_curved_closing_cap_family
    {ι : Type*} [Finite ι] {v : E3} (hv : ‖v‖ = 1) (b : Real)
    (A : ι → (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (hcircles : Pairwise (fun i j => Disjoint
      (A i '' sphere (0 : Hemisphere.Plane v) 1)
      (A j '' sphere (0 : Hemisphere.Plane v) 1)))
    {R : Real} (hR : 0 < R) :
    ∃ w : ι → Real, ∃ hw : ∀ i, 0 < w i,
      (∀ i, w i < R) ∧
      (∀ i j, A i '' closedBall (0 : Hemisphere.Plane v) 1 ⊆ A j '' ball 0 1 →
        2 * w i < w j) ∧
      Pairwise (fun i j => Disjoint
        (liftPlaneDiffeomorph hv b (w i) (hw i).ne' (A i) '' boundedCylinderNorthernCap v)
        (liftPlaneDiffeomorph hv b (w j) (hw j).ne' (A j) '' boundedCylinderNorthernCap v)) := by
  let J : Hemisphere.Plane v ≃ₗᵢ[Real] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by intro h; simp [h] at hv)).repr
  let : Nontrivial (Hemisphere.Plane v) := Module.nontrivial_of_finrank_pos
    (R := Real) (by rw [J.toLinearEquiv.finrank_eq]; norm_num)
  have hdim : 1 < Module.rank Real (Hemisphere.Plane v) := by
    rw [← Module.finrank_eq_rank, J.toLinearEquiv.finrank_eq]
    norm_num
  obtain ⟨w, hw, hscale⟩ := exists_separated_positive_scales
    (fun i => A i '' closedBall (0 : Hemisphere.Plane v) 1) hR
  have hstrict (i j : ι)
      (hij : A i '' closedBall (0 : Hemisphere.Plane v) 1 ⊆ A j '' ball 0 1) :
      A i '' closedBall (0 : Hemisphere.Plane v) 1 ⊂ A j '' closedBall 0 1 := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hij.trans (image_mono ball_subset_closedBall), ?_⟩
    intro heq
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty
      (E := Hemisphere.Plane v) (x := 0)).mpr (show (0 : Real) ≤ 1 by norm_num)
    have hm : A j x ∈ A i '' closedBall (0 : Hemisphere.Plane v) 1 := by
      rw [heq]
      exact mem_image_of_mem _ (sphere_subset_closedBall hx)
    obtain ⟨y, hy, he⟩ := hij hm
    have hyx := (A j).injective he
    subst y
    exact (ne_of_lt (mem_ball_zero_iff.mp hy)) (mem_sphere_zero_iff_norm.mp hx)
  have hs (i j : ι) (hij : A i '' closedBall (0 : Hemisphere.Plane v) 1 ⊆ A j '' ball 0 1) :
      2 * w i < w j := hscale i j (hstrict i j hij)
  refine ⟨w, fun i => (hw i).1, fun i => (hw i).2, hs, ?_⟩
  intro i j hij
  rcases (A i).toHomeomorph.disjoint_or_nested_image_closedBall (A j).toHomeomorph
    hdim (hcircles hij) with hd | hnest | hnest
  · exact disjoint_curved_closing_caps_of_disjoint_fillings hv b (w i) (w j)
      (hw i).1 (hw j).1 (A i) (A j) hd
  · exact disjoint_curved_closing_caps_of_nested_fillings hv b (w i) (w j)
      (hw i).1 (hw j).1 (A i) (A j) hnest (hs i j hnest)
  · exact (disjoint_curved_closing_caps_of_nested_fillings hv b (w j) (w i)
      (hw j).1 (hw i).1 (A j) (A i) hnest (hs j i hnest)).symm

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

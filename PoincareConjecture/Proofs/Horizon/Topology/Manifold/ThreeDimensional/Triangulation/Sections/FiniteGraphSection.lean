import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Sections.FiniteAffineSectionBound
import Mathlib.Topology.MetricSpace.Contracting

set_option autoImplicit false

open Set Metric
open scoped NNReal

universe u v w

namespace Poincare.Topology

theorem exists_unique_lipschitz_graph_section
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    {T : Type w} [NormedAddCommGroup T] [NormedSpace Real T]
    (A : E →ᵃ[Real] F) (s : Finset E) (a : Real) (ha : 0 < a)
    (hcard : s.card = Module.finrank Real F + 1)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real F →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖)
    (x0 : E) (hx0 : x0 ∈ convexHull Real (s : Set E)) (hAx0 : A x0 = 0)
    (p : E) (Q : E →L[Real] T) (hQ : ‖Q‖ ≤ 1)
    (f : T → F) (epsilon : NNReal) (rho R : Real)
    (hsize : ∀ x ∈ convexHull Real (s : Set E), ‖x - p‖ ≤ R)
    (hRrho : R < rho) (hf0 : f 0 = 0)
    (hf : LipschitzOnWith epsilon f (ball (0 : T) rho))
    (hsmall : (epsilon : Real) * R ≤ a)
    (hcontract : (epsilon : Real) * (diam (s : Set E) / a) < 1) :
    ∃ x ∈ convexHull Real (s : Set E), A x = f (Q (x - p)) ∧
      ‖x - x0‖ ≤ (diam (s : Set E) / a) * ((epsilon : Real) * R) ∧
      ∀ z ∈ convexHull Real (s : Set E), A z = f (Q (z - p)) → z = x := by
  obtain ⟨B, hB1, hB2⟩ :=
    exists_minimal_affine_section_inverse A s a ha hcard hgap ⟨x0, hx0, hAx0⟩
  have hBnorm := minimal_affine_section_inverse_norm_le A s a ha hgap
    ⟨x0, hx0, hAx0⟩ B hB2
  let g (n : F) : E := x0 + (B n : E)
  have hcoord (x : E) (hx : x ∈ convexHull Real (s : Set E)) : g (A x) = x := by
    have hv : x - x0 ∈ vectorSpan Real (s : Set E) :=
      vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
        (convexHull_subset_affineSpan _ hx) (convexHull_subset_affineSpan _ hx0)
    have hAv : A.linear (⟨x - x0, hv⟩ : vectorSpan Real (s : Set E)) = A x := by
      simpa only [vsub_eq_sub, hAx0, sub_zero] using A.linearMap_vsub x x0
    have h := hB2 ⟨x - x0, hv⟩
    rw [hAv] at h
    have hb : (B (A x) : E) = x - x0 := congrArg Subtype.val h
    dsimp only [g]
    rw [hb]
    abel
  have hAg (n : F) : A (g n) = n := by
    change A (x0 + (B n : E)) = n
    rw [add_comm]
    change A ((B n : E) +ᵥ x0) = n
    rw [A.map_vadd]
    change A.linear (B n) + A x0 = n
    rw [hB1, hAx0, add_zero]
  have hball := closedBall_subset_affine_convexHull_of_small_faces_gap
    A s a ha hgap ⟨x0, hx0, hAx0⟩
  have hghull (n : F) (hn : ‖n‖ ≤ a) : g n ∈ convexHull Real (s : Set E) := by
    obtain ⟨x, hx, hAx⟩ := hball (mem_closedBall_zero_iff.mpr hn)
    have h := hcoord x hx
    rw [hAx] at h
    rw [h]
    exact hx
  have hR : 0 ≤ R := (norm_nonneg _).trans (hsize x0 hx0)
  have hrho : 0 < rho := hR.trans_lt hRrho
  have hQbound (v : E) : ‖Q v‖ ≤ ‖v‖ := by
    calc
      ‖Q v‖ ≤ ‖Q‖ * ‖v‖ := Q.le_opNorm v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hQ (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  have hsource (x : E) (hx : x ∈ convexHull Real (s : Set E)) :
      Q (x - p) ∈ ball (0 : T) rho :=
    mem_ball_zero_iff.mpr ((hQbound _).trans (hsize x hx) |>.trans_lt hRrho)
  have hfsize (x : E) (hx : x ∈ convexHull Real (s : Set E)) :
      ‖f (Q (x - p))‖ ≤ (epsilon : Real) * R := by
    have h := hf.dist_le_mul (Q (x - p)) (hsource x hx) 0 (mem_ball_self hrho)
    rw [hf0, dist_zero_right, dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      ((hQbound _).trans (hsize x hx)) epsilon.coe_nonneg)
  have hQdiff (n m : F) :
      ‖Q (g n - p) - Q (g m - p)‖ ≤ ‖B.toContinuousLinearMap‖ * ‖n - m‖ := by
    have heq : Q (g n - p) - Q (g m - p) = Q (B (n - m) : E) := by
      rw [← map_sub]
      congr 1
      simp only [g, map_sub, Submodule.coe_sub]
      abel
    rw [heq]
    exact (hQbound _).trans (B.toContinuousLinearMap.le_opNorm (n - m))
  let r : Real := (epsilon : Real) * R
  have hr : 0 ≤ r := mul_nonneg epsilon.coe_nonneg hR
  let S := closedBall (0 : F) r
  have hgin (n : S) : g (n : F) ∈ convexHull Real (s : Set E) :=
    hghull n ((mem_closedBall_zero_iff.mp n.property).trans hsmall)
  let H : S → S := fun n =>
    ⟨f (Q (g (n : F) - p)), mem_closedBall_zero_iff.mpr (hfsize _ (hgin n))⟩
  let K : NNReal := epsilon * ‖B.toContinuousLinearMap‖₊
  have hK : K < 1 := by
    change (epsilon : Real) * ‖B.toContinuousLinearMap‖ < 1
    exact (mul_le_mul_of_nonneg_left hBnorm epsilon.coe_nonneg).trans_lt hcontract
  have hH : ContractingWith K H := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
    intro n m
    change dist (f (Q (g (n : F) - p))) (f (Q (g (m : F) - p))) ≤
      (K : Real) * dist (n : F) (m : F)
    have h := hf.dist_le_mul (Q (g (n : F) - p)) (hsource _ (hgin n))
      (Q (g (m : F) - p)) (hsource _ (hgin m))
    simp only [dist_eq_norm] at h ⊢
    calc
      _ ≤ (epsilon : Real) * ‖Q (g (n : F) - p) - Q (g (m : F) - p)‖ := h
      _ ≤ (epsilon : Real) * (‖B.toContinuousLinearMap‖ * ‖(n : F) - (m : F)‖) :=
        mul_le_mul_of_nonneg_left (hQdiff n m) epsilon.coe_nonneg
      _ = (K : Real) * ‖(n : F) - (m : F)‖ := by
        simp only [K, NNReal.coe_mul, coe_nnnorm, mul_assoc]
  let : CompleteSpace S := isClosed_closedBall.isComplete.completeSpace_coe
  let n0 : S := ⟨0, mem_closedBall_self hr⟩
  obtain ⟨n, hn, _⟩ := hH.exists_fixedPoint n0 (edist_ne_top _ _)
  have hfixed : f (Q (g (n : F) - p)) = (n : F) := congrArg Subtype.val hn
  refine ⟨g n, hgin n, (hAg n).trans hfixed.symm, ?_, ?_⟩
  · have heq : ‖g (n : F) - x0‖ = ‖B (n : F)‖ := by
      change ‖x0 + (B (n : F) : E) - x0‖ = ‖(B (n : F) : E)‖
      congr 1
      abel
    rw [heq]
    exact (B.toContinuousLinearMap.le_opNorm n).trans
      (mul_le_mul hBnorm (mem_closedBall_zero_iff.mp n.property)
        (norm_nonneg _) (div_nonneg diam_nonneg ha.le))
  · intro z hz heq
    have hAz : ‖A z‖ ≤ r := by
      rw [heq]
      exact hfsize z hz
    let m : S := ⟨A z, mem_closedBall_zero_iff.mpr hAz⟩
    have hm : Function.IsFixedPt H m := by
      apply Subtype.ext
      change f (Q (g (A z) - p)) = A z
      rw [hcoord z hz]
      exact heq.symm
    have hmn := congrArg Subtype.val (hH.fixedPoint_unique' hm hn)
    exact (hcoord z hz).symm.trans (congrArg g hmn)

end Poincare.Topology

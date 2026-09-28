import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2









noncomputable section

open Set Metric

namespace Poincare.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem isPreconnected_norm_ge (hdim : 1 < Module.rank ℝ E) {r : ℝ}
    (hr : 0 < r) : IsPreconnected {x : E | r ≤ ‖x‖} := by
  have himage : (fun p : ℝ × E => p.1 • p.2) ''
      (Ici r ×ˢ sphere (0 : E) 1) = {x : E | r ≤ ‖x‖} := by
    ext x
    constructor
    · rintro ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
      have hv' : ‖v‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hv
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hr.le.trans ht), hv'] using ht
    · intro hx
      have hx0 : ‖x‖ ≠ 0 := ne_of_gt (hr.trans_le hx)
      refine ⟨(‖x‖, ‖x‖⁻¹ • x), ⟨hx, ?_⟩, ?_⟩
      · simp [norm_smul, inv_mul_cancel₀ hx0]
      · simp [smul_smul, mul_inv_cancel₀ hx0]
  rw [← himage]
  exact (isPreconnected_Ici.prod (isPreconnected_sphere hdim 0 1)).image _ (by fun_prop)



theorem bounded_side_of_compact_complement_partition [Nontrivial E]
    (hdim : 1 < Module.rank ℝ E) {S A B : Set E} (hS : IsCompact S)
    (hA : IsOpen A) (hB : IsOpen B) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Sᶜ) :
    (Bornology.IsBounded A ∧ ¬Bornology.IsBounded B) ∨
      (Bornology.IsBounded B ∧ ¬Bornology.IsBounded A) := by
  obtain ⟨r, hr, hSr⟩ := hS.isBounded.subset_ball_lt 0 (0 : E)
  have houtside : {x : E | r ≤ ‖x‖} ⊆ A ∪ B := by
    intro x hx
    rw [hcover]
    intro hxS
    have hxr : ‖x‖ < r := by simpa [mem_ball, dist_zero_right] using hSr hxS
    exact (not_le_of_gt hxr) hx
  have hnotboth : ¬(Bornology.IsBounded A ∧ Bornology.IsBounded B) := by
    rintro ⟨hAb, hBb⟩
    apply NormedSpace.unbounded_univ ℝ E
    simpa [hcover] using hS.isBounded.union (hAb.union hBb)
  rcases (isPreconnected_norm_ge hdim hr).subset_or_subset hA hB hdisj houtside with hCA | hCB
  · have hBb : Bornology.IsBounded B := by
      apply (isBounded_ball : Bornology.IsBounded (ball (0 : E) r)).subset
      intro x hxB
      simp only [mem_ball, dist_zero_right]
      by_contra hxr
      exact Set.disjoint_left.mp hdisj (hCA (le_of_not_gt hxr)) hxB
    exact Or.inr ⟨hBb, fun hAb => hnotboth ⟨hAb, hBb⟩⟩
  · have hAb : Bornology.IsBounded A := by
      apply (isBounded_ball : Bornology.IsBounded (ball (0 : E) r)).subset
      intro x hxA
      simp only [mem_ball, dist_zero_right]
      by_contra hxr
      exact Set.disjoint_left.mp hdisj hxA (hCB (le_of_not_gt hxr))
    exact Or.inl ⟨hAb, fun hBb => hnotboth ⟨hAb, hBb⟩⟩



theorem bounded_side_of_compact_complement_partition_euclidean_three
    {S A B : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsCompact S)
    (hA : IsOpen A) (hB : IsOpen B) (hdisj : Disjoint A B)
    (hcover : A ∪ B = Sᶜ) :
    (Bornology.IsBounded A ∧ ¬Bornology.IsBounded B) ∨
      (Bornology.IsBounded B ∧ ¬Bornology.IsBounded A) := by
  apply bounded_side_of_compact_complement_partition (E := EuclideanSpace ℝ (Fin 3))
    (by rw [← Module.finrank_eq_rank]; simp) hS hA hB hdisj hcover

end Poincare.Topology

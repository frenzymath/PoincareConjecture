import PoincareConjecture.Proofs.M35.Uniqueness.LocalDistanceMaximum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.Uniqueness

theorem exists_raw_local_small_subsolution
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B L δ : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hδ : 0 < δ) {C₀ : Set StandardCapSpace} (hC₀ : IsCompact C₀) :
    ∃ S : Set StandardCapSpace, IsCompact S ∧ C₀ ⊆ S ∧
      ∀ Q : ℝ → StandardCapSpace → ℝ,
        ContinuousOn (Function.uncurry Q) (Icc 0 T ×ˢ S) →
        (∀ t ∈ Ioc 0 T, ∀ x ∈ S, ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (Q t) x) →
        (∀ x ∈ S, Q 0 x ≤ 0) →
        (∀ t ∈ Icc 0 T, ∀ x ∈ S, Q t x ≤ B) →
        (∀ t ∈ Ioc 0 T, ∀ x ∈ S, ∃ v : ℝ,
          HasDerivWithinAt (fun s => Q s x) v (Icc 0 T) t ∧
            v ≤ (G.flow.connection t).laplacian (Q t) x + L * Q t x) →
        ∀ t ∈ Icc 0 T, ∀ x ∈ C₀, Q t x ≤ δ := by
  obtain ⟨A, _, hcomparison⟩ := exists_raw_local_distance_comparison P G hT hTlt hB hL
  have hecont : Continuous (fun z : ℝ × StandardCapSpace => Real.exp (A * z.1)) := by
    fun_prop
  have hcont := (hecont.continuousOn.mul
    (continuousOn_rawDistanceSquare G hT hTlt (0 : StandardCapSpace))).mono
      (prod_mono Subset.rfl (subset_univ C₀))
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod hC₀).exists_bound_of_continuousOn hcont
  let M := max 0 M₀ + 1
  have hM : 0 < M := by dsimp only [M]; linarith [le_max_left (0 : ℝ) M₀]
  let ε := δ / M
  have hε : 0 < ε := div_pos hδ hM
  obtain ⟨S, hS, hCS, hlocal⟩ := hcomparison ε hε C₀ hC₀
  refine ⟨S, hS, hCS, ?_⟩
  intro Q hQc hQs hQi hQb hQheat
  have hout := hlocal (fun s y => -Q s y) hQc.neg
    (fun s hs y hy => (hQs s hs y hy).neg)
    (fun y hy => neg_nonneg.mpr (hQi y hy))
    (fun s hs y hy => neg_le_neg (hQb s hs y hy)) (fun s hs y hy => ?_)
  · intro t ht x hx
    have hb : Real.exp (A * t) * rawDistanceSquare G 0 t x ≤ M := by
      have hm := (le_abs_self _).trans (hM₀ (t, x) ⟨ht, hx⟩)
      exact hm.trans (by dsimp only [M]; linarith [le_max_right (0 : ℝ) M₀])
    have he : ε * M = δ := div_mul_cancel₀ δ hM.ne'
    have hmul := mul_le_mul_of_nonneg_left hb hε.le
    rw [he, ← mul_assoc] at hmul
    linarith [hout t ht x hx]
  · obtain ⟨v, hv, hvle⟩ := hQheat s hs y hy
    refine ⟨-v, hv.neg, ?_⟩
    have hneg : (fun z => -Q s z) = fun z => (-1 : ℝ) * Q s z := by
      funext z
      ring
    rw [hneg, LeviCivitaData.laplacian_const_mul]
    linarith

end PoincareConjecture.M35.Uniqueness

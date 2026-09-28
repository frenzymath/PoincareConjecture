import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawLowerBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem norm_rawLowerFormOperator_sub_le
    {g h : RiemannianMetric n V} (D : LeviCivitaData g) (E : LeviCivitaData h)
    {K : Set V} (hK : IsClosed K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hη1 : ∀ x, ‖η x‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hcoeff : ∀ x ∈ tsupport η,
      ‖rawLowerCoefficientArray D x - rawLowerCoefficientArray E x‖ ≤ ε) :
    ‖rawLowerFormOperator D hK η hη - rawLowerFormOperator E hK η hη‖ ≤
      (n : ℝ) ^ 2 * (((n : ℝ) + 1) * ε) := by
  have hcut {a b : V → ℝ}
      (hb : ∀ x ∈ tsupport η, ‖a x - b x‖ ≤ ε) (x : V) :
      ‖η x * a x - η x * b x‖ ≤ ε := by
    rw [← mul_sub, norm_mul]
    by_cases hx : η x = 0
    · simpa only [hx, norm_zero, zero_mul] using hε
    · exact (mul_le_mul (hη1 x) (hb x (subset_closure hx)) (norm_nonneg _)
        zero_le_one).trans_eq (one_mul ε)
  apply norm_dirichletVectorLowerOrder_sub_le hK _ _ _ _ hε
  · intro k j i x
    apply hcut _ x
    intro y hy
    let Q := rawLowerCoefficientArray D y - rawLowerCoefficientArray E y
    have he : ‖Q.1 k j i‖ ≤ ‖Q‖ :=
      (((norm_le_pi_norm (Q.1 k j) i).trans (norm_le_pi_norm (Q.1 k) j)).trans
        (norm_le_pi_norm Q.1 k)).trans (norm_fst_le Q)
    exact he.trans (hcoeff y hy)
  · intro k j x
    apply hcut _ x
    intro y hy
    let Q := rawLowerCoefficientArray D y - rawLowerCoefficientArray E y
    have he : ‖Q.2 k j‖ ≤ ‖Q‖ :=
      ((norm_le_pi_norm (Q.2 k) j).trans (norm_le_pi_norm Q.2 k)).trans (norm_snd_le Q)
    exact he.trans (hcoeff y hy)

theorem uniformContinuousOn_rawLowerFormOperator {J I : Set ℝ}
    (F : RicciFlow n V J) (hI : IsCompact I) (hIJ : I ⊆ J)
    {K : Set V} (hK : IsClosed K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hη1 : ∀ x, ‖η x‖ ≤ 1) :
    UniformContinuousOn (fun t => rawLowerFormOperator (F.connection t) hK η hη) I := by
  have hc := (rawLowerCoefficientArray_family_continuousOn F).mono
    (prod_mono hIJ (subset_univ (tsupport η)))
  have hu := (hI.prod hη).uniformContinuousOn_of_continuous hc
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  let d := (n : ℝ) ^ 2 * ((n : ℝ) + 1) + 1
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdiv : 0 < ε / d := div_pos hε hd
  obtain ⟨δ, hδ, hbδ⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / d) hdiv
  refine ⟨δ, hδ, ?_⟩
  intro t ht s hs hts
  have hclose (x : V) (hx : x ∈ tsupport η) :
      ‖rawLowerCoefficientArray (F.connection t) x -
        rawLowerCoefficientArray (F.connection s) x‖ ≤ ε / d := by
    have hp : dist (t, x) (s, x) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hts
    exact le_of_lt (by simpa only [dist_eq_norm] using
      (hbδ (t, x) ⟨ht, hx⟩ (s, x) ⟨hs, hx⟩ hp))
  rw [dist_eq_norm]
  calc
    _ ≤ (n : ℝ) ^ 2 * (((n : ℝ) + 1) * (ε / d)) :=
      norm_rawLowerFormOperator_sub_le _ _ hK η hη hη1 hdiv.le hclose
    _ = ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) * (ε / d) := (mul_assoc _ _ _).symm
    _ < d * (ε / d) := mul_lt_mul_of_pos_right (by dsimp only [d]; linarith) hdiv
    _ = ε := mul_div_cancel₀ ε hd.ne'

theorem continuousOn_rawLowerFormOperator {J I : Set ℝ}
    (F : RicciFlow n V J) (hI : IsCompact I) (hIJ : I ⊆ J)
    {K : Set V} (hK : IsClosed K) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hη1 : ∀ x, ‖η x‖ ≤ 1) :
    ContinuousOn (fun t => rawLowerFormOperator (F.connection t) hK η hη) I :=
  (uniformContinuousOn_rawLowerFormOperator F hI hIJ hK η hη hη1).continuousOn

end PoincareConjecture.M35.Uniqueness.Heat

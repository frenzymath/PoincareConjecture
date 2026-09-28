import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawPrincipalPerturbation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap Matrix.Norms.Elementwise

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem uniformContinuousOn_raw_principalFormOperator {J I : Set ℝ}
    (F : RicciFlow n V J) (hI : IsCompact I) (hIJ : I ⊆ J)
    (K : Set V) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hη1 : ∀ x, ‖η x‖ ≤ 1) :
    UniformContinuousOn (fun t =>
      principalFormOperator K (rawCutoffPrincipalCoefficient (F.metric t) η hη)) I := by
  have hc := (rawInverseGram_family_continuousOn F).mono
    (prod_mono hIJ (subset_univ (tsupport η)))
  have hu := (hI.prod hη).uniformContinuousOn_of_continuous hc
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  let d := (n : ℝ) ^ 2 + 1
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdiv : 0 < ε / d := div_pos hε hd
  obtain ⟨δ, hδ, hbδ⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / d) hdiv
  refine ⟨δ, hδ, ?_⟩
  intro t ht s hs hts
  have hclose (x : V) (hx : x ∈ tsupport η) :
      ‖(rawCoordinateGram (F.metric t) x)⁻¹ -
        (rawCoordinateGram (F.metric s) x)⁻¹‖ ≤ ε / d := by
    have hp : dist (t, x) (s, x) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hts
    exact le_of_lt (by simpa only [dist_eq_norm] using hbδ (t, x) ⟨ht, hx⟩ (s, x) ⟨hs, hx⟩ hp)
  have hcA := rawCutoffPrincipalCoefficient_difference_le (F.metric t) (F.metric s)
    η hη hη1 hdiv.le hclose
  rw [dist_eq_norm]
  calc
    _ ≤ (n : ℝ) ^ 2 * (ε / d) := norm_principalFormOperator_sub_le K _ _ hdiv.le hcA
    _ < d * (ε / d) := mul_lt_mul_of_pos_right (by dsimp only [d]; linarith) hdiv
    _ = ε := mul_div_cancel₀ ε hd.ne'

theorem continuousOn_raw_principalFormOperator {J I : Set ℝ}
    (F : RicciFlow n V J) (hI : IsCompact I) (hIJ : I ⊆ J)
    (K : Set V) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hη1 : ∀ x, ‖η x‖ ≤ 1) :
    ContinuousOn (fun t =>
      principalFormOperator K (rawCutoffPrincipalCoefficient (F.metric t) η hη)) I :=
  (uniformContinuousOn_raw_principalFormOperator F hI hIJ K η hη hη1).continuousOn

end PoincareConjecture.M35.Uniqueness.Heat

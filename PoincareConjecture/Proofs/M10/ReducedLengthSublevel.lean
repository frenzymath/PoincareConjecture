import PoincareConjecture.Proofs.M10.SquarePathCompact










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem exists_compact_reducedLength_sublevel
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {b : ℝ} (hb : 0 < b) (hbmax : b < τmax) (L : ℝ) :
    ∃ C : Set M, IsCompact C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ b → ∀ q : M,
      reducedLength F T p q τ ≤ L → q ∈ C := by
  classical
  obtain ⟨R, hR, hscalar⟩ := exists_uniform_scalarCurvature_bound F hcurvature
  obtain ⟨Q, hQ, hmetric⟩ := exists_uniform_backward_metric_comparison
    (hb.trans hbmax) hwindow hcurvature
  let K : ℝ := 2 * Q * (2 * Real.sqrt b * max L 0 + (2 * R / 3) * b * Real.sqrt b)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let A := {w : TangentSpace (𝓡 n) p × ℝ |
    0 < w.2 ∧ w.2 ≤ b ∧
      G.toLExponentialFamily.action w.1 w.2 ≤ 2 * Real.sqrt w.2 * L}
  have henergy (i : A) :
      (∫ s in 0..Real.sqrt i.val.2, terminalSquareEnergy G i.val.1 s) ≤ K := by
    have ht := i.property.1
    have htb := i.property.2.1
    have htmax := htb.trans_lt hbmax
    have hsqrt : Real.sqrt i.val.2 ≤ Real.sqrt b := Real.sqrt_le_sqrt htb
    have ha : G.toLExponentialFamily.action i.val.1 i.val.2 ≤
        2 * Real.sqrt b * max L 0 := by
      calc
        _ ≤ 2 * Real.sqrt i.val.2 * L := i.property.2.2
        _ ≤ 2 * Real.sqrt i.val.2 * max L 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) (le_max_right _ _)
    have hcorr : (2 * R / 3) * i.val.2 * Real.sqrt i.val.2 ≤
        (2 * R / 3) * b * Real.sqrt b := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left htb (by positivity)) hsqrt (Real.sqrt_nonneg _)
      positivity
    apply (integral_terminalSquareEnergy_le G i.val.1 ht htmax hQ ?_ ?_).trans
      (mul_le_mul_of_nonneg_left (add_le_add ha hcorr) (by positivity))
    · intro r hr q
      exact (abs_le.mp (hscalar (T - r)
        ⟨by linarith [hr.2], by linarith [hr.1]⟩ q)).1
    · intro r hr q v
      exact hmetric r ⟨hr.1, hr.2.trans htmax.le⟩ q v
  obtain ⟨C, hC, hend⟩ := exists_compact_square_endpoints G
    (hcurvature.1 T ⟨by linarith [hb.trans hbmax], le_rfl⟩)
    (fun i : A ↦ i.val.1) (fun i : A ↦ i.val.2) hb hbmax
    (fun i ↦ i.property.1) (fun i ↦ i.property.2.1) hK henergy
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτb q hq
  obtain ⟨Z, hZend, _, hval⟩ := exists_minimizing_lift hL G q τ hτ (hτb.trans_lt hbmax)
  have haction : G.toLExponentialFamily.action Z τ ≤ 2 * Real.sqrt τ * L := by
    rw [hval] at hq
    simpa only [mul_comm L] using
      (div_le_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr hτ))).mp hq
  have hend' := hend (⟨(Z, τ), hτ, hτb, haction⟩ : A)
  simpa only [hZend] using hend'

end PoincareConjecture.M10

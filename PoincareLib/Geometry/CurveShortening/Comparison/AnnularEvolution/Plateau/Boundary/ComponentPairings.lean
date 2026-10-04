import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.NaturalGrowthBounds

/-!
# Exact component pairings for the boundary equation

These identities retain the literal metric flux and its quadratic source,
so the scalar zero-boundary test applies to the actual vector error.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

namespace PoincareMT

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Summing first-coordinate trilinear pairings reconstructs evaluation at the actual
vector. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis.
Project derivation: `proof-work/tasks/M64/derivations/2026-09-26-raised-boundary-source.md`. -/
theorem m64Trilinear_first_pairing (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (v a b : E) :
    (∑ j : Fin n, T (EuclideanSpace.single j 1) a b * v j) = T v a b :=
  M60.suCoordinateDual_pairing ((T.flip a).flip b) v

/-- The component principal pairing is exactly the weighted metric pairing with the actual
error columns. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary
analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-raised-boundary-source.md`. -/
theorem m64WeightedBoundary_principal_pairing
    (G : E →L[ℝ] E →L[ℝ] ℝ) (w : Fin 2 → ℝ) (V D : Fin 2 → E) :
    (∑ j : Fin n, ∑ i : Fin 2,
      (w i * G (V i) (EuclideanSpace.single j 1)) * (V i - D i) j) =
        ∑ i : Fin 2, w i * G (V i) (V i - D i) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc, ← Finset.mul_sum, M60.suCoordinateDual_pairing]

/-- The component variational source pairing is exactly the displayed trilinear vector
pairing. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis.
Project derivation: `proof-work/tasks/M64/derivations/2026-09-26-raised-boundary-source.md`. -/
theorem m64WeightedBoundary_source_pairing
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (w : Fin 2 → ℝ) (V : Fin 2 → E) (v : E) :
    (∑ j : Fin n, (-(∑ i : Fin 2, w i * T (EuclideanSpace.single j 1) (V i) (V i)) /
      2) * v j) = -(∑ i : Fin 2, w i * T v (V i) (V i)) / 2 := by
  have hterms (j : Fin n) :
      (-(∑ i : Fin 2, w i * T (EuclideanSpace.single j 1) (V i) (V i)) / 2) * v j =
        -(∑ i : Fin 2, w i * T (EuclideanSpace.single j 1) (V i) (V i) * v j) / 2 := by
    rw [← Finset.sum_mul]
    ring
  simp_rw [hterms]
  rw [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_comm]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc, ← Finset.mul_sum, m64Trilinear_first_pairing]

/-- Summing component cutoff terms recovers the actual vector metric cross pairing. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/derivations/2026-09-26-raised-boundary-source.md`. -/
theorem m64WeightedBoundary_cross_pairing
    (G : E →L[ℝ] E →L[ℝ] ℝ) (w : Fin 2 → ℝ) (V : Fin 2 → E) (v : E)
    (d : Fin 2 → ℝ) :
    (∑ j : Fin n, ∑ i : Fin 2,
      (w i * G (V i) (EuclideanSpace.single j 1)) * v j * d i) =
        ∑ i : Fin 2, w i * G (V i) v * d i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul]
  congr 1
  simp_rw [mul_assoc, ← Finset.mul_sum, M60.suCoordinateDual_pairing]

end PoincareMT

import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.ReplacementIntegration

/-!
# The exact flux defect of a weak replacement

Integral splitting transports a local Green flux defect to the global
piecewise map. This allows a boundary half-cone to change its diameter
trace. Source: Lemaire 1982, p. 102; M64's free-boundary-
replacement derivation.

Morgan--Tian context: Lemma 19.15, printed pp. 447-449. This project analytic helper
supports the actual annular minimizer and boundary regularity construction.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Filter MeasureTheory

namespace PoincareMT

/-- A prescribed local Green flux defect is the exact global defect of the actual piecewise
fields. Source: the integral-splitting step in M64's free-boundary-replacement derivation.
Source/construction:
proof-work/tasks/M64/derivations/2026-09-26-free-boundary-replacement.md, Missing interface. -/
theorem m64WeakReplacement_flux_defect
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {mu : Measure X} {S K : Set X} [DecidablePred (· ∈ K)]
    (hK : MeasurableSet K) (hKS : K ⊆ S)
    (u0 u1 v0 v1 : X → E) (phi psi : X → ℝ) (delta : E)
    (hu0 : MemLp u0 2 (mu.restrict S)) (hu1 : MemLp u1 2 (mu.restrict K))
    (hv0 : MemLp v0 2 (mu.restrict S)) (hv1 : MemLp v1 2 (mu.restrict K))
    (hphi : MemLp phi 2 (mu.restrict S)) (hpsi : MemLp psi 2 (mu.restrict S))
    (hgreen : (∫ x in K, phi x • v1 x ∂mu) + (∫ x in K, psi x • u1 x ∂mu) =
      (∫ x in K, phi x • v0 x ∂mu) + (∫ x in K, psi x • u0 x ∂mu) + delta) :
    (∫ x in S, phi x • K.piecewise v1 v0 x ∂mu) +
      (∫ x in S, psi x • K.piecewise u1 u0 x ∂mu) =
      (∫ x in S, phi x • v0 x ∂mu) + (∫ x in S, psi x • u0 x ∂mu) + delta := by
  have hpK := hphi.mono_measure (Measure.restrict_mono hKS le_rfl)
  have hqK := hpsi.mono_measure (Measure.restrict_mono hKS le_rfl)
  have heqv : (fun x => phi x • K.piecewise v1 v0 x) =
      K.piecewise (fun x => phi x • v1 x) (fun x => phi x • v0 x) := by
    funext x
    by_cases hx : x ∈ K <;> simp only [piecewise, hx, if_true, if_false]
  have hequ : (fun x => psi x • K.piecewise u1 u0 x) =
      K.piecewise (fun x => psi x • u1 x) (fun x => psi x • u0 x) := by
    funext x
    by_cases hx : x ∈ K <;> simp only [piecewise, hx, if_true, if_false]
  rw [heqv, hequ,
    m64Integral_piecewise_of_subset hK hKS (m64L2_test_integrable hv1 hpK)
      (m64L2_test_integrable hv0 hphi),
    m64Integral_piecewise_of_subset hK hKS (m64L2_test_integrable hu1 hqK)
      (m64L2_test_integrable hu0 hpsi)]
  calc
    _ = ((∫ x in S, phi x • v0 x ∂mu) + (∫ x in S, psi x • u0 x ∂mu)) +
        ((∫ x in K, phi x • v1 x ∂mu) + (∫ x in K, psi x • u1 x ∂mu)) -
        ((∫ x in K, phi x • v0 x ∂mu) + (∫ x in K, psi x • u0 x ∂mu)) := by abel
    _ = _ := by rw [hgreen]; abel

end PoincareMT

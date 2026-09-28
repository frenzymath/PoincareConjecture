import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementIntegration

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

theorem m64WeakReplacement_flux
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {mu : Measure X} {S K : Set X} [DecidablePred (· ∈ K)]
    (hK : MeasurableSet K) (hKS : K ⊆ S)
    (u0 u1 v0 v1 : X → E) (phi psi : X → ℝ)
    (hu0 : MemLp u0 2 (mu.restrict S)) (hu1 : MemLp u1 2 (mu.restrict K))
    (hv0 : MemLp v0 2 (mu.restrict S)) (hv1 : MemLp v1 2 (mu.restrict K))
    (hphi : MemLp phi 2 (mu.restrict S)) (hpsi : MemLp psi 2 (mu.restrict S))
    (hgreen : (∫ x in K, phi x • v1 x ∂mu) + (∫ x in K, psi x • u1 x ∂mu) =
      (∫ x in K, phi x • v0 x ∂mu) + (∫ x in K, psi x • u0 x ∂mu)) :
    (∫ x in S, phi x • K.piecewise v1 v0 x ∂mu) +
      (∫ x in S, psi x • K.piecewise u1 u0 x ∂mu) =
      (∫ x in S, phi x • v0 x ∂mu) + (∫ x in S, psi x • u0 x ∂mu) := by
  classical
  have hpK := hphi.mono_measure (Measure.restrict_mono hKS le_rfl)
  have hqK := hpsi.mono_measure (Measure.restrict_mono hKS le_rfl)
  have heqv : (fun x => phi x • K.piecewise v1 v0 x) =
      K.piecewise (fun x => phi x • v1 x) (fun x => phi x • v0 x) := by
    funext x
    by_cases hx : x ∈ K <;> simp [hx]
  have hequ : (fun x => psi x • K.piecewise u1 u0 x) =
      K.piecewise (fun x => psi x • u1 x) (fun x => psi x • u0 x) := by
    funext x
    by_cases hx : x ∈ K <;> simp [hx]
  rw [heqv, hequ,
    m64Integral_piecewise_of_subset hK hKS (m64L2_test_integrable hv1 hpK)
      (m64L2_test_integrable hv0 hphi),
    m64Integral_piecewise_of_subset hK hKS (m64L2_test_integrable hu1 hqK)
      (m64L2_test_integrable hu0 hpsi)]
  calc
    _ = ((∫ x in S, phi x • v0 x ∂mu) + (∫ x in S, psi x • u0 x ∂mu)) +
        ((∫ x in K, phi x • v1 x ∂mu) + (∫ x in K, psi x • u1 x ∂mu)) -
        ((∫ x in K, phi x • v0 x ∂mu) + (∫ x in K, psi x • u0 x ∂mu)) := by abel
    _ = _ := by rw [hgreen, add_sub_cancel_right]

end PoincareConjecture

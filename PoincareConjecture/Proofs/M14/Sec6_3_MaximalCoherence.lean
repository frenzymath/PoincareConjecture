import PoincareConjecture.Proofs.M14.Sec6_3_MaximalDomain
import PoincareConjecture.Proofs.M14.Sec6_3_InitialValueUnique

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  {T τ s : ℝ} {x y : G.Point} {Z : G.Horizontal x}

include hM04 hM12

theorem initialValueCurve_eq_endpoint (hs : 0 < s)
    (P : M14SquareRootInitialValuePath G T (s ^ 2) x y Z) :
    initialValueCurve G T x Z s = y := by
  have hsurv : initialValueSurvives G T x Z s := ⟨hs, y, ⟨P⟩⟩
  exact initialValuePath_endpoint_eq hM04 hM12 (selectedInitialValuePath hsurv) P

theorem initialValueCurve_eqOn_square (P : M14SquareRootInitialValuePath G T τ x y Z) :
    EqOn (initialValueCurve G T x Z) P.square_path.curve (M14SqrtParameterInterval 0 τ) := by
  intro r hr
  have hr0 : 0 ≤ r := by simpa only [Real.sqrt_zero] using hr.1
  rcases eq_or_lt_of_le hr0 with hr0 | hr0
  · subst r
    exact (initialValueCurve_zero Z).trans P.initial_velocity.choose.symm
  · have hrτ : r ^ 2 ≤ τ := by
      have hsq := (sq_le_sq₀ hr0.le (Real.sqrt_nonneg τ)).mpr hr.2
      simpa only [Real.sq_sqrt P.path.tau_lt.le] using hsq
    exact (initialValueCurve_eq_endpoint hM04 hM12 hr0
      (initialValuePathRestrict P (sq_pos_of_pos hr0) hrτ)).trans (P.square_path.agrees r hr).symm

theorem initialValueCurve_eqOn_path (P : M14SquareRootInitialValuePath G T τ x y Z) :
    EqOn P.path.curve (fun t => initialValueCurve G T x Z (Real.sqrt t)) (Icc 0 τ) := by
  intro t ht
  have hs : Real.sqrt t ∈ M14SqrtParameterInterval 0 τ :=
    ⟨by simpa only [Real.sqrt_zero] using Real.sqrt_nonneg t, Real.sqrt_le_sqrt ht.2⟩
  have heq := (initialValueCurve_eqOn_square hM04 hM12 P hs).trans
    (P.square_path.agrees (Real.sqrt t) hs)
  simpa only [Real.sq_sqrt ht.1] using heq.symm

end PoincareConjecture.M14

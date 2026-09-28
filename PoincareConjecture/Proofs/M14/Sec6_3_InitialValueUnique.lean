import PoincareConjecture.Proofs.M14.Sec6_3_EulerUnique
import PoincareConjecture.Definitions.M14Exponential










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  {T τ σ : ℝ} {x y z : G.Point} {Z : G.Horizontal x}

include hM04 hM12




theorem initialValuePath_square_eqOn
    (P : M14SquareRootInitialValuePath G T τ x y Z)
    (Q : M14SquareRootInitialValuePath G T σ x z Z) :
    EqOn P.square_path.curve Q.square_path.curve (M14SqrtParameterInterval 0 (min τ σ)) := by
  obtain ⟨hP, hvP⟩ := P.initial_velocity
  obtain ⟨hQ, hvQ⟩ := Q.initial_velocity
  have hvel : HEq (P.square_path.horizontal_velocity 0) (Q.square_path.horizontal_velocity 0) := by
    have hp : HEq (hP ▸ P.square_path.horizontal_velocity 0)
        (P.square_path.horizontal_velocity 0) := eqRec_heq _ _
    have hq : HEq (hQ ▸ Q.square_path.horizontal_velocity 0)
        (Q.square_path.horizontal_velocity 0) := eqRec_heq _ _
    exact hp.symm.trans ((heq_of_eq (hvP.trans hvQ.symm)).trans hq)
  have hC : 0 < Real.sqrt (min τ σ) := Real.sqrt_pos.mpr (lt_min P.path.tau_lt Q.path.tau_lt)
  have hsubP : Icc 0 (Real.sqrt (min τ σ)) ⊆ M14SqrtParameterInterval 0 τ := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using
      Icc_subset_Icc (le_refl (0 : ℝ)) (Real.sqrt_le_sqrt (min_le_left τ σ))
  have hsubQ : Icc 0 (Real.sqrt (min τ σ)) ⊆ M14SqrtParameterInterval 0 σ := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using
      Icc_subset_Icc (le_refl (0 : ℝ)) (Real.sqrt_le_sqrt (min_le_right τ σ))
  have hsame := squareRootEuler_unique hM04 hM12 P.square_path Q.square_path hC hsubP hsubQ
    P.extension Q.extension (fun s hs => P.euler s (hsubP hs)) (fun s hs => Q.euler s (hsubQ hs))
    ⟨le_rfl, hC.le⟩ (hP.trans hQ.symm) hvel
  intro s hs
  exact (hsame s (by simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using hs)).1




theorem initialValuePath_curve_eqOn
    (P : M14SquareRootInitialValuePath G T τ x y Z)
    (Q : M14SquareRootInitialValuePath G T σ x z Z) :
    EqOn P.path.curve Q.path.curve (Icc 0 (min τ σ)) := by
  intro t ht
  have hs : Real.sqrt t ∈ M14SqrtParameterInterval 0 (min τ σ) :=
    ⟨by simpa only [Real.sqrt_zero] using Real.sqrt_nonneg t, Real.sqrt_le_sqrt ht.2⟩
  have hp := P.square_path.agrees (Real.sqrt t)
    ⟨hs.1, hs.2.trans (Real.sqrt_le_sqrt (min_le_left τ σ))⟩
  have hq := Q.square_path.agrees (Real.sqrt t)
    ⟨hs.1, hs.2.trans (Real.sqrt_le_sqrt (min_le_right τ σ))⟩
  rw [Real.sq_sqrt ht.1] at hp hq
  exact hp.symm.trans ((initialValuePath_square_eqOn hM04 hM12 P Q hs).trans hq)



theorem initialValuePath_endpoint_eq
    (P : M14SquareRootInitialValuePath G T τ x y Z)
    (Q : M14SquareRootInitialValuePath G T τ x z Z) : y = z := by
  have hτ : τ ∈ Icc 0 (min τ τ) := by simpa only [min_self] using
    (show τ ∈ Icc 0 τ from ⟨P.path.tau_lt.le, le_rfl⟩)
  exact P.path.curve_end.symm.trans
    ((initialValuePath_curve_eqOn hM04 hM12 P Q hτ).trans Q.path.curve_end)

end PoincareConjecture.M14

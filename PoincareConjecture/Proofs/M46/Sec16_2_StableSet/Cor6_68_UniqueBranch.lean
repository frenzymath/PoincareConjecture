import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_68_TerminalMomentum
import PoincareConjecture.Proofs.M14.Sec6_3_EulerUnique
import PoincareConjecture.Proofs.M14.Sec6_3_InitialVector

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x : G.Point}

theorem minimizing_branches_unique_of_differentiable
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {A : Set (G.slices (T - tau)).Point} (hA : IsOpen A)
    (hattained : ∀ q ∈ A, ∃ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p)
    {Z W : G.Horizontal x}
    (hZ : (Z, Real.sqrt tau) ∈ E.domain) (hW : (W, Real.sqrt tau) ∈ E.domain)
    (hcenter : survivalSliceMap E tau htau.le q0 Z ∈ A)
    (hpoint : survivalSliceMap E tau htau.le q0 Z = survivalSliceMap E tau htau.le q0 W)
    (hminZ : M14IsMinimizing (E.path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)))
    (hminW : M14IsMinimizing (E.path W (Real.sqrt tau) hW (Real.sqrt_pos.mpr htau)))
    (hbijZ : Function.Bijective (E.differential Z (Real.sqrt tau) hZ))
    (hbijW : Function.Bijective (E.differential W (Real.sqrt tau) hW))
    (hlength : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun q : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q.val)
      (survivalSliceMap E tau htau.le q0 Z)) : Z = W := by
  let RZ := E.square_path Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau)
  let RW := E.square_path W (Real.sqrt tau) hW (Real.sqrt_pos.mpr htau)
  have hsinterval : M14SqrtParameterInterval 0 ((Real.sqrt tau) ^ 2) =
      Icc 0 (Real.sqrt tau) := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero,
      Real.sqrt_sq (Real.sqrt_nonneg tau)]
  have hsub : Icc 0 (Real.sqrt tau) ⊆
      M14SqrtParameterInterval 0 ((Real.sqrt tau) ^ 2) := by
    rw [hsinterval]
  have hend : RZ.curve (Real.sqrt tau) = RW.curve (Real.sqrt tau) :=
    (survival_square_endpoint E htau q0 hZ).trans
      ((congrArg Subtype.val hpoint).trans (survival_square_endpoint E htau q0 hW).symm)
  have hmomentum := minimizing_terminal_velocities_heq LG E htau q0 hA hattained
    hZ hW hcenter hpoint hminZ hminW hbijZ hbijW hlength
  have hZvel : HEq (survivalTerminalVelocity E htau q0 Z hZ)
      (RZ.horizontal_velocity (Real.sqrt tau)) :=
    eqRec_heq (survival_square_endpoint E htau q0 hZ) _
  have hWvel : HEq (survivalTerminalVelocity E htau q0 W hW)
      (RW.horizontal_velocity (Real.sqrt tau)) :=
    eqRec_heq (survival_square_endpoint E htau q0 hW) _
  have hvelocity := hZvel.symm.trans (hmomentum.trans hWvel)
  have hsame := M14.squareRootEuler_unique hM04 hM12 RZ RW
    (Real.sqrt_pos.mpr htau) hsub hsub
    (E.square_extension Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau))
    (E.square_extension W (Real.sqrt tau) hW (Real.sqrt_pos.mpr htau))
    (fun s hs => E.square_euler Z (Real.sqrt tau) hZ (Real.sqrt_pos.mpr htau) s (hsub hs))
    (fun s hs => E.square_euler W (Real.sqrt tau) hW (Real.sqrt_pos.mpr htau) s (hsub hs))
    ⟨Real.sqrt_nonneg tau, le_rfl⟩ hend hvelocity
  apply M14.initialVector_eq_of_square_branches_eqOn E hZ hW (Real.sqrt_pos.mpr htau)
  intro s hs
  have hs' : s ∈ Icc 0 (Real.sqrt tau) := hsinterval ▸ hs
  exact (M14.exponential_square_curve_eq E Z hZ (Real.sqrt_pos.mpr htau) hs).symm.trans
    ((hsame s hs').1.trans
      (M14.exponential_square_curve_eq E W hW (Real.sqrt_pos.mpr htau) hs))

end PoincareConjecture.Proofs.M46

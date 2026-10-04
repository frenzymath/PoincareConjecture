import PoincareLib.Geometry.RicciFlow.Extinction.Width.Deformation.Data
import PoincareLib.Geometry.Riemannian.LoopSpace.ShortLoops.Statement

/-!
# M66 ordinary-slab width comparison

This file gives the primitive boundary for the smooth-time part of Morgan--Tian
Proposition 18.18.  Surgery-time transport and the lower-limit jump belong to
M67.  The width is the raw M61 free-class infimum for one fixed loop family
viewed through the Ricci-flow metrics on an ordinary slab.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The nontrivial class and component hypotheses for Proposition 18.18.

The raw family in `P` is the width anchor.  Its nontriviality is stated
directly as a concrete free homotopy relation, avoiding an unconnected
duplicate based-class package.
-/
structure M66ClassData {t₀ t₁ : ℝ}
    (P : M65RawFlowInput M t₀ t₁) where
  strict_time : t₀ < t₁
  connected : IsConnected (Set.univ : Set M)
  basepoint : M
  pi_two_subsingleton : Subsingleton (HomotopyGroup.Pi 2 M basepoint)
  /-- The raw nontrivial class boundary used by the M58 short-loop
  contradiction. -/
  raw_nontrivial : ¬ P.family.Homotopic (constantLoopFamily basepoint)
  scalar_infimum_attained : ∀ t : Set.Icc t₀ t₁, ∃ x : M,
    (P.flow.connection t.1).scalarCurvature x =
      flowScalarCurvatureInfimum P.flow t.1
  scalar_infimum_continuous : Continuous (fun t : Set.Icc t₀ t₁ =>
    flowScalarCurvatureInfimum P.flow t.1)

/-- The free-class width of the displayed family at a slab time. -/
noncomputable def m66Width {t₀ t₁ : ℝ}
    (P : M65RawFlowInput M t₀ t₁)
    (t : Set.Icc t₀ t₁) : ℝ :=
  m61FreeClassWidth (P.flow.metric t.1) P.family

end PoincareMT

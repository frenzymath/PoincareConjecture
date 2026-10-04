import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.CapPersistenceIsometryGerm
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.BilinearPullbackJetBound

/-!
# Finite moving-neck jet adapters

These wrappers expose the verified pointwise finite-jet bounds used by the
actual compact convergence producer. They keep the source neighborhoods and
maps local, while their constants are fixed before those choices.
Source: derivations/terminal-curvature-moving-jets.md, Stages H1-H2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology
open Poincare.Analysis.Calculus

namespace PoincareMT.M47

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Finite derivatives of every actual local isometry are bounded from
pointwise metric jets and a fixed quadratic floor. -/
theorem terminalCurvature_exists_moving_isometry_jet_bound
    (m : ℕ) {a K : ℝ} (ha : 0 < a) (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (A B : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ)
      (f : E₃ → E₃) (U V : Set E₃) (x : E₃),
      IsOpen U → IsOpen V → x ∈ U →
      ContDiffOn ℝ ∞ A U → ContDiffOn ℝ ∞ B V → ContDiffOn ℝ ∞ f U →
      (∀ y ∈ U, (A y).IsInvertible) → (∀ y ∈ V, (B y).IsInvertible) →
      (∀ y ∈ V, ∀ v w, B y v w = B y w v) → MapsTo f U V →
      (∀ y ∈ U, ∀ v w,
        A y v w = B (f y) (fderiv ℝ f y v) (fderiv ℝ f y w)) →
      ‖f x‖ ≤ K →
      (∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j A x‖ ≤ K) →
      (∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j B (f x)‖ ≤ K) →
      (∀ v, a * ‖v‖ ^ 2 ≤ A x v v) →
      (∀ v, a * ‖v‖ ^ 2 ≤ B (f x) v v) →
      ∀ j ≤ m + 2, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  simpa only using
    (PoincareMT.CoordinateTransition.exists_local_isometry_germ_jet_bound
      (E := E₃) m ha hK)

/-- A fixed bound on the finite jets of an actual transition map turns a
small coefficient jet error into a small pulled-back coefficient error. -/
theorem terminalCurvature_exists_moving_pullback_jet_bound
    (m : ℕ) {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : E₃ → E₃)
      (B : E₃ → E₃ →L[ℝ] E₃ →L[ℝ] ℝ) (x : E₃),
      ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ B (f x) →
      (∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j f x‖ ≤ D) →
      ∀ A : ℝ, 0 ≤ A →
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j B (f x)‖ ≤ A) →
      ‖iteratedFDeriv ℝ m (fun y => (B (f y)).bilinearComp
        (fderiv ℝ f y) (fderiv ℝ f y)) x‖ ≤ C * A := by
  simpa only using
    (Poincare.Analysis.Calculus.exists_bilinear_pullback_jet_bound
      (E := E₃) (F := E₃) (G := ℝ) m hD)

end PoincareMT.M47

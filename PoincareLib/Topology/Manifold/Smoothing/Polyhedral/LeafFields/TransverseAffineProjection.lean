import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

/-!
# Smooth affine projection along a transverse kernel

The intersection of an affine plane with a transverse affine leaf is given
by an invertible linear system. The solution depends smoothly on the leaf
and its transverse direction. This supplies the calculation in Cairns 1940,
Section 9, p. 806, under Hypotheses III and IV of p. 804.
See M76 derivation 14 for the domain and invertibility requirements.
-/

set_option autoImplicit false

open scoped ContDiff

namespace ContinuousAffineMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Coordinates of the intersection with the affine leaf parallel to `ker Q`.
Its geometric meaning requires invertibility of `Q` on the plane's linear
part; see Cairns p. 806 and M76 derivation 14. -/
noncomputable def transverseCoordinates (b : F →ᴬ[𝕜] E) (Q : E →L[𝕜] F) (x : E) : F :=
  (Q.comp b.contLinear).inverse (Q (x - b 0))

/-- Transverse coordinates are the unique solution of the affine-leaf
intersection equation. See Cairns p. 806 and M76 derivation 14. -/
theorem transverseCoordinates_eq_iff (b : F →ᴬ[𝕜] E) (Q : E →L[𝕜] F)
    (hQ : (Q.comp b.contLinear).IsInvertible) (x : E) (y : F) :
    b.transverseCoordinates Q x = y ↔ Q (b y - x) = 0 := by
  have hlin : b.contLinear y = b y - b 0 := by
    simpa using b.contLinear_map_vsub y 0
  rw [transverseCoordinates, hQ.inverse_apply_eq, ContinuousLinearMap.comp_apply, hlin]
  simp only [map_sub, sub_left_inj, sub_eq_zero]
  exact eq_comm

/-- A transverse projection fixes the coordinates of points already on the
target affine plane. See M76 derivation 14. -/
theorem transverseCoordinates_apply_self (b : F →ᴬ[𝕜] E) (Q : E →L[𝕜] F)
    (hQ : (Q.comp b.contLinear).IsInvertible) (y : F) :
    b.transverseCoordinates Q (b y) = y := by
  apply (b.transverseCoordinates_eq_iff Q hQ _ _).mpr
  simp

variable [CompleteSpace F] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {r : ℕ∞ω} {P : X → E →L[𝕜] F} {v : X → E} {x : X}

/-- The affine intersection coordinates vary smoothly wherever the transverse
linear system is invertible. See Cairns p. 806 and M76 derivation 14. -/
theorem contDiffAt_transverseCoordinates (b : F →ᴬ[𝕜] E)
    (hP : ContDiffAt 𝕜 r P x) (hv : ContDiffAt 𝕜 r v x)
    (htrans : ((P x).comp b.contLinear).IsInvertible) :
    ContDiffAt 𝕜 r (fun y => b.transverseCoordinates (P y) (v y)) x := by
  have hA : ContDiffAt 𝕜 r (fun y => (P y).comp b.contLinear) x :=
    hP.clm_comp contDiffAt_const
  have hinv := htrans.contDiffAt_map_inverse.comp x hA
  exact hinv.clm_apply (hP.clm_apply (hv.sub contDiffAt_const))

end ContinuousAffineMap

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

set_option autoImplicit false

open scoped ContDiff

namespace ContinuousAffineMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

noncomputable def transverseCoordinates (b : F →ᴬ[𝕜] E) (Q : E →L[𝕜] F) (x : E) : F :=
  (Q.comp b.contLinear).inverse (Q (x - b 0))

theorem transverseCoordinates_eq_iff (b : F →ᴬ[𝕜] E) (Q : E →L[𝕜] F)
    (hQ : (Q.comp b.contLinear).IsInvertible) (x : E) (y : F) :
    b.transverseCoordinates Q x = y ↔ Q (b y - x) = 0 := by
  have hlin : b.contLinear y = b y - b 0 := by
    simpa using b.contLinear_map_vsub y 0
  rw [transverseCoordinates, hQ.inverse_apply_eq, ContinuousLinearMap.comp_apply, hlin]
  simp only [map_sub, sub_left_inj, sub_eq_zero]
  exact eq_comm

theorem transverseCoordinates_apply_self (b : F →ᴬ[𝕜] E) (Q : E →L[𝕜] F)
    (hQ : (Q.comp b.contLinear).IsInvertible) (y : F) :
    b.transverseCoordinates Q (b y) = y := by
  apply (b.transverseCoordinates_eq_iff Q hQ _ _).mpr
  simp

variable [CompleteSpace F] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {r : ℕ∞ω} {P : X → E →L[𝕜] F} {v : X → E} {x : X}

theorem contDiffAt_transverseCoordinates (b : F →ᴬ[𝕜] E)
    (hP : ContDiffAt 𝕜 r P x) (hv : ContDiffAt 𝕜 r v x)
    (htrans : ((P x).comp b.contLinear).IsInvertible) :
    ContDiffAt 𝕜 r (fun y => b.transverseCoordinates (P y) (v y)) x := by
  have hA : ContDiffAt 𝕜 r (fun y => (P y).comp b.contLinear) x :=
    hP.clm_comp contDiffAt_const
  have hinv := htrans.contDiffAt_map_inverse.comp x hA
  exact hinv.clm_apply (hP.clm_apply (hv.sub contDiffAt_const))

end ContinuousAffineMap

import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.ResolutionCopies
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalStripEndPaths
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.ResolutionEndHomotopies



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1

def spanningEndPoint (i sign : Bool) : endSquare 0 :=
  ⟨((farArmParameter sign, if i then -farArmParameter sign else farArmParameter sign), 0), by
    cases i <;> cases sign <;> norm_num [endSquare, farArmParameter]⟩

noncomputable def spanningOldEndPath (i sign : Bool) :
    Path (spanningEndPoint i sign) (spanningEndPoint i (!sign)) where
  toFun t := ⟨((originalStripEndParameter (!sign) t,
    if i then -originalStripEndParameter (!sign) t else originalStripEndParameter (!sign) t), 0), by
      have h := originalStripEndParameter_mem (!sign) t
      refine ⟨⟨h, ?_⟩, rfl⟩
      cases i
      · exact h
      · change -1 ≤ -originalStripEndParameter (!sign) t ∧
          -originalStripEndParameter (!sign) t ≤ 1
        constructor <;> linarith [h.1, h.2]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    cases i <;> dsimp [originalStripEndParameter] <;> fun_prop
  source' := by apply Subtype.ext; simp [spanningEndPoint]
  target' := by apply Subtype.ext; simp [spanningEndPoint]

noncomputable def spanningResolvingEndPath (sign : Bool → Bool) :
    Path (spanningEndPoint false (sign false)) (spanningEndPoint true (sign true)) where
  toFun t := ⟨tubeArmOrientation (!(sign false)) (!(sign true)) (resolvingSquare true (t, 0)), by
    have hz : resolvingSquare true (t, 0) ∈ tube :=
      resolvingSquare_mapsTo true ⟨t.property, by norm_num⟩
    have h := (tubeArmOrientation_mem_tube (!(sign false)) (!(sign true)) _).mpr hz
    refine ⟨h.1, ?_⟩
    rw [tubeArmOrientation_longitudinal]
    rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (tubeArmOrientation (!(sign false)) (!(sign true))).continuous.comp
    change Continuous (fun t : I ↦ strip (1 / 4) true (0, 2 * (t : ℝ) - 1))
    exact ((continuous_maps (1 / 4) true).1).comp (by fun_prop)
  source' := by
    apply Subtype.ext
    change tubeArmOrientation (!(sign false)) (!(sign true)) (resolvingSquare true (0, 0)) = _
    have h := (tubeArmOrientation_corners (!(sign false)) (!(sign true)) 0).1
    convert h using 1 <;>
      norm_num [resolvingSquare, squareStripCoordinates, strip, signedHeight, height, spanningEndPoint]
  target' := by
    apply Subtype.ext
    change tubeArmOrientation (!(sign false)) (!(sign true)) (resolvingSquare true (1, 0)) = _
    have h := (tubeArmOrientation_corners (!(sign false)) (!(sign true)) 0).2.2.2
    convert h using 1 <;>
      norm_num [resolvingSquare, squareStripCoordinates, strip, signedHeight, height, spanningEndPoint]

theorem spanningOldEndPath_val (i sign : Bool) (t : I) :
    (spanningOldEndPath i sign t : C3) =
      ((originalStripEndParameter (!sign) t,
        if i then -originalStripEndParameter (!sign) t else originalStripEndParameter (!sign) t), 0) :=
  rfl

theorem spanningResolvingEndPath_val (sign : Bool → Bool) (t : I) :
    (spanningResolvingEndPath sign t : C3) =
      tubeArmOrientation (!(sign false)) (!(sign true)) (resolvingSquare true (t, 0)) := rfl

end PoincareConjecture.M76.Dehn

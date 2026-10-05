import PoincareLib.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Theory
import PoincareLib.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ModelVolume

/-!
# Fixed constants for the universal noncollapsing estimate

The normalized cylinder determines all three source constants before any
ancient solution is supplied. The given generalized noncollapsing theorem
then produces one positive constant for those fixed inputs.
Reference: Morgan--Tian, Proposition 9.58, pp. 220--221.
-/

noncomputable section
set_option autoImplicit false

universe u

namespace PoincareMT

def universalNoncollapseTime : ℝ := 2

def universalNoncollapseLength : ℝ := 10 * (1 + Real.exp 4)

def universalNoncollapseVolume : ℝ := universalNoncollapseModelVolume / 8

theorem universalNoncollapseTime_pos : 0 < universalNoncollapseTime := by
  norm_num [universalNoncollapseTime]

theorem universalNoncollapseLength_pos : 0 < universalNoncollapseLength := by
  unfold universalNoncollapseLength
  positivity

theorem universalNoncollapseVolume_pos : 0 < universalNoncollapseVolume :=
  div_pos universalNoncollapseModelVolume_pos (by norm_num)

def universalNoncollapseEstimate (H : M15GeneralizedUniformTheorem.{u} 3) :
    M15GeneralizedUniformData.{u} 3 universalNoncollapseTime
      universalNoncollapseLength universalNoncollapseVolume :=
  Classical.choice (H _ _ _ universalNoncollapseTime_pos
    universalNoncollapseLength_pos universalNoncollapseVolume_pos)

def universalNoncollapseData (H : M15GeneralizedUniformTheorem.{u} 3) :
    UniversalNoncollapsingData where
  universal_kappa := (universalNoncollapseEstimate H).kappa
  universal_kappa_pos := (universalNoncollapseEstimate H).kappa_pos

end PoincareMT

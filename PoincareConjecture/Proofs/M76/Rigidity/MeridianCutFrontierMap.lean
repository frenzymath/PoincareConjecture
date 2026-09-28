import PoincareConjecture.Proofs.M76.Rigidity.MarkedMeridianStrip
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

variable {ι : Type*} {e : ι → OpenPartialHomeomorph X V3} {j : V2 → X}



noncomputable def meridianCutFrontierMap (P : OriginalDiskProduct e R j) (a : ℝ) : E → X := by
  classical
  exact fun z => if z.2 = a / 2 then P.map (z.1, (1 / 2 : ℝ)) else
    if z.2 = p - a / 2 then P.map (z.1, -(1 / 2 : ℝ)) else
      hamiltonMeridianCutAmbientMap z


theorem meridianCutFrontierMap_lower (P : OriginalDiskProduct e R j) (a : ℝ) (z : V2) :
    P.meridianCutFrontierMap a (z, a / 2) = P.map (z, (1 / 2 : ℝ)) := by
  simp [meridianCutFrontierMap]


theorem meridianCutFrontierMap_upper (P : OriginalDiskProduct e R j) {a : ℝ}
    (hgap : a / 2 < p - a / 2) (z : V2) :
    P.meridianCutFrontierMap a (z, p - a / 2) = P.map (z, -(1 / 2 : ℝ)) := by
  simp [meridianCutFrontierMap, ne_of_gt hgap]



theorem meridianCutFrontierMap_lateral (P : OriginalDiskProduct e R j) {a : ℝ}
    (hgap : a / 2 < p - a / 2)
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t))
    (z : E) (hz : z.1 ∈ Q) :
    P.meridianCutFrontierMap a z = hamiltonMeridianCutAmbientMap z := by
  classical
  obtain ⟨hplus, hminus⟩ := P.marked_meridian_cap_rims hmark
  by_cases hlow : z.2 = a / 2
  · have heq : z = (z.1, a / 2) := Prod.ext rfl hlow
    rw [heq, P.meridianCutFrontierMap_lower]
    exact hplus _ hz
  · by_cases hupp : z.2 = p - a / 2
    · have heq : z = (z.1, p - a / 2) := Prod.ext rfl hupp
      rw [heq, P.meridianCutFrontierMap_upper hgap]
      exact hminus _ hz
    · simp only [meridianCutFrontierMap, if_neg hlow, if_neg hupp]

end PoincareConjecture.M76.OriginalDiskProduct

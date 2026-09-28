import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.CylinderLift
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmptyInteriorFaceDimension

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)

theorem source_interior_empty : interior source = ∅ := by
  change interior (closedBall (0 : V1) 1 ×ˢ sphere (0 : V2) 1) = ∅
  rw [interior_prod_eq, interior_sphere _ one_ne_zero, prod_empty]

theorem source_face_card_le (K : SimplicialComplex ℝ (V1 × V2))
    (hK : K.space = source) {a : Finset (V1 × V2)} (ha : a ∈ K.faces) : a.card ≤ 3 := by
  have hdim : Module.finrank ℝ (V1 × V2) = 3 := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun]
  have h := K.face_card_le_of_interior_space_eq_empty
    (hK ▸ source_interior_empty) ha
  rwa [hdim] at h

end PoincareConjecture.M76.Dehn.ProtectedAnnulus

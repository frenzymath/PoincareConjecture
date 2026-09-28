import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralCapFlattening
import PoincareConjecture.Proofs.M76.Mathlib.ConvexSectionBallPair
import PoincareConjecture.Proofs.M76.Mathlib.AffineHyperplaneCoordinates











set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]





theorem isFinitePLBallPair_convex_frontier_cap (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {s : Set E} (hs : IsCompact s) (hcv : Convex ℝ s)
    (hs0 : (0 : E) ∈ interior s) (hspace : K.space = s)
    (L : E →ₗ[ℝ] ℝ) (hL : L ≠ 0)
    (hne : (interior s ∩ {x | L x = 1}).Nonempty)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1) :
    IsFinitePLBallPair F (frontier s ∩ {x | 1 ≤ L x}) (frontier s ∩ {x | L x = 1}) := by
  obtain ⟨H, hH, _, hHb⟩ :=
    K.exists_finitePL_polyhedral_cap_flattening hK hs hcv hs0 hspace L
  have hcopy := hH.symm
  obtain ⟨_, ⟨J, hJ, hJspace, _⟩, _⟩ := hcopy
  let A : E →ᵃ[ℝ] ℝ := L.toAffineMap - AffineMap.const ℝ E 1
  have hA : A.linear ≠ 0 := by simpa [A] using hL
  obtain ⟨a, r, hleft, hright, ha⟩ := A.exists_zeroLevel_coordinates (F := F) hA hdim
  have hr : LeftInvOn a r {x | L x = 1} := by
    intro x hx
    apply hright
    exact sub_eq_zero.mpr hx
  have hai (y : F) : L (a y) = 1 := sub_eq_zero.mp (ha y)
  have hT := hs.isFinitePLBallPair_affine_section hcv L a r hleft hr hai hne J hJ hJspace
  have hq : frontier s ∩ {x | L x = 1} ⊆ frontier s ∩ {x | 1 ≤ L x} :=
    fun x hx => ⟨hx.1, hx.2.ge⟩
  apply hT.of_homeomorph hq H hH
  intro x
  simpa only [mem_inter_iff, mem_ofPred_eq, x.property.1, true_and,
    (H x).property.2, and_true] using hHb x

end Geometry.SimplicialComplex

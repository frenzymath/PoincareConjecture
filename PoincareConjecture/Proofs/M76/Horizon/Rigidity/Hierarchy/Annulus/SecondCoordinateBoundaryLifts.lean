import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SecondCoordinateLifts
import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))

theorem exists_hamiltonZero_second_coordinate_boundary_lift {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {R : Set X0} (he : PLDomain e R) (x : X0) (hx : x ∈ frontier R) :
    ∃ (G : OpenPartialHomeomorph X0 V3) (psi : V3 →ᴬ[ℝ] ℝ) (u : V3)
      (K : SimplicialComplex ℝ V3) (w : V3 → ℝ),
      psi.contLinear u = 1 ∧ x ∈ G.source ∧ psi (G x) = 0 ∧
      G x ∈ interior K.space ∧ K.faces.Finite ∧ K.space ⊆ G.target ∧
      K.AffineOnFaces w ∧ K.RespectsAffineHyperplane psi.toAffineMap ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source, y ∈ R ↔ 0 ≤ psi (G y)) ∧
      ∀ y ∈ G.source, G y ∈ K.space →
        hamiltonZeroSecondCircleMap phi y = (w (G y) : C0) := by
  classical
  obtain ⟨psi, u, G, hu, hxG, hxzero, hG, hGR⟩ := he.halfspace x hx
  obtain ⟨K, w, hK, hxK, hKt, hw, hlift⟩ :=
    exists_hamiltonZeroSecondCircleMap_lift_in_compatible_chart e d hd phi hphi x G hG hxG
  let n := hK.toFinset.sup Finset.card
  have hn (s : Finset V3) (hs : s ∈ K.faces) : s.card ≤ n + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ n)
  obtain ⟨J, hJ, hJK, _, hJpsi⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hK hn {psi.toAffineMap}
  refine ⟨G, psi, u, J, w, hu, hxG, hxzero, ?_, hJ, ?_,
    hJK.affineOnFaces hw, hJpsi psi.toAffineMap (Finset.mem_singleton_self _), hG, hGR, ?_⟩
  · simpa only [hJK.space_eq] using hxK
  · rw [hJK.space_eq]; exact hKt
  · intro y hyG hyJ
    exact hlift y hyG (hJK.space_eq.subset hyJ)

end PoincareConjecture.M76

import PoincareConjecture.Proofs.M76.Triangulation.HamiltonSphereInverseCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnitCubePLCollar
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineProd
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]




theorem ChartwisePLSphere.cap_interior_transition_mem_piecewiseAffineGroupoid
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (c H C : OpenPartialHomeomorph X V3)
    (hcompat : ∀ i, (e i).symm.trans c ∈ piecewiseAffineGroupoid V3)
    (z : V3 →ᴬ[ℝ] V3) (d : V3 →ᴬ[ℝ] ℝ)
    (hzt : MapsTo z (H.symm.trans C).source c.target)
    (himage : ∀ y ∈ (H.symm.trans C).source, c.symm (z y) ∈ S)
    (hformula : ∀ y (hy : y ∈ (H.symm.trans C).source),
      C (H.symm y) = unitCubeInwardCollarMap
        ((s.parametrization.symm ⟨c.symm (z y), himage y hy⟩ : V3), d y)) :
    H.symm.trans C ∈ piecewiseAffineGroupoid V3 := by
  let U := (H.symm.trans C).source
  have hU : IsOpen U := (H.symm.trans C).open_source
  obtain ⟨q, hq, hqval⟩ := s.exists_locallyPL_inverse_chart_parameterization
    c hcompat (locallyPiecewiseAffineOn_affine z hU) hzt himage
  have hp := hq.prod_mk (locallyPiecewiseAffineOn_affine d hU)
  have hPL : LocallyPiecewiseAffineOn
      (fun y => unitCubeInwardCollarMap (q y, d y)) U := by
    have h := locallyPiecewiseAffineOn_unitCubeInwardCollarMap.comp hp
    simpa only [preimage_univ, inter_univ, Function.comp_def] using h
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  apply hPL.congr
  intro y hy
  change unitCubeInwardCollarMap (q y, d y) = C (H.symm y)
  rw [hformula y hy, hqval y hy]

end PoincareConjecture.M76

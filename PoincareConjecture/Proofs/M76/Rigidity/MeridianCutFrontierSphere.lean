import PoincareConjecture.Proofs.M76.Rigidity.MeridianCutFrontierHomeomorph
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundarySphere

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Q3" => sphere (0 : V3) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

variable {ι : Type*} {e : ι → OpenPartialHomeomorph X V3} {j : V2 → X}

theorem nonempty_chartwisePLSphere_cut (P : OriginalDiskProduct e R j)
    (he : PLDomain e R) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    {a : ℝ} (ha : 0 < a) (hasmall : a ≤ 1 / 2)
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t))
    (hC : PolyhedralPLInCharts e hamiltonMeridianCutAmbientMap
      (Q ×ˢ Icc (a / 2) (p - a / 2))) :
    Nonempty (ChartwisePLSphere e (frontier P.cutCarrier)) := by
  have hgap : a / 2 < p - a / 2 := by norm_num at hasmall ⊢; linarith
  obtain ⟨H, hHval⟩ := P.exists_meridianCutFrontier_homeomorph
    he hR hopen ha hasmall hmark hC
  obtain ⟨c, g, hg, hcval⟩ := exists_finitePL_cubePrismBoundary_sphere hgap
  obtain ⟨K, hK, hKQ⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hgK : FinitePiecewiseAffineOn g K.space := hKQ.symm ▸ hg
  have hmap : MapsTo g K.space (cubePrismBoundary (a / 2) (p - a / 2)) := by
    intro z hz
    rw [← hcval ⟨z, hKQ.subset hz⟩]
    exact (c ⟨z, hKQ.subset hz⟩).property
  have hPL := (P.polyhedral_meridianCutFrontierMap he hgap hmark hC).comp_finitePiecewiseAffineOn
    K hK hgK hmap
  refine ⟨{
    parametrization := c.trans H
    map := P.meridianCutFrontierMap a ∘ g
    map_eq := ?_
    piecewiseAffine := hKQ ▸ hPL
  }⟩
  intro z
  change P.meridianCutFrontierMap a (g z) = (H (c z) : X)
  rw [← hcval z, hHval]

end PoincareConjecture.M76.OriginalDiskProduct

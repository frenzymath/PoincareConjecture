import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.MeridianBand
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.SourceBoundaryCylinder

/-!
# The literal signed meridian band in the original source atlas

The whole target band certificate transfers through the given map's
fixed original boundary. The signed endpoints remain in the same
finite carrier and retain their literal quotient values. See037.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "I" => Icc (-1 : ℝ) 1

/-- The unchanged full signed band is PL in the original arbitrary
source atlas. Its actual short quotient chart already supplies the
whole injectivity and openness. See rigidity037, section5. -/
theorem polyhedralPL_source_hamiltonMeridianBand
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 2) (Fin 1) L phi))
    (F : (ContinuousMap.id H).HomotopyRel phi B) :
    PolyhedralPLInCharts e hamiltonMeridianCutAmbientMap (Q ×ˢ I) := by
  classical
  let R := latticeHandleDomain (Fin 2) (Fin 1) L
  let f := latticeHandleMapInDomain (Fin 2) (Fin 1) L phi
  let F' := latticeHandleMapInDomain_homotopyRel (Fin 2) (Fin 1) L phi F
  let q : (V2 × ℝ) → R := fun z => if hz : z.1 ∈ D then
    ⟨hamiltonMeridianCutAmbientMap z, hz, mem_univ _⟩ else
      ⟨(0, 0), mem_closedBall_self zero_le_one, mem_univ _⟩
  have hqval (z : V2 × ℝ) (hz : z ∈ Q ×ˢ I) :
      (q z : X) = hamiltonMeridianCutAmbientMap z := by
    simp only [q, dif_pos (sphere_subset_closedBall hz.1)]
  have hq : ContinuousOn q (Q ×ˢ I) :=
    Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
      (continuous_hamiltonMeridianCutAmbientMap.continuousOn.congr hqval)
  have hqB : MapsTo q (Q ×ˢ I) ((Subtype.val : R → X) ⁻¹' frontier R) := by
    intro z hz
    change (q z : X) ∈ frontier R
    rw [hqval z hz]
    exact mapsTo_hamiltonMeridianBand_frontier hz
  have hfix (x : R) (hx : (x : X) ∈ frontier R) : f x = x :=
    (F'.fst_eq_snd hx).symm
  have hqPL : PolyhedralPLInCharts d (fun z => (q z : X)) (Q ×ˢ I) :=
    hd.polyhedralPL_meridianBand.congr (fun z hz => (hqval z hz).symm)
  obtain ⟨K, hK, hKA⟩ := exists_finite_hamiltonMeridianBand
    (a := (-1 : ℝ)) (b := 1) (by norm_num)
  have hqK : ContinuousOn q K.space := hKA.symm ▸ hq
  have hqBK : MapsTo q K.space ((Subtype.val : R → X) ⁻¹' frontier R) :=
    hKA.symm ▸ hqB
  have hqPLK : PolyhedralPLInCharts d (fun z => (q z : X)) K.space :=
    hKA.symm ▸ hqPL
  have hsource := hphi.polyhedralPLInCharts_boundary_fixed hfix K hK q hqK hqBK hqPLK
  rw [hKA] at hsource
  exact hsource.congr hqval

end PoincareMT.M76

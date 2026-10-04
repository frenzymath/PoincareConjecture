import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Levels.ShortCutParameters
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.EmbeddedParameterCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.PolyhedralPLComposition
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.PolyhedralPLGluing

/-!
# Original PL coordinates across the complete identified meridian

The literal period shift certifies the same composite on the
negative and positive halves of a signed box. Finite pasting and
actual embedded parameters then give the original chartwise map.
See Hudson pp.12--19 and rigidity derivation 010.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

variable {α β : Type*}
  {e : α → OpenPartialHomeomorph X (Fin 3 → ℝ)}
  {d : β → OpenPartialHomeomorph X (Fin 3 → ℝ)}

/-- The complete cut formula gives the same PL composite across
both identified end disks, including their whole rims.
See rigidity derivation 010, section 2. -/
theorem polyhedralPL_hamiltonMeridian_signed_composite
    (he : PLDomain e R) (f : C(R, R))
    (hcut : PolyhedralPLInCharts e (fun z => (f (hamiltonMeridianParameter z) : X))
      (D ×ˢ Icc 0 p)) :
    PolyhedralPLInCharts e (fun z => (f (hamiltonMeridianParameter z) : X))
      (D ×ˢ Icc (-1) 1) := by
  obtain ⟨K, hK, hKbox⟩ := exists_finite_hamiltonMeridianBox
    (show (-1 : ℝ) < 1 by norm_num)
  obtain ⟨Kplus, hKplus, hKplusbox⟩ := exists_finite_hamiltonMeridianBox
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨Kminus, hKminus, hKminusbox⟩ := exists_finite_hamiltonMeridianBox
    (show (-1 : ℝ) < 0 by norm_num)
  let F : (V2 × ℝ) → X := fun z => f (hamiltonMeridianParameter z)
  have hplus : PolyhedralPLInCharts e F Kplus.space :=
    hcut.restrict_finite Kplus hKplus (by
      intro z hz
      obtain ⟨hzD, hz0, hz1⟩ := hKplusbox.subset hz
      exact ⟨hzD, hz0, by linarith⟩)
  let A : (V2 × ℝ) →ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousAffineEquiv.constVAdd ℝ (V2 × ℝ) (0, p)).toContinuousAffineMap
  have hAvalue (z : V2 × ℝ) : A z = (z.1, z.2 + p) := by
    change ((0 : V2) + z.1, p + z.2) = (z.1, z.2 + p)
    rw [zero_add, add_comm p z.2]
  have hA : FinitePiecewiseAffineOn A Kminus.space :=
    ⟨Kminus, hKminus, rfl, Kminus.affineOnFaces_affine A⟩
  have hmap : MapsTo A Kminus.space (D ×ˢ Icc 0 p) := by
    intro z hz
    rw [hAvalue]
    obtain ⟨hzD, hzm, hz0⟩ := hKminusbox.subset hz
    exact ⟨hzD, by linarith, by linarith⟩
  have hminus : PolyhedralPLInCharts e F Kminus.space :=
    (hcut.comp_finitePiecewiseAffineOn Kminus hKminus hA hmap).congr (by
      intro z _
      change (f (hamiltonMeridianParameter (A z)) : X) =
        (f (hamiltonMeridianParameter z) : X)
      rw [hAvalue, hamiltonMeridianParameter_period])
  let J : Bool → SimplicialComplex ℝ (V2 × ℝ) := fun i => cond i Kplus Kminus
  have hJ : ∀ i, (J i).faces.Finite := by
    intro i
    cases i
    · exact hKminus
    · exact hKplus
  have hPL : ∀ i, PolyhedralPLInCharts e F (J i).space := by
    intro i
    cases i
    · exact hminus
    · exact hplus
  have hcont : ContinuousOn F K.space :=
    continuous_subtype_val.comp_continuousOn
      (f.continuous.comp_continuousOn (continuousOn_hamiltonMeridianParameter.mono
        (fun z hz => ⟨(hKbox.subset hz).1, mem_univ _⟩)))
  have hcover : K.space ⊆ ⋃ i, (J i).space := by
    intro z hz
    obtain ⟨hzD, hzm, hz1⟩ := hKbox.subset hz
    by_cases ht : 0 ≤ z.2
    · exact mem_iUnion.mpr ⟨true, hKplusbox.symm.subset ⟨hzD, ht, hz1⟩⟩
    · exact mem_iUnion.mpr ⟨false,
        hKminusbox.symm.subset ⟨hzD, hzm, (lt_of_not_ge ht).le⟩⟩
  have hF := polyhedralPLInCharts_of_finite_cover he.cover he.compatible
    K hK J hJ hcont hPL hcover
  exact hKbox ▸ hF

/-- A full PL cut composite descends to the unchanged original
chartwise map predicate. The actual short parameters include
every old boundary point. See rigidity derivation 010, section 3. -/
theorem StandardLatticeHandleAtlas.chartwisePLMap_of_meridianCut
    (hd : StandardLatticeHandleAtlas (Fin 2) (Fin 1) L d)
    (he : PLDomain e R) (f : C(R, R))
    (hcut : PolyhedralPLInCharts e (fun z => (f (hamiltonMeridianParameter z) : X))
      (D ×ˢ Icc 0 p)) :
    ChartwisePLMap d e f := by
  apply chartwisePLMap_of_embedded_polyhedral_parameters (E := V2 × ℝ) d e hd.domain he f
  intro x
  obtain ⟨a, b, K, z, hab, hK, hKbox, hqz, hQ, hnbhd, hcase⟩ :=
    exists_hamiltonMeridian_short_box x
  refine ⟨K, hamiltonMeridianParameter, z, hK,
    continuousOn_hamiltonMeridianParameter.mono
      (fun u hu => ⟨(hKbox.subset hu).1, mem_univ _⟩), hQ, hqz, hnbhd, ?_, ?_⟩
  · exact hKbox.symm ▸ hd.polyhedralPL_meridianParameter hab
  · rcases hcase with ⟨rfl, rfl⟩ | ⟨ha, hb⟩
    · exact hKbox.symm ▸ polyhedralPL_hamiltonMeridian_signed_composite he f hcut
    · apply hcut.restrict_finite K hK
      intro u hu
      obtain ⟨huD, hua, hub⟩ := hKbox.subset hu
      exact ⟨huD, (ha.trans_le hua).le, (hub.trans_lt hb).le⟩

end PoincareMT.M76

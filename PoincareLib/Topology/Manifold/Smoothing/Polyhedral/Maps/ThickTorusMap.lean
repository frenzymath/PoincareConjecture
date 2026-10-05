import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.StableAnnulusMap
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CubeShellGeometry
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PiecewiseAffineProd

/-!
# The actual two-annulus map of a bounded thick torus

Two concrete annulus coordinates, with their literal
intermediate height bound, embed the bounded real factor
and two circles in three-dimensional real space. The
central cube formula is exact. See Hamilton 1976, p. 66
and M76 derivations 270 and 279.
-/

set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace ThickTorus

/-- The actual period-64 circle in the annulus construction.
See M76 derivation 279. -/
abbrev Circle := AddCircle (4 * (16 : ℝ))

/-- The literal two-annulus map with successive transverse
scales 64 and final inverse scale 4096. Its useful domain
is the bounded real cylinder. See M76 derivation 279. -/
noncomputable def map (z : (ℝ × Circle) × Circle) : CubeShell.Ambient :=
  let u := centeredAnnulusMap 16 (by norm_num) (z.1.2, z.1.1 / 64)
  let v := centeredAnnulusMap 16 (by norm_num) (z.2, u.2 / 64)
  ((4096 * v.2, u.1), v.1)

/-- The first transverse input stays in the open unit
strip throughout the full radius-32 real cylinder.
See M76 derivation 279. -/
theorem first_height_mem_unit {r : ℝ} (hr : |r| < 32) : r / 64 ∈ Ioo (-1) 1 := by
  have h := abs_lt.mp hr
  constructor <;> linarith [h.1, h.2]

/-- The same actual first annulus output gives a valid
second transverse input, uniformly for every circle point.
See Hamilton p. 66 and M76 derivation 279. -/
theorem second_height_mem_unit {r : ℝ} (hr : |r| < 32) (z : Circle) :
    (centeredAnnulusMap 16 (by norm_num) (z, r / 64)).2 / 64 ∈ Ioo (-1) 1 := by
  have hfirst := first_height_mem_unit hr
  have h := centeredAnnulusMap_snd_mem (L := (16 : ℝ)) (d := 1)
    (by norm_num) (by norm_num) (by norm_num) z ⟨hfirst.1.le, hfirst.2.le⟩
  constructor <;> linarith [h.1, h.2]

/-- The entire closed central cube has the exact original
real coordinates under the two-annulus map. See Hamilton
p. 66 and M76 derivation 279. -/
theorem map_core {r s t : ℝ} (hr : |r| ≤ 1 / 4) (hs : |s| ≤ 1 / 4)
    (ht : |t| ≤ 1 / 4) :
    map ((r, (s : Circle)), (t : Circle)) = ((r, s), t) := by
  have hr64 : |r / 64| ≤ 1 / 4 := by rw [abs_div]; norm_num; linarith
  have hfirst := centeredAnnulusMap_core (L := (16 : ℝ)) (d := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) hs hr64
  have hr4096 : |r / 64 / 64| ≤ 1 / 4 := by
    rw [abs_div, abs_div]
    norm_num
    linarith
  have hsecond := centeredAnnulusMap_core (L := (16 : ℝ)) (d := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) ht hr4096
  unfold map
  rw [hfirst]
  dsimp only
  rw [hsecond]
  apply Prod.ext
  · exact Prod.ext (by dsimp; ring) rfl
  · rfl

/-- The full literal real-coordinate lift of the thick-torus
map is locally PL throughout the bounded real cylinder,
including all circle quotient seams. See Hudson pp. 15--19
and M76 derivation 279. -/
theorem locallyPiecewiseAffineOn_map_lift :
    LocallyPiecewiseAffineOn
      (fun x : CubeShell.Ambient => map ((x.1.1, (x.1.2 : Circle)), (x.2 : Circle)))
      {x | |x.1.1| < 32} := by
  let U : Set CubeShell.Ambient := {x | |x.1.1| < 32}
  have hU : IsOpen U := by
    apply isOpen_lt <;> fun_prop
  have hcoord (i : Fin 3) : LocallyPiecewiseAffineOn (CubeShell.coordinate i) U :=
    locallyPiecewiseAffineOn_affine (CubeShell.coordinate i).toContinuousAffineMap hU
  have hr : LocallyPiecewiseAffineOn (fun x : CubeShell.Ambient => x.1.1 / 64) U := by
    apply (locallyPiecewiseAffineOn_affine
      ((1 / 64 : ℝ) • (CubeShell.coordinate 0).toContinuousAffineMap) hU).congr
    intro x _
    change 1 / 64 * x.1.1 = x.1.1 / 64
    ring
  have hpair : LocallyPiecewiseAffineOn (fun x : CubeShell.Ambient =>
      (x.1.2, x.1.1 / 64)) U := (hcoord 1).prod_mk hr
  have hAnn := locallyPiecewiseAffineOn_centeredAnnulusMap_lift
    (L := (16 : ℝ)) (d := 1) (by norm_num) (by norm_num) (by norm_num)
  let f : CubeShell.Ambient → ℝ × ℝ := fun x =>
    centeredAnnulusMap 16 (by norm_num) ((x.1.2 : Circle), x.1.1 / 64)
  have hf : LocallyPiecewiseAffineOn f U :=
    (hAnn.comp hpair).mono hU (fun x hx => ⟨hx, mem_univ _, first_height_mem_unit hx⟩)
  have hsecondHeight : LocallyPiecewiseAffineOn (fun x => (f x).2 / 64) U := by
    let a := (1 / 64 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
    apply (((locallyPiecewiseAffineOn_affine a isOpen_univ).comp hf).mono hU
      (fun _ hx => ⟨hx, mem_univ _⟩)).congr
    intro x _
    change 1 / 64 * (f x).2 = (f x).2 / 64
    ring
  let g : CubeShell.Ambient → ℝ × ℝ := fun x =>
    centeredAnnulusMap 16 (by norm_num) ((x.2 : Circle), (f x).2 / 64)
  have hg : LocallyPiecewiseAffineOn g U :=
    (hAnn.comp ((hcoord 2).prod_mk hsecondHeight)).mono hU
      (fun x hx => ⟨hx, mem_univ _, second_height_mem_unit hx (x.1.2 : Circle)⟩)
  have hfirstCoordinate : LocallyPiecewiseAffineOn (fun x => 4096 * (g x).2) U := by
    let a := (4096 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
    exact ((locallyPiecewiseAffineOn_affine a isOpen_univ).comp hg).mono hU
      (fun _ hx => ⟨hx, mem_univ _⟩)
  have hsecondCoordinate : LocallyPiecewiseAffineOn (fun x => (f x).1) U :=
    ((locallyPiecewiseAffineOn_affine
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap isOpen_univ).comp hf).mono hU
      (fun _ hx => ⟨hx, mem_univ _⟩)
  have hthirdCoordinate : LocallyPiecewiseAffineOn (fun x => (g x).1) U :=
    ((locallyPiecewiseAffineOn_affine
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap isOpen_univ).comp hg).mono hU
      (fun _ hx => ⟨hx, mem_univ _⟩)
  exact (hfirstCoordinate.prod_mk hsecondCoordinate).prod_mk hthirdCoordinate

end ThickTorus

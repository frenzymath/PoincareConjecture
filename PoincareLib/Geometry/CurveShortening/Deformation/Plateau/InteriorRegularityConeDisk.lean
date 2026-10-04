import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.InteriorRegularityPolarInverse
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.InteriorRegularityConeL2

/-!
# The actual target-valued cone disk and its L2 fields

The literal radius and argument are substituted into the constructed
cone. The true measure transport proves L2 membership of its values
and Cartesian fields, including the center. Morrey ICM 1950, printed
pp. 183-185, for Morgan--Tian Lemma 19.2, pp. 437-438;
M65 derivation 38, actual disk realization.
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareMT.M65Interior

/-- The literal cone disk, with values in the reconstruction's actual
target. Morrey ICM pp. 183-185; derivation 38. -/
def coneDiskMap {M : Type*} (P : EuclideanSpace ℝ (Fin 3) → M)
    (r : ℝ) (v0 : EuclideanSpace ℝ (Fin 3))
    (v : ℝ → EuclideanSpace ℝ (Fin 3)) (x z : LoopPlane) : M :=
  P (coneCoordinates r v0 v (polarCoordinates x z).1 (polarCoordinates x z).2)

/-- The actual Cartesian field transported from the polar rectangle.
Morrey ICM pp. 183-185; derivation 38. -/
def coneDiskField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : EuclideanSpace ℝ (Fin 3) → E) (r : ℝ)
    (v0 : EuclideanSpace ℝ (Fin 3)) (v d : ℝ → EuclideanSpace ℝ (Fin 3))
    (x : LoopPlane) (i : Fin 2) (z : LoopPlane) : E :=
  coneCartesianField g r v0 v d (polarCoordinates x z).1 (polarCoordinates x z).2 i

/-- On the genuine angular chart the disk is the original literal
polar cone. Morrey ICM pp. 183-185; derivation 38. -/
theorem coneDiskMap_polar {M : Type*} (P : EuclideanSpace ℝ (Fin 3) → M)
    (r : ℝ) (v0 : EuclideanSpace ℝ (Fin 3))
    (v : ℝ → EuclideanSpace ℝ (Fin 3)) (x : LoopPlane) {p : ℝ × ℝ}
    (hp : p ∈ polarCoord.target) :
    coneDiskMap P r v0 v x (polarPlane x p) = P (coneCoordinates r v0 v p.1 p.2) := by
  simp only [coneDiskMap, polarCoordinates_polarPlane x hp]

/-- The genuine disk fields recover the actual rectangle fields on
the angular chart. Morrey ICM pp. 183-185; derivation 38. -/
theorem coneDiskField_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : EuclideanSpace ℝ (Fin 3) → E) (r : ℝ)
    (v0 : EuclideanSpace ℝ (Fin 3)) (v d : ℝ → EuclideanSpace ℝ (Fin 3))
    (x : LoopPlane) (i : Fin 2) {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    coneDiskField g r v0 v d x i (polarPlane x p) =
      coneCartesianField g r v0 v d p.1 p.2 i := by
  simp only [coneDiskField, polarCoordinates_polarPlane x hp]

/-- Every point of the actual disk has cone coordinates in the genuine
closed reconstruction ball. Morrey ICM pp. 183-185; derivation 38. -/
theorem coneDisk_coordinates_mem {r ρ : ℝ} (hr : 0 < r)
    {v0 : EuclideanSpace ℝ (Fin 3)} {v : ℝ → EuclideanSpace ℝ (Fin 3)}
    (h0 : v0 ∈ closedBall 0 ρ)
    (hv : MapsTo v (Icc (-Real.pi) Real.pi) (closedBall 0 ρ))
    (x : LoopPlane) {z : LoopPlane} (hz : z ∈ closedBall x r) :
    coneCoordinates r v0 v (polarCoordinates x z).1 (polarCoordinates x z).2 ∈
      closedBall 0 ρ := by
  have hp : polarCoordinates x z ∈ Icc (0 : ℝ) r ×ˢ Icc (-Real.pi) Real.pi := by
    rwa [← polarCoordinates_preimage_rectangle x r] at hz
  exact coneCoordinates_mem_closedBall hr h0 (hv hp.2) hp.1

/-- The actual reconstructed values and explicit Cartesian fields
belong to L2 on the genuine disk. Morrey ICM pp. 183-185; derivation 38. -/
theorem coneDisk_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : EuclideanSpace ℝ (Fin 3) → E}
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    {r ρ K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : ContinuousOn v (Icc (-Real.pi) Real.pi))
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (-Real.pi) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hD : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, ‖fderiv ℝ g y‖ ≤ K)
    (x : LoopPlane) :
    MemLp (coneDiskMap g r v0 v x) 2 (volume.restrict (closedBall x r)) ∧
      ∀ i, MemLp (coneDiskField g r v0 v d x i) 2
        (volume.restrict (closedBall x r)) := by
  let S : Set (ℝ × ℝ) := Icc 0 r ×ˢ Icc (-Real.pi) Real.pi
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  have hc := (cone_reconstruction_continuous hr hρ hv hg h0 hvb).1
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc
  have hm : MemLp (fun p : ℝ × ℝ => g (coneCoordinates r v0 v p.1 p.2)) 2
      (volume.restrict S) := by
    apply MemLp.of_bound (hc.aestronglyMeasurable hS.measurableSet) B
    filter_upwards [ae_restrict_mem hS.measurableSet] with p hp
    exact hB p hp
  refine ⟨memLp_polarCoordinates hm x, fun i => ?_⟩
  exact memLp_polarCoordinates
    (coneCartesianField_memLp hr hρ hK hv hg h0 hvb hd hD i) x

end PoincareMT.M65Interior

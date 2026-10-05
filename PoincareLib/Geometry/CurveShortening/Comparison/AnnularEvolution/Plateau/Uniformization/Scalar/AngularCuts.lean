import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.IntegerCoverArea

/-!
# Null angular cuts and the actual integer deck relation

The countable union of integer angular cuts has zero source area. The
actual area inequality gives zero area for its differentiable image.
The unit deck identity extends to every integer by periodicity of the
actual affine defect.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

/-- The genuine integer angular cuts of the physical covering strip. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-global-injectivity.md`. -/
def scalarAngularCuts : Set Cover := ⋃ n : ℤ, Ioo (1 : ℝ) 2 ×ˢ {(n : ℝ)}

/-- The countable family of actual integer angular cuts is measurable. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-global-injectivity.md`. -/
theorem scalarAngularCuts_measurable : MeasurableSet scalarAngularCuts :=
  MeasurableSet.iUnion fun n => measurableSet_Ioo.prod (measurableSet_singleton (n : ℝ))

/-- Every actual integer angular cut lies in the open polar strip. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-global-injectivity.md`. -/
theorem scalarAngularCuts_subset : scalarAngularCuts ⊆ scalarCoverStrip := by
  rintro z ⟨_, ⟨n, rfl⟩, hz⟩
  exact hz.1

/-- The actual angular cuts have zero planar area. Source: Morgan--Tian (2007), Lemma 19.15,
pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-global-injectivity.md`. -/
theorem scalarAngularCuts_measure_zero : volume scalarAngularCuts = 0 := by
  apply measure_iUnion_null
  intro n
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- Differentiability on the actual strip suffices to make the image of its angular cuts
null, by the noninjective area inequality. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-global-injectivity.md`. -/
theorem scalarAngularCuts_image_measure_zero {f : Cover → Cover}
    (hd : ∀ z ∈ scalarCoverStrip, DifferentiableAt ℝ f z) :
    volume (f '' scalarAngularCuts) = 0 := by
  have h := addHaar_image_le_lintegral_abs_det_fderiv volume scalarAngularCuts_measurable
    (fun z hz => (hd z (scalarAngularCuts_subset hz)).hasFDerivAt.hasFDerivWithinAt)
  have hzero : volume.restrict scalarAngularCuts = 0 :=
    Measure.restrict_eq_zero.mpr scalarAngularCuts_measure_zero
  rw [hzero, lintegral_zero_measure] at h
  exact le_antisymm h zero_le

/-- The actual normalized map obeys the full integer deck identity, not only its defining
unit increment. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project
construction is recorded in `proof-work/tasks/M64/reports/annular-global-injectivity.md`. -/
theorem scalarNormalizedCoverMap_sub_int {H : Plane → ℝ} {V : Cover → ℝ}
    {P : ℝ} (hP : P ≠ 0)
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P)
    {z : Cover} (hz : z ∈ scalarCoverStrip) (n : ℤ) :
    scalarNormalizedCoverMap H V P (z - (0, (n : ℝ))) =
      scalarNormalizedCoverMap H V P z - (0, (n : ℝ)) := by
  let F := scalarNormalizedCoverMap H V P
  have hper : Function.Periodic (fun t : ℝ => F (z.1, t) - (0, t)) 1 := by
    intro t
    have h := scalarNormalizedCoverMap_deck (H := H) hP hdeck
      (show (z.1, t) ∈ scalarCoverStrip from hz)
    simp only [Prod.mk_add_mk, add_zero] at h
    change F (z.1, t + 1) = F (z.1, t) + (0, 1) at h
    dsimp only
    rw [h]
    ext <;> simp
  have h : F (z.1, z.2 - (n : ℝ) * 1) - (0, z.2 - (n : ℝ) * 1) =
      F (z.1, z.2) - (0, z.2) := hper.sub_int_mul_eq n
  simp only [mul_one] at h
  change F (z - (0, (n : ℝ))) = F z - (0, (n : ℝ))
  rw [show z - (0, (n : ℝ)) = (z.1, z.2 - (n : ℝ)) by ext <;> simp]
  apply Prod.ext
  · have h0 := congrArg Prod.fst h
    simpa only [Prod.fst_sub, sub_zero, Prod.mk.eta] using h0
  · have h1 := congrArg Prod.snd h
    simp only [Prod.snd_sub] at h1
    change (F (z.1, z.2 - (n : ℝ))).2 = (F z).2 - (n : ℝ)
    linarith

end PoincareMT.M64Uniformization

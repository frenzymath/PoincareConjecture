import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.PLInChartsProd
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.TorusPLCharts

/-!
# The actual real, circle and product coordinate families

These families consist only of identity charts, additive
circle quotient charts, and their literal products. The
cover and PL identity statements use those actual maps.
See Hamilton 1976, p. 66 and M76 derivation270.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F X Y ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [TopologicalSpace Y]

/-- The one actual identity chart of a real model.
See M76 derivation270. -/
def realCharts (E : Type*) [TopologicalSpace E] : Unit → OpenPartialHomeomorph E E :=
  fun _ => OpenPartialHomeomorph.refl E

/-- The actual product coordinate family, without changing
the association of its spatial factors. See derivation270. -/
def prodCharts (Q : ι → OpenPartialHomeomorph E X) (R : κ → OpenPartialHomeomorph F Y) :
    ι × κ → OpenPartialHomeomorph (E × F) (X × Y) :=
  fun i => (Q i.1).prod (R i.2)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Full products of covering actual chart families cover
their entire product space. See M76 derivation270. -/
theorem prodCharts_cover (Q : ι → OpenPartialHomeomorph E X)
    (R : κ → OpenPartialHomeomorph F Y)
    (hQ : ∀ x, ∃ i, x ∈ (Q i).target) (hR : ∀ y, ∃ j, y ∈ (R j).target)
    (z : X × Y) : ∃ i, z ∈ (prodCharts Q R i).target := by
  obtain ⟨i, hi⟩ := hQ z.1
  obtain ⟨j, hj⟩ := hR z.2
  exact ⟨(i, j), hi, hj⟩

/-- The one identity chart covers the entire real model.
See M76 derivation270. -/
theorem realCharts_cover (E : Type*) [TopologicalSpace E] (x : E) :
    ∃ i, x ∈ (realCharts E i).target := ⟨(), mem_univ _⟩

omit [FiniteDimensional ℝ E] in
/-- Transition PL certificates give the identity map's
actual chartwise PL certificate on the whole space.
See Hudson pp. 15--19 and M76 derivation270. -/
theorem plInCharts_id (Q : ι → OpenPartialHomeomorph E X)
    (hQ : ∀ i j, LocallyPiecewiseAffineOn ((Q i).trans (Q j).symm)
      ((Q i).trans (Q j).symm).source) :
    PLInCharts Q Q id univ := by
  refine ⟨isOpen_univ, continuous_id.continuousOn, ?_⟩
  intro i j
  have hdom : chartMapDomain (Q i) (Q j) id univ = ((Q i).trans (Q j).symm).source := by
    ext x
    simp only [chartMapDomain, mem_inter_iff, mem_preimage, mem_univ, and_true,
      Function.comp_apply, id_eq, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source]
  rw [hdom]
  exact hQ i j

omit [FiniteDimensional ℝ F] in
/-- An affine real map has actual PL coordinates in the
single identity charts on every open source. See derivation270. -/
theorem plInCharts_affine (a : E →ᴬ[ℝ] F) {U : Set E} (hU : IsOpen U) :
    PLInCharts (realCharts E) (realCharts F) a U := by
  refine ⟨hU, a.continuous.continuousOn, ?_⟩
  intro i j
  have hdom : chartMapDomain (realCharts E i) (realCharts F j) a U = U := by
    ext x
    change ((x ∈ univ ∧ x ∈ U) ∧ a x ∈ univ) ↔ x ∈ U
    simp
  rw [hdom]
  exact locallyPiecewiseAffineOn_affine a hU

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- When the target is a real model in its one identity
chart, its coordinate condition has no target restriction.
See Hudson pp. 15--19 and M76 derivation270. -/
theorem plInCharts_real_target (Q : ι → OpenPartialHomeomorph E X)
    (f : X → F) (U : Set X) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hPL : ∀ i, LocallyPiecewiseAffineOn (f ∘ Q i) ((Q i).source ∩ Q i ⁻¹' U)) :
    PLInCharts Q (realCharts F) f U := by
  refine ⟨hU, hf, ?_⟩
  intro i j
  have hdom : chartMapDomain (Q i) (realCharts F j) f U = (Q i).source ∩ Q i ⁻¹' U := by
    ext x
    change ((x ∈ (Q i).source ∧ Q i x ∈ U) ∧ f (Q i x) ∈ univ) ↔ _
    simp
  rw [hdom]
  exact hPL i

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A map with a real identity-chart target exposes its
full literal input-chart PL expression. See derivation270. -/
theorem PLInCharts.real_target_coordinates
    {Q : ι → OpenPartialHomeomorph E X} {f : X → F} {U : Set X}
    (hf : PLInCharts Q (realCharts F) f U) (i : ι) :
    LocallyPiecewiseAffineOn (f ∘ Q i) ((Q i).source ∩ Q i ⁻¹' U) := by
  have h := hf.coordinates i ()
  have hdom : chartMapDomain (Q i) (realCharts F ()) f U = (Q i).source ∩ Q i ⁻¹' U := by
    ext x
    change ((x ∈ (Q i).source ∧ Q i x ∈ U) ∧ f (Q i x) ∈ univ) ↔ _
    simp
  rw [hdom] at h
  exact h

end Geometry

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

/-- The entire actual family of standard circle quotient
charts. See Hamilton p. 66 and M76 derivation270. -/
noncomputable def quotientCharts : ℝ → OpenPartialHomeomorph ℝ (AddCircle p) :=
  fun a => openPartialHomeomorphCoe p a

/-- The actual standard circle charts cover, by the two
distinct puncture charts. See M76 derivation270. -/
theorem quotientCharts_cover (z : AddCircle p) :
    ∃ a, z ∈ (quotientCharts p a).target := by
  obtain ⟨b, hb⟩ := two_puncture_charts_cover p z
  exact ⟨if b then 0 else p / 2, hb⟩

/-- The actual circle identity has PL coordinates at every
quotient seam in every chosen source and target chart.
See Hamilton p. 66 and M76 derivation270. -/
theorem plInCharts_id :
    PLInCharts (quotientCharts p) (quotientCharts p) id univ :=
  Geometry.plInCharts_id (quotientCharts p) (quotient_chart_transition_locallyPiecewiseAffine p)

end AddCircle

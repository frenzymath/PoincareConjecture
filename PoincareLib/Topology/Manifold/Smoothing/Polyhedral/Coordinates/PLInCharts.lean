import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PiecewiseAffineProd

/-!
# PL maps in explicit actual coordinate families

The real coordinate source retains both chart domains and
the given open map domain. Composition chooses an actual
covering intermediate chart, cancels its inverse only on
its target, and applies local PL locality. See Hudson
pp. 15--19 and M76 derivation270, stable torus induction.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F G X Y Z ι κ nu : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The exact real source of one map expression in two
actual direct charts. See M76 derivation270. -/
def chartMapDomain (Q : OpenPartialHomeomorph E X) (R : OpenPartialHomeomorph F Y)
    (f : X → Y) (U : Set X) : Set E :=
  (Q.source ∩ Q ⁻¹' U) ∩ (f ∘ Q) ⁻¹' R.target

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Every literal coordinate source is open when the map
is continuous on its given open domain. See derivation270. -/
theorem isOpen_chartMapDomain
    (Q : OpenPartialHomeomorph E X) (R : OpenPartialHomeomorph F Y)
    (f : X → Y) (U : Set X) (hU : IsOpen U) (hf : ContinuousOn f U) :
    IsOpen (chartMapDomain Q R f U) := by
  have hbase : IsOpen (Q.source ∩ Q ⁻¹' U) :=
    Q.continuousOn_toFun.isOpen_inter_preimage Q.open_source hU
  have hcomp : ContinuousOn (f ∘ Q) (Q.source ∩ Q ⁻¹' U) :=
    hf.comp (Q.continuousOn_toFun.mono inter_subset_left) (fun _ hx => hx.2)
  exact hcomp.isOpen_inter_preimage hbase R.open_target

/-- Continuity and actual local finite PL formulas in a
specified family of direct real coordinate charts. The
families need not cover until a theorem explicitly asks
for that property. See Hudson pp. 15--19 and derivation270. -/
structure PLInCharts (Q : ι → OpenPartialHomeomorph E X)
    (R : κ → OpenPartialHomeomorph F Y) (f : X → Y) (U : Set X) : Prop where
  isOpen : IsOpen U
  continuousOn : ContinuousOn f U
  coordinates : ∀ i j, LocallyPiecewiseAffineOn ((R j).symm ∘ f ∘ Q i)
    (chartMapDomain (Q i) (R j) f U)

namespace PLInCharts

variable {Q : ι → OpenPartialHomeomorph E X}
  {R : κ → OpenPartialHomeomorph F Y} {S : nu → OpenPartialHomeomorph G Z}
  {f f' : X → Y} {g : Y → Z} {U U' : Set X} {V : Set Y}

omit [FiniteDimensional ℝ F] in
/-- Actual chartwise PL formulas restrict to any open
subset of their original map domain. See derivation270. -/
theorem mono (hf : PLInCharts Q R f U) (hU' : IsOpen U') (hsub : U' ⊆ U) :
    PLInCharts Q R f U' where
  isOpen := hU'
  continuousOn := hf.continuousOn.mono hsub
  coordinates i j := (hf.coordinates i j).mono
    (isOpen_chartMapDomain (Q i) (R j) f U' hU' (hf.continuousOn.mono hsub))
      (fun _ hx => ⟨⟨hx.1.1, hsub hx.1.2⟩, hx.2⟩)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Equality on the whole actual map domain retains every
coordinate certificate on its exact source. See derivation270. -/
theorem congr (hf : PLInCharts Q R f U) (heq : EqOn f f' U) :
    PLInCharts Q R f' U := by
  refine ⟨hf.isOpen, hf.continuousOn.congr heq.symm, ?_⟩
  intro i j
  have hdom : chartMapDomain (Q i) (R j) f' U = chartMapDomain (Q i) (R j) f U := by
    ext x
    constructor <;> intro hx
    · refine ⟨hx.1, ?_⟩
      change f (Q i x) ∈ (R j).target
      rw [heq hx.1.2]
      exact hx.2
    · refine ⟨hx.1, ?_⟩
      change f' (Q i x) ∈ (R j).target
      rw [← heq hx.1.2]
      exact hx.2
  rw [hdom]
  apply (hf.coordinates i j).congr
  intro x hx
  exact congrArg (R j).symm (heq hx.1.2)

omit [FiniteDimensional ℝ G] in
/-- Chartwise PL maps compose when the intermediate actual
chart targets cover. Continuity gives the needed open patches
and chart inverse laws are used only there. The source is the
literal domain intersection. See Hudson and derivation270. -/
theorem comp (hg : PLInCharts R S g V) (hf : PLInCharts Q R f U)
    (hcover : ∀ y : Y, ∃ j, y ∈ (R j).target) :
    PLInCharts Q S (g ∘ f) (U ∩ f ⁻¹' V) := by
  have hUV : IsOpen (U ∩ f ⁻¹' V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen hg.isOpen
  have hcont : ContinuousOn (g ∘ f) (U ∩ f ⁻¹' V) :=
    hg.continuousOn.comp (hf.continuousOn.mono inter_subset_left) (fun _ hx => hx.2)
  refine ⟨hUV, hcont, ?_⟩
  intro i k
  let D := chartMapDomain (Q i) (S k) (g ∘ f) (U ∩ f ⁻¹' V)
  have hD : IsOpen D := isOpen_chartMapDomain (Q i) (S k) (g ∘ f) _ hUV hcont
  apply LocallyPiecewiseAffineOn.locality
  intro x hx
  obtain ⟨j, hxj⟩ := hcover (f (Q i x))
  let W := chartMapDomain (Q i) (R j) f U
  have hW : IsOpen W := isOpen_chartMapDomain (Q i) (R j) f U hf.isOpen hf.continuousOn
  refine ⟨W, ⟨⟨hx.1.1, hx.1.2.1⟩, hxj⟩, ?_⟩
  have hsub : D ∩ W ⊆ chartMapDomain (Q i) (R j) f U ∩
      ((R j).symm ∘ f ∘ Q i) ⁻¹' chartMapDomain (R j) (S k) g V := by
    intro y hy
    have hcancel : R j ((R j).symm (f (Q i y))) = f (Q i y) :=
      (R j).right_inv hy.2.2
    refine ⟨hy.2, ⟨⟨(R j).map_target hy.2.2, ?_⟩, ?_⟩⟩
    · change R j ((R j).symm (f (Q i y))) ∈ V
      rw [hcancel]
      exact hy.1.1.2.2
    · change g (R j ((R j).symm (f (Q i y)))) ∈ (S k).target
      rw [hcancel]
      exact hy.1.2
  apply (((hg.coordinates j k).comp (hf.coordinates i j)).mono (hD.inter hW) hsub).congr
  intro y hy
  change (S k).symm (g (R j ((R j).symm (f (Q i y))))) =
    (S k).symm (g (f (Q i y)))
  exact congrArg (fun z => (S k).symm (g z)) ((R j).right_inv hy.2.2)

omit [FiniteDimensional ℝ G] in
/-- An exact image bound restricts the chartwise composition
back to its entire prescribed open source. See derivation270. -/
theorem comp_mapsTo (hg : PLInCharts R S g V) (hf : PLInCharts Q R f U)
    (hcover : ∀ y : Y, ∃ j, y ∈ (R j).target) (hmap : MapsTo f U V) :
    PLInCharts Q S (g ∘ f) U :=
  (hg.comp hf hcover).mono hf.isOpen (fun _ hx => ⟨hx, hmap hx⟩)

end PLInCharts

end Geometry

import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Polar.Dilation
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter TopologicalSpace PoincareConjecture Manifold IsManifold
open scoped Manifold ContDiff Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} (hc : RayComparison p)

def positiveConeOpens : Opens (AsymptoticCone p hc) :=
  ⟨{a | 0 < asymptoticConeRadius hc a},
    isOpen_lt continuous_const (lipschitzWith_asymptoticConeRadius hc).continuous⟩

theorem nonempty_asymptoticConePositive_of_unitSlice
    (hu : Nonempty (AsymptoticConeUnitSlice p hc)) : Nonempty (AsymptoticConePositive p hc) := by
  obtain ⟨a⟩ := hu
  exact ⟨⟨a.1, by rw [a.property]; exact zero_lt_one⟩⟩

variable {hc} {n : ℕ}

namespace UnitSliceRadialChartData

theorem ambientChart_target_positive (d : UnitSliceRadialChartData hc n)
    {a : AsymptoticCone p hc} (ha : a ∈ d.ambientChart.target) :
    0 < asymptoticConeRadius hc a := by
  have hr := d.radial _ (d.ambientChart.map_target ha)
  rw [d.ambientChart.right_inv ha] at hr
  have hf := d.positive _ (d.ambientChart.map_target ha)
  have hnonneg := (asymptoticConeRadius hc a).coe_nonneg
  exact_mod_cast (show 0 < (asymptoticConeRadius hc a : ℝ) by nlinarith)

def positiveChart (d : UnitSliceRadialChartData hc n)
    (hne : Nonempty (AsymptoticConePositive p hc)) :
    OpenPartialHomeomorph (AsymptoticConePositive p hc) (UnitSliceAmbient n) :=
  d.ambientChart.symm.subtypeRestr (s := positiveConeOpens hc) hne

@[simp] theorem positiveChart_source (d : UnitSliceRadialChartData hc n)
    (hne : Nonempty (AsymptoticConePositive p hc)) :
    (d.positiveChart hne).source = {a | a.1 ∈ d.ambientChart.target} := by
  simp only [positiveChart, OpenPartialHomeomorph.subtypeRestr_source,
    OpenPartialHomeomorph.symm_source]
  rfl

@[simp] theorem positiveChart_target (d : UnitSliceRadialChartData hc n)
    (hne : Nonempty (AsymptoticConePositive p hc)) :
    (d.positiveChart hne).target = d.ambientChart.source := by
  apply subset_antisymm
  · exact d.ambientChart.symm.subtypeRestr_target_subset hne
  · intro x hx
    let a : AsymptoticConePositive p hc :=
      ⟨d.ambientChart x, d.ambientChart_target_positive (d.ambientChart.map_source hx)⟩
    have h := d.ambientChart.symm.map_subtype_source (s := positiveConeOpens hc) hne
      (x := a) (d.ambientChart.map_source hx)
    simpa only [a, d.ambientChart.left_inv hx, positiveChart] using h

theorem positiveChart_apply (d : UnitSliceRadialChartData hc n)
    (hne : Nonempty (AsymptoticConePositive p hc)) (a : AsymptoticConePositive p hc) :
    d.positiveChart hne a = d.ambientChart.symm a.1 := rfl

theorem positiveChart_symm_val (d : UnitSliceRadialChartData hc n)
    (hne : Nonempty (AsymptoticConePositive p hc)) {x : UnitSliceAmbient n}
    (hx : x ∈ (d.positiveChart hne).target) :
    ((d.positiveChart hne).symm x).1 = d.ambientChart x :=
  d.ambientChart.symm.subtypeRestr_symm_apply hne hx

theorem positiveChart_symm_distance (d : UnitSliceRadialChartData hc n)
    (hne : Nonempty (AsymptoticConePositive p hc))
    {x y : UnitSliceAmbient n} (hx : x ∈ (d.positiveChart hne).target)
    (hy : y ∈ (d.positiveChart hne).target) :
    dist ((d.positiveChart hne).symm x) ((d.positiveChart hne).symm y) =
      (d.metric.edist x y).toReal := by
  change dist (((d.positiveChart hne).symm x).1) (((d.positiveChart hne).symm y).1) = _
  rw [d.positiveChart_symm_val hne hx, d.positiveChart_symm_val hne hy]
  exact d.distance x (d.positiveChart_target hne ▸ hx) y (d.positiveChart_target hne ▸ hy)

theorem contDiffOn_positiveChart_transition (d e : UnitSliceRadialChartData hc n)
    (hne : Nonempty (AsymptoticConePositive p hc)) :
    ContDiffOn ℝ ∞ ((d.positiveChart hne).symm.trans (e.positiveChart hne))
      ((d.positiveChart hne).symm.trans (e.positiveChart hne)).source :=
  d.metric.contDiffOn_isometric_chart_transition e.metric
    (d.positiveChart hne).symm (e.positiveChart hne).symm
    (fun _ hx _ hy => d.positiveChart_symm_distance hne hx hy)
    (fun _ hx _ hy => e.positiveChart_symm_distance hne hx hy)

end UnitSliceRadialChartData

variable (hc) (n : ℕ) (hne : Nonempty (AsymptoticConePositive p hc))
  (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
    ∃ (d : UnitSliceRadialChartData hc n) (x : d.Level), (d.levelHomeomorph x).1 = z)

include hcover in
theorem positiveCone_radialAtlas_covers (a : AsymptoticConePositive p hc) :
    ∃ d : UnitSliceRadialChartData hc n, a ∈ (d.positiveChart hne).source := by
  obtain ⟨d, x, _, _, ha⟩ := exists_dilated_radial_model_at_positive_point hc hcover a
  exact ⟨d.dilate (asymptoticConeRadius hc a.1) a.property, by simpa using ha⟩

@[instance_reducible] def positiveConeChartedSpace :
    ChartedSpace (UnitSliceAmbient n) (AsymptoticConePositive p hc) where
  atlas := {C | ∃ d : UnitSliceRadialChartData hc n, C = d.positiveChart hne}
  chartAt a := (positiveCone_radialAtlas_covers hc n hne hcover a).choose.positiveChart hne
  mem_chart_source a := (positiveCone_radialAtlas_covers hc n hne hcover a).choose_spec
  chart_mem_atlas _ := ⟨_, rfl⟩

theorem positiveCone_isManifold :
    letI := positiveConeChartedSpace hc n hne hcover
    IsManifold (𝓡 (n + 1)) ∞ (AsymptoticConePositive p hc) := by
  let := positiveConeChartedSpace hc n hne hcover
  apply isManifold_of_contDiffOn (𝓡 (n + 1)) ∞ (AsymptoticConePositive p hc)
  intro C C' hC hC'
  obtain ⟨d, rfl⟩ := hC
  obtain ⟨e, rfl⟩ := hC'
  simpa using d.contDiffOn_positiveChart_transition e hne

namespace UnitSliceRadialChartData

variable {hc n}


def positiveMap (d : UnitSliceRadialChartData hc n) : d.source → AsymptoticConePositive p hc :=
  fun x => ⟨d.ambientChart x, d.ambientChart_target_positive (d.ambientChart.map_source x.property)⟩

theorem positiveMap_distance (d : UnitSliceRadialChartData hc n) (x y : d.source) :
    dist (d.positiveMap x) (d.positiveMap y) = (d.metric.edist x y).toReal :=
  d.distance x x.property y y.property

theorem positiveMap_eq_chart_symm (d : UnitSliceRadialChartData hc n) (x : d.source) :
    d.positiveMap x = (d.positiveChart hne).symm x := by
  apply Subtype.ext
  exact (d.positiveChart_symm_val hne (by rw [d.positiveChart_target]; exact x.property)).symm

theorem isLocalDiffeomorph_positiveMap (d : UnitSliceRadialChartData hc n) :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ d.positiveMap := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  have hmax : d.positiveChart hne ∈ maximalAtlas (𝓡 (n + 1)) ∞ (AsymptoticConePositive p hc) :=
    subset_maximalAtlas ⟨d, rfl⟩
  let C : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
      (AsymptoticConePositive p hc) (UnitSliceAmbient n) ∞ := {
    toPartialEquiv := (d.positiveChart hne).toPartialEquiv
    open_source := (d.positiveChart hne).open_source
    open_target := (d.positiveChart hne).open_target
    contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hmax
    contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hmax }
  intro x
  have hx : (x : UnitSliceAmbient n) ∈ C.target := by
    change (x : UnitSliceAmbient n) ∈ (d.positiveChart hne).target
    rw [d.positiveChart_target]
    exact x.property
  have hcomp := (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 (n + 1)) d.source x).comp
    (𝓡 (n + 1)) (AsymptoticConePositive p hc)
    (C.symm.isLocalDiffeomorphAt (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ hx)
  convert! hcomp using 1
  funext y
  exact d.positiveMap_eq_chart_symm hne y

end UnitSliceRadialChartData

end Poincare.AncientVolume.ScalarRatio

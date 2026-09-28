import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto














set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a : ℕ → ℝ} {T : ℝ}

namespace TimeGluing

variable (F : ∀ j, RicciFlow n M (Ioo (a j) T))
  (hcover : ∀ t < T, ∃ j, a j < t)
  (hcompat : ∀ i j t, t ∈ Ioo (a i) T → t ∈ Ioo (a j) T →
    (F i).metric t = (F j).metric t)

private noncomputable def index (t : ℝ) : ℕ :=
  if ht : t < T then Classical.choose (hcover t ht) else 0

private theorem index_mem {t : ℝ} (ht : t < T) :
    t ∈ Ioo (a (index hcover t)) T := by
  simpa only [index, dif_pos ht, mem_Ioo] using
    And.intro (Classical.choose_spec (hcover t ht)) ht



noncomputable def metric (t : ℝ) : RiemannianMetric n M :=
  (F (index hcover t)).metric t

include hcompat in

theorem metric_eq (j : ℕ) {t : ℝ} (ht : t ∈ Ioo (a j) T) :
    metric F hcover t = (F j).metric t :=
  hcompat _ j t (index_mem hcover ht.2) ht

include hcompat in
private theorem metric_eventuallyEq (j : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (a j) T) :
    metric F hcover =ᶠ[𝓝 t] (F j).metric := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact metric_eq F hcover hcompat j hs


noncomputable def connection (t : ℝ) : LeviCivitaData (metric F hcover t) :=
  (F (index hcover t)).connection t

include hcompat in
theorem smooth : RiemannianMetric.IsSmoothFamilyOn (metric F hcover) (Iio T) := by
  intro p hp
  obtain ⟨j, hj⟩ := hcover p.1 hp.1
  have hmem : p ∈ Ioo (a j) T ×ˢ (univ : Set M) := ⟨⟨hj, hp.1⟩, mem_univ _⟩
  have hnhds : Ioo (a j) T ×ˢ (univ : Set M) ∈ 𝓝 p :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds hmem
  apply ContMDiffAt.contMDiffWithinAt
  apply ((F j).smooth.contMDiffAt hnhds).congr_of_eventuallyEq
  filter_upwards [hnhds] with q hq
  simp only [metric_eq F hcover hcompat j hq.1]

include hcompat in
theorem equation (t : ℝ) (ht : t ∈ Iio T) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (metric F hcover s).inner x v w)
      (-2 * (connection F hcover t).ricci x v w) (Iio T) t := by
  let j := index hcover t
  have hj : t ∈ Ioo (a j) T := index_mem hcover ht
  have hderiv := ((F j).equation t hj x v w).hasDerivAt
    (Ioo_mem_nhds hj.1 hj.2)
  apply HasDerivAt.hasDerivWithinAt
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [metric_eventuallyEq F hcover hcompat j hj] with s hs
  rw [hs]

end TimeGluing




noncomputable def glueAncient
    (F : ∀ j, RicciFlow n M (Ioo (a j) T))
    (hcover : ∀ t < T, ∃ j, a j < t)
    (hcompat : ∀ i j t, t ∈ Ioo (a i) T → t ∈ Ioo (a j) T →
      (F i).metric t = (F j).metric t) : RicciFlow n M (Iio T) where
  metric := TimeGluing.metric F hcover
  connection := TimeGluing.connection F hcover
  interval := ordConnected_Iio
  nontrivial := ⟨T - 2, by simp, T - 1, by simp, by linarith⟩
  smooth := TimeGluing.smooth F hcover hcompat
  equation := TimeGluing.equation F hcover hcompat

theorem glueAncient_metric_eq
    (F : ∀ j, RicciFlow n M (Ioo (a j) T))
    (hcover : ∀ t < T, ∃ j, a j < t)
    (hcompat : ∀ i j t, t ∈ Ioo (a i) T → t ∈ Ioo (a j) T →
      (F i).metric t = (F j).metric t)
    (j : ℕ) {t : ℝ} (ht : t ∈ Ioo (a j) T) :
    (glueAncient F hcover hcompat).metric t = (F j).metric t :=
  TimeGluing.metric_eq F hcover hcompat j ht




theorem glueAncient_slice_property_at
    (F : ∀ j, RicciFlow n M (Ioo (a j) T))
    (hcover : ∀ t < T, ∃ j, a j < t)
    (hcompat : ∀ i j t, t ∈ Ioo (a i) T → t ∈ Ioo (a j) T →
      (F i).metric t = (F j).metric t)
    (t : ℝ) (ht : t < T)
    (P : (g : RiemannianMetric n M) → LeviCivitaData g → Prop)
    (hP : ∀ j, t ∈ Ioo (a j) T → P ((F j).metric t) ((F j).connection t)) :
    P ((glueAncient F hcover hcompat).metric t)
      ((glueAncient F hcover hcompat).connection t) :=
  hP (TimeGluing.index hcover t) (TimeGluing.index_mem hcover ht)




theorem glueAncient_slice_property
    (F : ∀ j, RicciFlow n M (Ioo (a j) T))
    (hcover : ∀ t < T, ∃ j, a j < t)
    (hcompat : ∀ i j t, t ∈ Ioo (a i) T → t ∈ Ioo (a j) T →
      (F i).metric t = (F j).metric t)
    (P : (g : RiemannianMetric n M) → LeviCivitaData g → Prop)
    (hP : ∀ j t, t ∈ Ioo (a j) T → P ((F j).metric t) ((F j).connection t))
    (t : ℝ) (ht : t < T) :
    P ((glueAncient F hcover hcompat).metric t)
      ((glueAncient F hcover hcompat).connection t) :=
  glueAncient_slice_property_at F hcover hcompat t ht P (fun j ↦ hP j t)



theorem ancientTimeCover_of_tendsto (ha : Tendsto a atTop atBot) :
    ∀ t < T, ∃ j, a j < t := by
  intro t _
  exact (ha.eventually (eventually_lt_atBot t)).exists




theorem exists_ancient_of_local_metric_realizations
    (g : ℝ → RiemannianMetric n M)
    (hg : RiemannianMetric.IsSmoothFamilyOn g (Iio T))
    (hlocal : ∀ t < T, ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∃ F : RicciFlow n M V, F.metric = g) :
    ∃ F : RicciFlow n M (Iio T), F.metric = g := by
  classical
  let time : ℝ → ℝ := fun t ↦ if t < T then t else T - 1
  have htime (t : ℝ) : time t < T := by
    dsimp [time]
    split_ifs with ht
    · exact ht
    · linarith
  choose V hV htV G hG using fun t ↦ hlocal (time t) (htime t)
  let g' : ℝ → RiemannianMetric n M := fun t ↦ (G t).metric t
  have hgg : g' = g := by
    funext t
    exact congrFun (hG t) t
  refine ⟨{
    metric := g'
    connection := fun t ↦ (G t).connection t
    interval := ordConnected_Iio
    nontrivial := ⟨T - 2, by simp, T - 1, by simp, by linarith⟩
    smooth := by simpa only [hgg] using hg
    equation := ?_ }, hgg⟩
  intro t ht x v w
  change t < T at ht
  have hmem : t ∈ V t := by
    simpa only [time, if_pos ht] using htV t
  have hd := ((G t).equation t hmem x v w).hasDerivAt ((hV t).mem_nhds hmem)
  apply HasDerivAt.hasDerivWithinAt
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall fun s ↦ by
    change ((G s).metric s).inner x v w = ((G t).metric s).inner x v w
    rw [hG s, hG t]

end PoincareConjecture.RicciFlow

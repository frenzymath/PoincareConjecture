import PoincareConjecture.Definitions.Ch18.Deformation
import PoincareConjecture.Definitions.Ch11.BlowupLimits
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Geometry.Manifold.Diffeomorph










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u v

namespace PoincareConjecture


def mappedGenLoop {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {x : X} {y : Y} {n : ℕ}
    (f : ContinuousMap X Y) (h : f x = y) (gamma : GenLoop (Fin n) X x) :
    GenLoop (Fin n) Y y :=
  ⟨f.comp gamma.1, fun z hz => by
    change f (gamma z) = y
    have hg : gamma z = x := gamma.2 z hz
    simpa [hg] using h⟩


def mappedHomotopyClass {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] {x : X} {y : Y} {n : ℕ}
    (f : ContinuousMap X Y) (h : f x = y) :
    HomotopyGroup.Pi n X x → HomotopyGroup.Pi n Y y :=
  Quotient.map (mappedGenLoop f h) (fun _ _ hab =>
    ContinuousMap.HomotopicRel.comp_continuousMap hab f)


noncomputable def componentThirdHomology (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} ℤ :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) 3).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X))

noncomputable def componentThirdHomologyMap {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : ContinuousMap X Y) :
    componentThirdHomology X →ₗ[ℤ] componentThirdHomology Y :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) 3).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))).map (TopCat.ofHom f)).hom


structure WidthComponentSlice where
  ambient : GeneralizedSliceCarrier.{u}
  carrier : GeneralizedSliceCarrier.{u}
  inclusion : carrier.carrier → ambient.carrier
  inclusion_openEmbedding : Topology.IsOpenEmbedding inclusion
  inclusion_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ inclusion
  ambient_metric : RiemannianMetric 3 ambient.carrier
  metric : RiemannianMetric 3 carrier.carrier
  connection : LeviCivitaData metric
  metric_pullback : ∀ x v w,
    ambient_metric.inner (inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) inclusion x v)
      (mfderiv (𝓡 3) (𝓡 3) inclusion x w) = metric.inner x v w
  compact : IsCompact (Set.univ : Set carrier.carrier)
  connected : IsConnected (Set.univ : Set carrier.carrier)
  family : FreeTwoSphereFamily (M := carrier.carrier)
  component_range : Set.range inclusion = connectedComponent (inclusion family.basepoint)
  pi_two : Subsingleton (HomotopyGroup.Pi 2 carrier.carrier family.basepoint)
  loop_pi_three : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := carrier.carrier))
    (constantC1Loop family.basepoint) ≃*
      HomotopyGroup.Pi 3 carrier.carrier family.basepoint
  pi_three_integer : HomotopyGroup.Pi 3 carrier.carrier family.basepoint ≃*
    Multiplicative ℤ
  orientation : componentThirdHomology carrier.carrier ≃ₗ[ℤ] ULift.{u} ℤ

noncomputable def componentPiThreeClass (C : WidthComponentSlice.{u}) :
    HomotopyGroup.Pi 3 C.carrier.carrier C.family.basepoint :=
  C.loop_pi_three C.family.homotopy_class




structure SmoothComponentClassMap (C D : WidthComponentSlice.{u}) where
  map : ContinuousMap C.carrier.carrier D.carrier.carrier
  smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ map
  based : map C.family.basepoint = D.family.basepoint
  loop_map : ContinuousMap (C1FreeLoopSpace (M := C.carrier.carrier))
    (C1FreeLoopSpace (M := D.carrier.carrier))
  loop_extension : ∀ gamma x, (loop_map gamma).extension x = map (gamma.extension x)
  loop_based : loop_map (constantC1Loop C.family.basepoint) =
    constantC1Loop D.family.basepoint
  loop_class : mappedHomotopyClass loop_map loop_based C.family.homotopy_class =
    D.family.homotopy_class
  pi_three_naturality : ∀ alpha,
    D.loop_pi_three (mappedHomotopyClass loop_map loop_based alpha) =
      mappedHomotopyClass map based (C.loop_pi_three alpha)
  pi_three_injective : Function.Injective (mappedHomotopyClass (n := 3) map based)
  family_homotopic : ∃ Gamma : FreeTwoSphereFamily (M := D.carrier.carrier),
    (∀ c, Gamma.family c = loop_map (C.family.family c)) ∧
      FreeTwoSphereHomotopic Gamma D.family



def ComponentMapDegreeOne {C D : WidthComponentSlice.{u}}
    (f : SmoothComponentClassMap C D) : Prop :=
  ∀ z : componentThirdHomology C.carrier.carrier,
    D.orientation (componentThirdHomologyMap f.map z) = C.orientation z

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



structure WidthRegularSlab {t₀ t₁ : ℝ}
    (slice : Set.Icc t₀ t₁ → WidthComponentSlice.{u})
    (a b : Set.Icc t₀ t₁) where
  ordered : a.1 < b.1
  flow : RicciFlow 3 (slice a).carrier.carrier (Set.Icc a.1 b.1)
  identify : ∀ s : Set.Icc a.1 b.1,
    Diffeomorph (𝓡 3) (𝓡 3) (slice a).carrier.carrier
      (slice ⟨s.1, ⟨a.2.1.trans s.2.1, s.2.2.trans b.2.2⟩⟩).carrier.carrier ∞
  initial_identify : ∀ x,
    identify ⟨a.1, ⟨le_rfl, ordered.le⟩⟩ x = x
  class_map : ∀ s : Set.Icc a.1 b.1,
    SmoothComponentClassMap (slice a)
      (slice ⟨s.1, ⟨a.2.1.trans s.2.1, s.2.2.trans b.2.2⟩⟩)
  class_map_identify : ∀ s x, (class_map s).map x = identify s x
  metric_pullback : ∀ (s : Set.Icc a.1 b.1) x v w,
    (slice ⟨s.1, ⟨a.2.1.trans s.2.1, s.2.2.trans b.2.2⟩⟩).metric.inner
      (identify s x) (mfderiv (𝓡 3) (𝓡 3) (identify s) x v)
      (mfderiv (𝓡 3) (𝓡 3) (identify s) x w) =
        (flow.metric s.1).inner x v w
  scalar_pullback : ∀ (s : Set.Icc a.1 b.1) x,
    (slice ⟨s.1, ⟨a.2.1.trans s.2.1, s.2.2.trans b.2.2⟩⟩).connection.scalarCurvature
      (identify s x) = (flow.connection s.1).scalarCurvature x




structure SurgeryComponentPath (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (t₀ t₁ : ℝ) where
  time_ordered : t₀ ≤ t₁
  slice : Set.Icc t₀ t₁ → WidthComponentSlice.{u}
  initial_identification : Diffeomorph (𝓡 3) (𝓡 3) M
    (slice ⟨t₀, ⟨le_rfl, time_ordered⟩⟩).carrier.carrier ∞
  initial_class_nonzero :
    componentPiThreeClass (slice ⟨t₀, ⟨le_rfl, time_ordered⟩⟩) ≠ 1
  surgery_times : Set ℝ
  surgery_finite : (surgery_times ∩ Set.Icc t₀ t₁).Finite
  transport : ∀ s t : Set.Icc t₀ t₁, s.1 ≤ t.1 →
    SmoothComponentClassMap (slice s) (slice t)
  regular_slabs : ∀ a b : Set.Icc t₀ t₁, a.1 < b.1 →
    Disjoint surgery_times (Set.Ioc a.1 b.1) → Nonempty (WidthRegularSlab slice a b)
  surgery_comparison : ∀ t : Set.Icc t₀ t₁, t.1 ∈ surgery_times →
    ∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
      ∀ s : Set.Icc t₀ t₁, t.1 - delta < s.1 → s.1 < t.1 →
        ∃ f : SmoothComponentClassMap (slice s) (slice t),
          ComponentMapDegreeOne f ∧
          (∀ x y, (slice t).metric.edist (f.map x) (f.map y) ≤
            ENNReal.ofReal (1 + eta) * (slice s).metric.edist x y) ∧
          (∀ (hst : s.1 < t.1) alpha,
            mappedHomotopyClass (n := 3) f.map f.based alpha =
              mappedHomotopyClass (transport s t (le_of_lt hst)).map
                (transport s t (le_of_lt hst)).based alpha)

noncomputable def componentWidth {t₀ t₁ : ℝ}
    (P : SurgeryComponentPath M t₀ t₁)
    (t : Set.Icc t₀ t₁) : ℝ :=
  classWidth (P.slice t).metric (P.slice t).family

noncomputable def componentScalarInfimum {t₀ t₁ : ℝ}
    (P : SurgeryComponentPath M t₀ t₁)
    (t : Set.Icc t₀ t₁) : ℝ :=
  sInf (Set.range (fun x : (P.slice t).carrier.carrier =>
    (P.slice t).connection.scalarCurvature x))

end PoincareConjecture

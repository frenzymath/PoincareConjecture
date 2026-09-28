import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import PoincareConjecture.Definitions.Ch01.Topology
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Topology.Homotopy.Equiv











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture

def surgeryMappedGenLoop {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} {n : ℕ} (f : ContinuousMap X Y) (h : f x = y)
    (gamma : GenLoop (Fin n) X x) : GenLoop (Fin n) Y y :=
  ⟨f.comp gamma.1, fun z hz => by
    change f (gamma z) = y
    have hg : gamma z = x := gamma.2 z hz
    simpa [hg] using h⟩

def surgeryHomotopyMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} {n : ℕ} (f : ContinuousMap X Y) (h : f x = y) :
    HomotopyGroup.Pi n X x → HomotopyGroup.Pi n Y y :=
  Quotient.map (surgeryMappedGenLoop f h)
    (fun _ _ hab => hab.comp_continuousMap f)

noncomputable def surgeryThirdHomology (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} ℤ :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) 3).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X))

noncomputable def surgeryThirdHomologyMap {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : ContinuousMap X Y) :
    surgeryThirdHomology X →ₗ[ℤ] surgeryThirdHomology Y :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) 3).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))).map (TopCat.ofHom f)).hom


structure SurgerySelectedComponent (A : GeneralizedSliceCarrier.{u}) where
  carrier : GeneralizedSliceCarrier.{u}
  basepoint : carrier.carrier
  inclusion : carrier.carrier → A.carrier
  inverse : A.carrier → carrier.carrier
  inclusion_openEmbedding : Topology.IsOpenEmbedding inclusion
  inclusion_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ inclusion
  inverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inverse (Set.range inclusion)
  left_inverse : Function.LeftInverse inverse inclusion
  range_eq_component : Set.range inclusion = connectedComponent (inclusion basepoint)
  compact : IsCompact (Set.univ : Set carrier.carrier)
  connected : IsConnected (Set.univ : Set carrier.carrier)



structure SurgeryComparisonInput (F : SurgeryFlowData.{u})
    (T : ℝ) (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier] where
  parent : SurgerySelectedComponent (F.slice (F.event T hT).tMinus)
  child : SurgerySelectedComponent (F.slice T)
  parent_metric : ℝ → RiemannianMetric 3 parent.carrier.carrier
  child_metric : RiemannianMetric 3 child.carrier.carrier
  parent_pullback : ∀ t : Set.Ico (F.event T hT).tMinus T,
    ∀ x v w, ((F.event T hT).pre_flow.metric t.1).inner (parent.inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) parent.inclusion x v)
      (mfderiv (𝓡 3) (𝓡 3) parent.inclusion x w) =
        (parent_metric t.1).inner x v w
  child_pullback : ∀ x v w, (F.metric T).inner (child.inclusion x)
    (mfderiv (𝓡 3) (𝓡 3) child.inclusion x v)
    (mfderiv (𝓡 3) (𝓡 3) child.inclusion x w) = child_metric.inner x v w
  separating : ∀ i : Fin (F.event T hT).cap_count,
    SeparatingSphere
      (parent.inverse '' ((F.event T hT).limit_identify.inverse ''
        ((F.event T hT).necks i).neck.central_sphere))
  inherited : ∃ x : parent.carrier.carrier,
    parent.inclusion x ∈ interior (F.event T hT).retained_pre ∧
      (F.event T hT).retention.map (parent.inclusion x) ∈ Set.range child.inclusion
  parent_simply_connected : SimplyConnectedSpace parent.carrier.carrier
  child_simply_connected : SimplyConnectedSpace child.carrier.carrier
  parent_orientation : surgeryThirdHomology parent.carrier.carrier ≃ₗ[ℤ] ULift.{u} ℤ

def SurgeryComparisonInput.retained
    {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
    [Nonempty (F.slice T).carrier]
    (I : SurgeryComparisonInput F T hT) : Set I.parent.carrier.carrier :=
  {x | I.parent.inclusion x ∈ interior (F.event T hT).retained_pre ∧
    (F.event T hT).retention.map (I.parent.inclusion x) ∈ Set.range I.child.inclusion}

structure SurgeryComparisonConclusion {F : SurgeryFlowData.{u}}
    {T : ℝ} {hT : T ∈ F.surgery_times} [Nonempty (F.slice T).carrier]
    (I : SurgeryComparisonInput F T hT) where
  map : ContinuousMap I.parent.carrier.carrier I.child.carrier.carrier
  target_basepoint : I.child.carrier.carrier
  based : map I.parent.basepoint = target_basepoint
  child_orientation : surgeryThirdHomology I.child.carrier.carrier ≃ₗ[ℤ] ULift.{u} ℤ
  retained_agreement : ∀ x ∈ I.retained,
    I.child.inclusion (map x) = (F.event T hT).retention.map (I.parent.inclusion x)
  outside_distance_decreasing : ∃ d : ℝ, 0 < d ∧
    ∀ t : ℝ, T - d < t → t < T →
      ∀ x ∉ I.retained, ∀ y ∉ I.retained,
        I.child_metric.edist (map x) (map y) ≤
          intrinsicEDist (I.parent_metric t) I.retainedᶜ x y
  ambient_distance_decreasing : ∃ d : ℝ, 0 < d ∧
    ∀ t : ℝ, T - d < t → t < T →
      ∀ x ∉ I.retained, ∀ y ∉ I.retained,
        I.child_metric.edist (map x) (map y) ≤
          (I.parent_metric t).edist x y
  degree_one : ∀ z : surgeryThirdHomology I.parent.carrier.carrier,
    child_orientation (surgeryThirdHomologyMap map z) = I.parent_orientation z
  homotopy_equivalence : ∃ e : ContinuousMap.HomotopyEquiv
    I.parent.carrier.carrier I.child.carrier.carrier, e.toFun = map
  pi_three_bijective : Function.Bijective (surgeryHomotopyMap (n := 3) map based)
  smooth_approximants : ∀ eta : ℝ, 0 < eta → ∃ d : ℝ, 0 < d ∧
    ∀ t : ℝ, T - d < t → t < T →
      ∃ f : ContinuousMap I.parent.carrier.carrier I.child.carrier.carrier,
        ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧
        (∃ hbase : f I.parent.basepoint = target_basepoint,
          ∀ alpha, surgeryHomotopyMap (n := 3) f hbase alpha =
            surgeryHomotopyMap map based alpha) ∧
        ContinuousMap.Homotopic f map ∧
        (∀ x y, I.child_metric.edist (f x) (f y) ≤
          ENNReal.ofReal (1 + eta) * (I.parent_metric t).edist x y) ∧
        (∀ z : surgeryThirdHomology I.parent.carrier.carrier,
          child_orientation (surgeryThirdHomologyMap f z) = I.parent_orientation z)

end PoincareConjecture

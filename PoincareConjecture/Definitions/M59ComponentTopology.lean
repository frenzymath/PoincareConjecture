import PoincareConjecture.Definitions.Ch15.SurgeryComparison
import PoincareConjecture.Definitions.Ch18.WidthEvolution
import PoincareConjecture.Statement
import Mathlib.Topology.Covering.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval ContinuousMap

universe u

namespace PoincareConjecture

section Cover

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

structure M59PointedFiniteSmoothUniversalCover (x : M) where
  space : GeneralizedSliceCarrier.{u}
  projection : ContinuousMap space.carrier M
  covering : IsCoveringMap projection
  surjective : Function.Surjective projection
  finite_fibers : ∀ y : M, (projection ⁻¹' {y}).Finite
  local_diffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ projection
  compact : IsCompact (Set.univ : Set space.carrier)
  simply_connected : SimplyConnectedSpace space.carrier
  lift : space.carrier
  based : projection lift = x
  homotopy_three_sphere : Nonempty (space.carrier ≃ₕ ThreeSphere)
  cover_pi_three_integer :
    HomotopyGroup.Pi 3 space.carrier lift ≃* Multiplicative ℤ
  projection_pi_three :
    HomotopyGroup.Pi 3 space.carrier lift ≃* HomotopyGroup.Pi 3 M x
  projection_pi_three_eq : ∀ alpha,
    projection_pi_three alpha = surgeryHomotopyMap (n := 3) projection based alpha

noncomputable def M59PointedFiniteSmoothUniversalCover.basePiThreeInteger {x : M}
    (U : M59PointedFiniteSmoothUniversalCover x) :
    HomotopyGroup.Pi 3 M x ≃* Multiplicative ℤ :=
  U.projection_pi_three.symm.trans U.cover_pi_three_integer

end Cover

section Width

variable {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
  (sphere_parameter : ContinuousMap (Fin 2 → I) LoopTwoSphere)
  (loop_pi_three :
    HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
      (constantC1Loop C.basepoint) ≃*
        HomotopyGroup.Pi 3 C.carrier.carrier C.basepoint)
  (xi : HomotopyGroup.Pi 3 C.carrier.carrier C.basepoint)

structure M59WidthCarrierRepresentative where
  family : FreeTwoSphereFamily (M := C.carrier.carrier)
  sphere_parameter_eq : family.class_certificate.sphere_parameter = sphere_parameter
  class_eq : familySigmaClass family = ⟨C.basepoint, loop_pi_three.symm xi⟩

namespace M59WidthCarrierRepresentative

variable {C sphere_parameter loop_pi_three xi}

theorem basepoint_eq
    (R : M59WidthCarrierRepresentative C sphere_parameter loop_pi_three xi) :
    R.family.basepoint = C.basepoint :=
  congrArg Sigma.fst R.class_eq

variable (R : M59WidthCarrierRepresentative C sphere_parameter loop_pi_three xi)
  (ambient_metric : RiemannianMetric 3 A.carrier)
  (metric : RiemannianMetric 3 C.carrier.carrier)
  (connection : LeviCivitaData metric)
  (metric_pullback : ∀ x v w,
    ambient_metric.inner (C.inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) = metric.inner x v w)
  (orientation : componentThirdHomology C.carrier.carrier ≃ₗ[ℤ] ULift.{u} ℤ)
  (pi_two_trivial : Subsingleton (HomotopyGroup.Pi 2 C.carrier.carrier C.basepoint))
  (pi_three_integer : HomotopyGroup.Pi 3 C.carrier.carrier C.basepoint ≃*
    Multiplicative ℤ)

def toLegacy : WidthComponentSlice.{u} :=
  { ambient := A
    carrier := C.carrier
    inclusion := C.inclusion
    inclusion_openEmbedding := C.inclusion_openEmbedding
    inclusion_smooth := C.inclusion_smooth
    ambient_metric := ambient_metric
    metric := metric
    connection := connection
    metric_pullback := metric_pullback
    compact := C.compact
    connected := C.connected
    family := R.family
    component_range := by simpa only [R.basepoint_eq] using C.range_eq_component
    pi_two := by simpa only [R.basepoint_eq] using pi_two_trivial
    loop_pi_three := Eq.mpr
      (congrArg (fun x : C.carrier.carrier =>
        HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
          (constantC1Loop x) ≃* HomotopyGroup.Pi 3 C.carrier.carrier x)
        R.basepoint_eq) loop_pi_three
    pi_three_integer := Eq.mpr
      (congrArg (fun x : C.carrier.carrier =>
        HomotopyGroup.Pi 3 C.carrier.carrier x ≃* Multiplicative ℤ)
        R.basepoint_eq) pi_three_integer
    orientation := orientation }

@[simp] theorem toLegacy_ambient :
    (R.toLegacy ambient_metric metric connection metric_pullback orientation
      pi_two_trivial pi_three_integer).ambient = A := rfl

@[simp] theorem toLegacy_carrier :
    (R.toLegacy ambient_metric metric connection metric_pullback orientation
      pi_two_trivial pi_three_integer).carrier = C.carrier := rfl

@[simp] theorem toLegacy_inclusion :
    (R.toLegacy ambient_metric metric connection metric_pullback orientation
      pi_two_trivial pi_three_integer).inclusion = C.inclusion := rfl

@[simp] theorem toLegacy_ambient_metric :
    (R.toLegacy ambient_metric metric connection metric_pullback orientation
      pi_two_trivial pi_three_integer).ambient_metric = ambient_metric := rfl

@[simp] theorem toLegacy_metric :
    (R.toLegacy ambient_metric metric connection metric_pullback orientation
      pi_two_trivial pi_three_integer).metric = metric := rfl

@[simp] theorem toLegacy_connection :
    (R.toLegacy ambient_metric metric connection metric_pullback orientation
      pi_two_trivial pi_three_integer).connection = connection := rfl

@[simp] theorem toLegacy_orientation :
    (R.toLegacy ambient_metric metric connection metric_pullback orientation
      pi_two_trivial pi_three_integer).orientation = orientation := rfl

@[simp] theorem toLegacy_family :
    (R.toLegacy ambient_metric metric connection metric_pullback orientation
      pi_two_trivial pi_three_integer).family = R.family := rfl

theorem toLegacy_class :
    (⟨R.family.basepoint,
      componentPiThreeClass (R.toLegacy ambient_metric metric connection metric_pullback
        orientation pi_two_trivial pi_three_integer)⟩ :
      Σ x : C.carrier.carrier, HomotopyGroup.Pi 3 C.carrier.carrier x) =
        ⟨C.basepoint, xi⟩ := by
  have htransport : ∀ {a b : C.carrier.carrier} (h : a = b)
      (e : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
        (constantC1Loop b) ≃* HomotopyGroup.Pi 3 C.carrier.carrier b)
      (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
        (constantC1Loop a))
      (beta : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
        (constantC1Loop b)),
      (⟨a, alpha⟩ : Σ x : C.carrier.carrier,
        HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
          (constantC1Loop x)) = ⟨b, beta⟩ →
      (⟨a, (Eq.mpr (congrArg (fun x : C.carrier.carrier =>
        HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
          (constantC1Loop x) ≃* HomotopyGroup.Pi 3 C.carrier.carrier x) h) e) alpha⟩ :
        Σ x : C.carrier.carrier, HomotopyGroup.Pi 3 C.carrier.carrier x) =
          ⟨b, e beta⟩ := by
    intro a b h
    cases h
    intro e alpha beta hclass
    have hab : alpha = beta := eq_of_heq (Sigma.mk.inj_iff.mp hclass).2
    cases hab
    rfl
  change (⟨R.family.basepoint, (Eq.mpr (congrArg (fun x : C.carrier.carrier =>
    HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
      (constantC1Loop x) ≃* HomotopyGroup.Pi 3 C.carrier.carrier x)
      R.basepoint_eq) loop_pi_three) R.family.homotopy_class⟩ :
    Σ x : C.carrier.carrier, HomotopyGroup.Pi 3 C.carrier.carrier x) =
      ⟨C.basepoint, xi⟩
  simpa only [MulEquiv.apply_symm_apply] using
    htransport R.basepoint_eq loop_pi_three R.family.homotopy_class
      (loop_pi_three.symm xi) R.class_eq

end M59WidthCarrierRepresentative

end Width

end PoincareConjecture

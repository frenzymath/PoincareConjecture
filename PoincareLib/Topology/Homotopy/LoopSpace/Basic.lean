import PoincareLib.Geometry.Riemannian.Metric
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.CompactOpen

/-!
# The C1 free-loop space

Adapted from Mapher commit f927d9e1f0810042766d3b5f64d3f4da02ee93cc.
Source: Morgan--Tian, Definition 18.17 and Lemma 18.27, pp. 430, 434-435.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval
universe u
namespace PoincareMT

abbrev LoopPlane := EuclideanSpace ℝ (Fin 2)
abbrev LoopAmbient := EuclideanSpace ℝ (Fin 3)

/-- The closed unit disk used as a parametrized filling domain. -/
def loopDiskSet : Set LoopPlane := Metric.closedBall 0 1

/-- The unit circle, represented as a subtype of the parameter plane. -/
abbrev LoopCircle := {z : LoopPlane // ‖z‖ = 1}

/-- The disk with its subspace topology. -/
abbrev LoopDisk := {z : LoopPlane // z ∈ loopDiskSet}

/-- The parameter two-sphere for free families. -/
abbrev LoopTwoSphere := {z : LoopAmbient // ‖z‖ = 1}

/-- A fixed annular neighborhood, with no filling-disk condition. -/
def loopAnnulus : Set LoopPlane := {z | 1 / 2 < ‖z‖ ∧ ‖z‖ < 2}

/-- The counterclockwise unit tangent at a point of the unit circle. -/
noncomputable def loopCircleTangent (z : LoopCircle) : LoopPlane :=
  !₂[-z.1 1, z.1 0]

instance : Coe LoopCircle LoopPlane := ⟨Subtype.val⟩
instance : Coe LoopDisk LoopPlane := ⟨Subtype.val⟩
instance : Coe LoopTwoSphere LoopAmbient := ⟨Subtype.val⟩

/-- A circle reparameterization is an explicit homeomorphism of the boundary. -/
structure CircleReparameterization where
  map : LoopCircle → LoopCircle
  inverse : LoopCircle → LoopCircle
  left_inverse : Function.LeftInverse inverse map
  right_inverse : Function.RightInverse inverse map
  continuous_map : Continuous map
  continuous_inverse : Continuous inverse

/-- A compact connected smooth three-manifold carrier. -/
structure CompactConnectedThreeManifold (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] where
  hausdorff : T2Space M
  second_countable : SecondCountableTopology M
  compact : IsCompact (Set.univ : Set M)
  connected : IsConnected (Set.univ : Set M)
  nonempty : (Set.univ : Set M).Nonempty

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- C¹ regularity of a circle map, expressed by an ambient neighbourhood extension. -/
def IsC1Loop (γ : LoopCircle → M) : Prop :=
  ∃ extension : LoopPlane → M,
    (∀ z : LoopCircle, extension z = γ z) ∧
      ContMDiffOn (𝓡 2) (𝓡 3) 1 extension loopAnnulus

/-- The project-owned C¹ free-loop space.  The extension and its regularity are
part of each loop. The topology ignores its off-circle values and normal
derivatives, retaining only the intrinsic first jet of the circle map. -/
structure C1FreeLoopSpace where
  toFun : LoopCircle → M
  extension : LoopPlane → M
  boundary : ∀ z : LoopCircle, extension z = toFun z
  regularity : ContMDiffOn (𝓡 2) (𝓡 3) 1 extension loopAnnulus
  continuous : Continuous toFun
  tangent_continuous : Continuous (fun z : LoopCircle =>
    (⟨toFun z, mfderiv (𝓡 2) (𝓡 3) extension z.1 (loopCircleTangent z)⟩ :
      TangentBundle (𝓡 3) M))

instance : CoeFun (C1FreeLoopSpace (M := M)) (fun _ => LoopCircle → M) :=
  ⟨fun γ => γ.toFun⟩

/-- The canonical C¹ extension carried by the loop object. -/
def c1LoopExtension (γ : C1FreeLoopSpace (M := M)) : LoopPlane → M :=
  γ.extension

/-- The first derivative field, packaged in the tangent bundle so that its base
point and its vector vary together. -/
noncomputable def c1LoopDerivative (γ : C1FreeLoopSpace (M := M))
    (z : LoopCircle) (i : Fin 2) : TangentBundle (𝓡 3) M :=
  ⟨γ z, (mfderiv (𝓡 2) (𝓡 3) (c1LoopExtension γ) z)
    (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩

/-- The intrinsic derivative; normal derivatives of an extension do not enter
the loop topology. -/
noncomputable def c1LoopTangent (γ : C1FreeLoopSpace (M := M)) :
    ContinuousMap LoopCircle (TangentBundle (𝓡 3) M) :=
  ⟨fun z => ⟨γ z, mfderiv (𝓡 2) (𝓡 3) γ.extension z.1 (loopCircleTangent z)⟩,
    γ.tangent_continuous⟩

/-- The C¹ topology is the induced topology of two compact-open function
spaces. In particular, convergence controls the whole compact circle. -/
noncomputable instance : TopologicalSpace (C1FreeLoopSpace (M := M)) :=
  TopologicalSpace.induced
    (fun γ => ((⟨γ.toFun, γ.continuous⟩ : ContinuousMap LoopCircle M),
      c1LoopTangent γ)) inferInstance

/-- The constant C¹ loop at a point. -/
noncomputable def constantC1Loop (x : M) : C1FreeLoopSpace (M := M) :=
  { toFun := fun _ => x
    extension := fun _ => x
    boundary := fun _ => rfl
    regularity := by
      simpa using (contMDiff_const.contMDiffOn :
        ContMDiffOn (𝓡 2) (𝓡 3) 1 (fun _ : LoopPlane => x) loopAnnulus)
    continuous := continuous_const
    tangent_continuous := by
      convert (continuous_const : Continuous (fun _ : LoopCircle =>
        (⟨x, 0⟩ : TangentBundle (𝓡 3) M))) using 1
      funext z
      simp only [mfderiv_const]
      rfl }

/-- A path in the free-loop space from a loop to a constant loop. -/
def InIdentityComponent (x₀ : M) (γ : C1FreeLoopSpace (M := M)) : Prop :=
  ∃ H : Set.Icc (0 : ℝ) 1 → C1FreeLoopSpace,
    Continuous H ∧ H ⟨0, by simp⟩ = γ ∧
      H ⟨1, by simp⟩ = constantC1Loop x₀

/-- A continuous disk extension witnesses that a loop is null-homotopic. -/
def IsNullHomotopicLoop (γ : C1FreeLoopSpace (M := M)) : Prop :=
  ∃ extension : LoopPlane → M,
    Continuous extension ∧
      ∀ z : LoopCircle, extension z = γ z


end PoincareMT

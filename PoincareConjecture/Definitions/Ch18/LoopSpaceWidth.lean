import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.CompactOpen

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval

universe u

namespace PoincareConjecture

abbrev LoopPlane := EuclideanSpace ℝ (Fin 2)
abbrev LoopAmbient := EuclideanSpace ℝ (Fin 3)

def loopDiskSet : Set LoopPlane := Metric.closedBall 0 1

abbrev LoopCircle := {z : LoopPlane // ‖z‖ = 1}

abbrev LoopDisk := {z : LoopPlane // z ∈ loopDiskSet}

abbrev LoopTwoSphere := {z : LoopAmbient // ‖z‖ = 1}

def loopAnnulus : Set LoopPlane := {z | 1 / 2 < ‖z‖ ∧ ‖z‖ < 2}

noncomputable def loopCircleTangent (z : LoopCircle) : LoopPlane :=
  !₂[-z.1 1, z.1 0]

instance : Coe LoopCircle LoopPlane := ⟨Subtype.val⟩
instance : Coe LoopDisk LoopPlane := ⟨Subtype.val⟩
instance : Coe LoopTwoSphere LoopAmbient := ⟨Subtype.val⟩

structure CircleReparameterization where
  map : LoopCircle → LoopCircle
  inverse : LoopCircle → LoopCircle
  left_inverse : Function.LeftInverse inverse map
  right_inverse : Function.RightInverse inverse map
  continuous_map : Continuous map
  continuous_inverse : Continuous inverse

structure CompactConnectedThreeManifold (M : Type u) [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] where
  hausdorff : T2Space M
  second_countable : SecondCountableTopology M
  compact : IsCompact (Set.univ : Set M)
  connected : IsConnected (Set.univ : Set M)
  nonempty : (Set.univ : Set M).Nonempty

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

def IsC1Loop (γ : LoopCircle → M) : Prop :=
  ∃ extension : LoopPlane → M,
    (∀ z : LoopCircle, extension z = γ z) ∧
      ContMDiffOn (𝓡 2) (𝓡 3) 1 extension loopAnnulus

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

def c1LoopExtension (γ : C1FreeLoopSpace (M := M)) : LoopPlane → M :=
  γ.extension

noncomputable def c1LoopDerivative (γ : C1FreeLoopSpace (M := M))
    (z : LoopCircle) (i : Fin 2) : TangentBundle (𝓡 3) M :=
  ⟨γ z, (mfderiv (𝓡 2) (𝓡 3) (c1LoopExtension γ) z)
    (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩

noncomputable def c1LoopTangent (γ : C1FreeLoopSpace (M := M)) :
    ContinuousMap LoopCircle (TangentBundle (𝓡 3) M) :=
  ⟨fun z => ⟨γ z, mfderiv (𝓡 2) (𝓡 3) γ.extension z.1 (loopCircleTangent z)⟩,
    γ.tangent_continuous⟩

noncomputable instance : TopologicalSpace (C1FreeLoopSpace (M := M)) :=
  TopologicalSpace.induced
    (fun γ => ((⟨γ.toFun, γ.continuous⟩ : ContinuousMap LoopCircle M),
      c1LoopTangent γ)) inferInstance

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

def InIdentityComponent (x₀ : M) (γ : C1FreeLoopSpace (M := M)) : Prop :=
  ∃ H : Set.Icc (0 : ℝ) 1 → C1FreeLoopSpace,
    Continuous H ∧ H ⟨0, by simp⟩ = γ ∧
      H ⟨1, by simp⟩ = constantC1Loop x₀

def IsNullHomotopicLoop (γ : C1FreeLoopSpace (M := M)) : Prop :=
  ∃ extension : LoopPlane → M,
    Continuous extension ∧
      ∀ z : LoopCircle, extension z = γ z

def loopBoundary : Set LoopPlane := {z | ‖z‖ = 1}

noncomputable def parametrizedAreaDensity (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) (z : LoopPlane) : ℝ :=
  let d := mfderiv (𝓡 2) (𝓡 3) f z
  let e : Fin 2 → TangentSpace (𝓡 3) (f z) :=
    fun i => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  Real.sqrt (max 0 (Matrix.det (fun i j => g.inner (f z) (e i) (e j))))

noncomputable def parametrizedRiemannianArea (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) : ℝ :=
  ∫ z in loopDiskSet, parametrizedAreaDensity g f z ∂MeasureTheory.volume

structure LipschitzSpanningDisk (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) where
  map : LoopPlane → M
  continuous_on_disk : ContinuousOn map loopDiskSet

  ae_manifold_differentiable : ∀ᵐ z ∂MeasureTheory.volume,
    z ∈ loopDiskSet → MDifferentiableAt (𝓡 2) (𝓡 3) map z
  reparameterization : CircleReparameterization
  boundary_eq : ∀ z : LoopCircle,
    map z = γ (reparameterization.map z)
  lipschitz_constant : ℝ
  lipschitz_nonnegative : 0 ≤ lipschitz_constant
  lipschitz_on_disk : ∀ x y : LoopDisk,
    g.edist (map x) (map y) ≤
      ENNReal.ofReal lipschitz_constant * ENNReal.ofReal ‖(x : LoopPlane) - y‖
  area_integrable : MeasureTheory.IntegrableOn
    (parametrizedAreaDensity g map) loopDiskSet MeasureTheory.volume
  area_nonnegative : 0 ≤ parametrizedRiemannianArea g map

namespace LipschitzSpanningDisk

noncomputable def area {g : RiemannianMetric 3 M}
    {γ : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g γ) : ℝ :=
  parametrizedRiemannianArea g D.map

end LipschitzSpanningDisk

structure FillingAreaData (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) where
  nonempty : Nonempty (LipschitzSpanningDisk g γ)
  finite_witness : ∃ D : LipschitzSpanningDisk g γ, ∃ C : ℝ, D.area ≤ C
  bounded_below : BddBelow (Set.range (fun D : LipschitzSpanningDisk g γ => D.area))

noncomputable def fillingArea (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) : ℝ :=
  sInf (Set.range (fun D : LipschitzSpanningDisk g γ => D.area))

structure FreeTwoSphereClassCertificate
    (basepoint : M)
    (family : LoopTwoSphere → C1FreeLoopSpace (M := M))
    (α : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop basepoint)) where
  cube_representative : ContinuousMap (Fin 2 → I) (C1FreeLoopSpace (M := M))
  boundary_const : ∀ y ∈ Cube.boundary (Fin 2),
    cube_representative y = constantC1Loop basepoint
  sphere_parameter : ContinuousMap (Fin 2 → I) LoopTwoSphere
  sphere_parameter_surjective : Function.Surjective sphere_parameter
  sphere_parameter_boundary_collapsed : ∃ c : LoopTwoSphere, ∀ y,
    y ∈ Cube.boundary (Fin 2) → sphere_parameter y = c

  sphere_parameter_quotient_fiber : ∀ y z,
    sphere_parameter y = sphere_parameter z ↔
      y = z ∨ (y ∈ Cube.boundary (Fin 2) ∧ z ∈ Cube.boundary (Fin 2))
  family_agreement : ∀ y,
    cube_representative y = family (sphere_parameter y)
  class_eq : α = Quotient.mk'
    (⟨cube_representative, boundary_const⟩ :
      GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop basepoint))

structure FreeTwoSphereFamily where

  basepoint : M
  family : LoopTwoSphere → C1FreeLoopSpace (M := M)

  homotopy_class : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
    (constantC1Loop basepoint)
  class_certificate : FreeTwoSphereClassCertificate basepoint family homotopy_class
  continuous : Continuous family
  derivative_continuous : ∀ i : Fin 2,
    Continuous (fun p : LoopTwoSphere × LoopCircle =>
      c1LoopDerivative (family p.1) p.2 i)
  null_homotopic : ∀ c, IsNullHomotopicLoop (family c)
  joint_extension : ∃ extension : LoopTwoSphere × LoopPlane → M,
    ContinuousOn extension (Set.univ ×ˢ loopAnnulus) ∧
      (∀ c (z : LoopCircle), extension (c, z.1) = family c z) ∧
      ∀ c, ContMDiffOn (𝓡 2) (𝓡 3) 1 (fun z => extension (c, z)) loopAnnulus

noncomputable def familyWidth (g : RiemannianMetric 3 M)
    (Γ : FreeTwoSphereFamily (M := M)) : ℝ :=
  sSup (Set.range (fun c => fillingArea g (Γ.family c)))

def familySigmaClass (Γ : FreeTwoSphereFamily (M := M)) :
    Σ x : M, HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop x) :=
  ⟨Γ.basepoint, Γ.homotopy_class⟩

structure FamilyWidthData (g : RiemannianMetric 3 M)
    (Γ : FreeTwoSphereFamily (M := M)) where
  filling_data : ∀ c, FillingAreaData g (Γ.family c)
  bounded_above : BddAbove (Set.range (fun c => fillingArea g (Γ.family c)))
  attained : ∃ c : LoopTwoSphere,
    fillingArea g (Γ.family c) = familyWidth g Γ

def FreeTwoSphereHomotopic (Γ₁ Γ₂ : FreeTwoSphereFamily (M := M)) : Prop :=
  ∃ H : Set.Icc (0 : ℝ) 1 → FreeTwoSphereFamily,
    Γ₁.basepoint = Γ₂.basepoint ∧
      familySigmaClass Γ₁ = familySigmaClass Γ₂ ∧
      (∀ s, (H s).basepoint = Γ₁.basepoint) ∧
      Continuous (fun p : Set.Icc (0 : ℝ) 1 × LoopTwoSphere => (H p.1).family p.2) ∧
      H ⟨0, by simp⟩ = Γ₁ ∧ H ⟨1, by simp⟩ = Γ₂

noncomputable def classWidthRange (g : RiemannianMetric 3 M)
    (ξ : FreeTwoSphereFamily (M := M)) : Set ℝ :=
  by classical
    exact {w | ∃ Γ : FreeTwoSphereFamily (M := M),
      familySigmaClass Γ = familySigmaClass ξ ∧
        Nonempty (FreeTwoSphereClassCertificate Γ.basepoint Γ.family
          Γ.homotopy_class) ∧
        FreeTwoSphereHomotopic ξ Γ ∧ familyWidth g Γ = w}

noncomputable def classWidth (g : RiemannianMetric 3 M)
    (ξ : FreeTwoSphereFamily (M := M)) : ℝ :=
  by classical
    exact sInf (classWidthRange g ξ)

structure ClassWidthData (g : RiemannianMetric 3 M)
    (ξ : FreeTwoSphereFamily (M := M)) where
  based_class : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
    (constantC1Loop ξ.basepoint)
  based_class_eq : based_class = ξ.homotopy_class
  representative : FreeTwoSphereFamily (M := M)
  representative_based : representative.basepoint = ξ.basepoint
  representative_class : familySigmaClass representative = familySigmaClass ξ
  representative_homotopic : FreeTwoSphereHomotopic ξ representative
  representative_width_finite : ∃ C : ℝ, familyWidth g representative ≤ C
  bounded_below : BddBelow (classWidthRange g ξ)

end PoincareConjecture

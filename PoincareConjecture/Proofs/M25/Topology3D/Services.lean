import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false

open scoped Manifold ContDiff
open Set Metric

namespace PoincareConjecture.M25.Topology3D

abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev E2 := EuclideanSpace ℝ (Fin 2)

noncomputable def sphereMap (A : E3 ≃ₗᵢ[ℝ] E3) (x : UnitTwoSphere) : UnitTwoSphere :=
  ⟨A x.1, by
    rw [mem_sphere_zero_iff_norm, A.norm_map]
    exact mem_sphere_zero_iff_norm.mp x.2⟩

structure DiffSphereIsotopyData (f : UnitTwoSphere → UnitTwoSphere) where
  isometry : E3 ≃ₗᵢ[ℝ] E3
  isotopy : ℝ → UnitTwoSphere → UnitTwoSphere
  isotopy_smooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
    (fun p : ℝ × UnitTwoSphere => isotopy p.1 p.2)
  isotopy_diffeo : ∀ t : ℝ, ∃ g : Diffeomorph (𝓡 2) (𝓡 2)
    UnitTwoSphere UnitTwoSphere ∞, ∀ x, g x = isotopy t x
  isotopy_zero : ∀ x, isotopy 0 x = sphereMap isometry x
  isotopy_one : ∀ x, isotopy 1 x = f x

def DiffSphereIsotopyService : Prop :=
  ∀ f : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
    Nonempty (DiffSphereIsotopyData f)

structure PlanarSchoenfliesData (c : UnitCircle → E2) where
  inside : Set E2
  inside_open : IsOpen inside
  inside_bounded : Bornology.IsBounded inside
  inside_connected : IsConnected inside
  outside_connected : IsConnected (univ \ (inside ∪ range c))
  inside_disjoint : Disjoint inside (range c)
  radius : ℝ
  one_lt_radius : 1 < radius
  chart : E2 → E2
  chart_smooth : ContDiffOn ℝ ∞ chart (ball 0 radius)
  chart_injOn : InjOn chart (ball 0 radius)
  chart_open_map : IsOpen (chart '' ball 0 radius)
  chart_image_inside : chart '' ball 0 1 = inside
  chart_boundary : ∀ q : UnitCircle, chart q.1 = c q
  chart_inverse : ∃ Ψ : E2 → E2, ContDiffOn ℝ ∞ Ψ (chart '' ball 0 radius) ∧
    ∀ x ∈ ball 0 radius, Ψ (chart x) = x

structure PlanarSchoenfliesFamilyData (c : ℝ → UnitCircle → E2) (a b : ℝ) where
  radius : ℝ
  one_lt_radius : 1 < radius
  margin : ℝ
  margin_pos : 0 < margin
  chart : ℝ → E2 → E2
  chart_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × E2 => chart p.1 p.2)
    (Ioo (a - margin) (b + margin) ×ˢ ball 0 radius)
  chart_injOn : ∀ z ∈ Icc a b, InjOn (chart z) (ball 0 radius)
  chart_immersion : ∀ z ∈ Icc a b, ∀ x ∈ ball 0 radius,
    Function.Injective (fderiv ℝ (chart z) x)
  chart_boundary : ∀ z ∈ Icc a b, ∀ q : UnitCircle, chart z q.1 = c z q
  chart_inside : ∀ z ∈ Icc a b, IsOpen (chart z '' ball 0 1) ∧
    Disjoint (chart z '' ball 0 1) (range (c z)) ∧
    Bornology.IsBounded (chart z '' ball 0 1)

def IsPlanarEmbedding (c : UnitCircle → E2) : Prop :=
  ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ c ∧ Function.Injective c ∧
    ∀ q, Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2) c q)

def PlanarSchoenfliesService : Prop :=
  (∀ c : UnitCircle → E2, IsPlanarEmbedding c → Nonempty (PlanarSchoenfliesData c)) ∧
  (∀ (a b : ℝ) (c : ℝ → UnitCircle → E2), a < b →
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => c p.1 p.2) →
    (∀ z ∈ Icc a b, IsPlanarEmbedding (c z)) →
    Nonempty (PlanarSchoenfliesFamilyData c a b))

structure SchoenfliesData (ψ : UnitTwoSphere × ℝ → E3) (δ : ℝ) where
  side : ℝ
  side_sq : side * side = 1
  inside : Set E3
  inside_open : IsOpen inside
  inside_bounded : Bornology.IsBounded inside
  inside_connected : IsConnected inside
  inside_disjoint : Disjoint inside (ψ '' (univ ×ˢ {0}))
  outside_connected : IsConnected (univ \ (inside ∪ ψ '' (univ ×ˢ {0})))
  collar_inside : (fun p : UnitTwoSphere × ℝ => ψ (p.1, side * p.2)) ''
    (univ ×ˢ Ioo (-1) 0) ⊆ inside
  radius : ℝ
  chart : E3 → E3
  boundary_map : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞
  radial : ℝ → ℝ
  chart_smooth : ContDiffOn ℝ ∞ chart (ball 0 radius)
  chart_injOn : InjOn chart (ball 0 radius)
  chart_image : chart '' ball 0 radius =
    inside ∪ (fun p : UnitTwoSphere × ℝ => ψ (p.1, side * p.2)) '' (univ ×ˢ Ico 0 1)
  chart_inverse : ∃ Ψ : E3 → E3, ContDiffOn ℝ ∞ Ψ (chart '' ball 0 radius) ∧
    ∀ x ∈ ball 0 radius, Ψ (chart x) = x
  radial_strictMono : StrictMonoOn radial (Ico δ 1)
  radial_pos : ∀ s ∈ Ico δ 1, 0 < radial s
  radial_lt : ∀ s ∈ Ico δ 1, radial s < radius
  chart_collar : ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ico δ 1 →
    chart (radial s • (boundary_map q).1) = ψ (q, side * s)

def IsCollarEmbedding (ψ : UnitTwoSphere × ℝ → E3) : Prop :=
  ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ ψ (univ ×ˢ Ioo (-1) 1) ∧
    InjOn ψ (univ ×ˢ Ioo (-1) 1) ∧
    ∀ z ∈ (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (UnitTwoSphere × ℝ)),
      Function.Injective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ψ z)

def SchoenfliesService : Prop :=
  ∀ ψ : UnitTwoSphere × ℝ → E3, IsCollarEmbedding ψ →
    ∀ δ : ℝ, 0 < δ → δ < 1 → Nonempty (SchoenfliesData ψ δ)

end PoincareConjecture.M25.Topology3D

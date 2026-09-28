import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialSliceMap
import PoincareConjecture.Proofs.M09.ManifoldLocalInverse

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

private theorem bijective_iff_of_horizontal_val_eq {a b : G.Point} (h : a = b)
    (A : G.Horizontal x →L[ℝ] G.Horizontal a) (B : G.Horizontal x →L[ℝ] G.Horizontal b)
    (hval : ∀ W, (A W).val = (B W).val) : Function.Bijective A ↔ Function.Bijective B := by
  cases h
  have heq : A = B := ContinuousLinearMap.ext (fun W => Subtype.ext (hval W))
  rw [heq]

theorem exponentialSliceMap_differential_bijective_iff (E : M14ExponentialFamily G T x)
    {τ : ℝ} (hτ : 0 ≤ τ) (q₀ : (G.slices (T - τ)).Point)
    {Z : G.Horizontal x} (hZ : (Z, Real.sqrt τ) ∈ E.domain) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    Function.Bijective
      (mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n) (exponentialSliceMap E τ hτ q₀) Z) ↔
        Function.Bijective (E.differential Z (Real.sqrt τ) hZ) := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  let f := exponentialSliceMap E τ hτ q₀
  let A : G.Horizontal x →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n) f Z
  let L := (G.slices (T - τ)).tangentEquiv (f Z)
  have hcomp := bijective_iff_of_horizontal_val_eq (exponentialSliceMap_val E hτ q₀ hZ)
    (L.toContinuousLinearMap.comp A) (E.differential Z (Real.sqrt τ) hZ)
    (fun W => exponentialSliceMap_differential_val E hτ q₀ hZ W)
  exact (Function.Bijective.of_comp_iff' L.bijective A).symm.trans hcomp

theorem exists_exponentialSlice_local_inverse (E : M14ExponentialFamily G T x)
    {τ : ℝ} (hτ : 0 ≤ τ) (q₀ : (G.slices (T - τ)).Point)
    {S : Set (G.Horizontal x)} (hS : IsOpen S)
    (hSD : ∀ Z ∈ S, (Z, Real.sqrt τ) ∈ E.domain)
    {Z : G.Horizontal x} (hZS : Z ∈ S)
    (hbij : Function.Bijective (E.differential Z (Real.sqrt τ) (hSD Z hZS))) :
    ∃ e : OpenPartialHomeomorph (G.Horizontal x) (G.slices (T - τ)).Point,
      Z ∈ e.source ∧ e.source ⊆ S ∧
      EqOn (e : G.Horizontal x → (G.slices (T - τ)).Point)
        (exponentialSliceMap E τ hτ q₀) e.source ∧
      M14InverseSliceSmooth G e.symm e.target ∧
      ∀ W ∈ e.source, ∃ hW : (W, Real.sqrt τ) ∈ E.domain,
        Function.Bijective (E.differential W (Real.sqrt τ) hW) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let : FiniteDimensional ℝ (G.Horizontal x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  have hsm : ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (𝓡 n) ∞
      (exponentialSliceMap E τ hτ q₀) S :=
    fun W hW => (exponentialSliceMap_contMDiffAt E hτ q₀ (hSD W hW)).contMDiffWithinAt
  obtain ⟨e, hZe, heS, hef, hinv, heBij⟩ := Proofs.M09.exists_manifold_local_inverse
    (exponentialSliceMap E τ hτ q₀) S hS hsm Z hZS
    ((exponentialSliceMap_differential_bijective_iff E hτ q₀ (hSD Z hZS)).mpr hbij)
  refine ⟨e, hZe, heS, hef, hinv, ?_⟩
  intro W hW
  exact ⟨hSD W (heS hW),
    (exponentialSliceMap_differential_bijective_iff E hτ q₀ (hSD W (heS hW))).mp (heBij W hW)⟩

end PoincareConjecture.M14

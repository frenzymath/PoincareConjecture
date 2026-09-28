import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Embedded.EmbeddedThreeTriangulation
import Mathlib.Geometry.Manifold.WhitneyEmbedding









set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

universe u

namespace Poincare.Topology

private def euclideanZeroPadFour (n : Nat) :
    EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin (n + 4)) where
  toFun x := WithLp.toLp 2 (fun i => if h : i.val < n then x ⟨i.val, h⟩ else 0)
  map_add' := by
    intro x y
    ext i
    change (if h : i.val < n then (x + y) ⟨i.val, h⟩ else 0) =
      (if h : i.val < n then x ⟨i.val, h⟩ else 0) +
        (if h : i.val < n then y ⟨i.val, h⟩ else 0)
    split_ifs
    · rfl
    · exact (zero_add 0).symm
  map_smul' := by
    intro r x
    ext i
    change (if h : i.val < n then (r • x) ⟨i.val, h⟩ else 0) =
      r • (if h : i.val < n then x ⟨i.val, h⟩ else 0)
    split_ifs
    · rfl
    · exact (smul_zero r).symm

private theorem euclideanZeroPadFour_injective (n : Nat) :
    Function.Injective (euclideanZeroPadFour n) := by
  intro x y hxy
  ext i
  have h := congrArg (fun z : EuclideanSpace Real (Fin (n + 4)) =>
    z ⟨i.val, by omega⟩) hxy
  change (if h : i.val < n then x ⟨i.val, h⟩ else 0) =
    (if h : i.val < n then y ⟨i.val, h⟩ else 0) at h
  simpa only [dif_pos i.isLt] using h

theorem exists_compact_three_manifold_finite_triangulation
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] :
    ∃ (I : Type) (_ : PartialOrder I) (_ : Fintype I),
      Nonempty ((finiteOrderComplex I).space ≃ₜ M) ∧
        ∀ t ∈ (finiteOrderComplex I).faces, t.card ≤ 4 := by
  obtain ⟨n, f, hs, he, hi⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 3) (M := M)
  let L := (euclideanZeroPadFour n).toContinuousLinearMap
  let e : C(M, EuclideanSpace Real (Fin (n + 4))) :=
    ⟨L ∘ f, L.continuous.comp hs.continuous⟩
  have hL : Function.Injective L := euclideanZeroPadFour_injective n
  have hs' : ContMDiff (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin (n + 4)))) ∞ e :=
    L.contMDiff.comp hs
  have he' : _root_.Topology.IsClosedEmbedding e :=
    hs'.continuous.isClosedEmbedding (hL.comp he.injective)
  have hi' (p : M) : Function.Injective
      (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin (n + 4)))) e p) := by
    change Function.Injective
      (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin (n + 4)))) (L ∘ f) p)
    rw [mfderiv_comp _ L.mdifferentiableAt (hs.mdifferentiable (by simp)).mdifferentiableAt,
      L.mfderiv_eq]
    exact hL.comp (hi p)
  exact exists_embedded_three_finite_triangulation (by omega) e hs' he' hi'

end Poincare.Topology

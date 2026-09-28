import PoincareConjecture.Proofs.M02.Topology.EmbeddedThreeNearest
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.Topology.Homotopy.Equiv








set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem exists_embedded_three_neighborhood_homotopyEquiv
    [T2Space M] [CompactSpace M] [Nonempty M] :
    ∃ (N : Nat) (e : C(M, EuclideanSpace Real (Fin N))) (r : Real),
      0 < r ∧
      ContMDiff (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) ∞ e ∧
      _root_.Topology.IsClosedEmbedding e ∧
      (∀ p : M, Function.Injective
        (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e p)) ∧
      ∃ h : ContinuousMap.HomotopyEquiv M
          {z : EuclideanSpace Real (Fin N) | Metric.infDist z (Set.range e) < r},
        ∀ p : M, (h p : EuclideanSpace Real (Fin N)) = e p := by
  classical
  obtain ⟨N, f, hs, he, hi⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓡 3) (M := M)
  let e : C(M, EuclideanSpace Real (Fin N)) := ⟨f, hs.continuous⟩
  obtain ⟨r, hr, hc, hnormal⟩ :=
    exists_embedded_three_nearest_neighborhood e hs he hi
  let U := {z : EuclideanSpace Real (Fin N) | Metric.infDist z (Set.range e) < r}
  have hnear (p : M) : e p ∈ U := by
    change Metric.infDist (e p) (Set.range e) < r
    rw [Metric.infDist_zero_of_mem (Set.mem_range_self p)]
    exact hr
  have hfix (p : M) : embeddedThreeNearest e (e p) = p := by
    simpa only [add_zero] using hnormal p 0 (Submodule.zero_mem _)
      (by simpa only [norm_zero] using hr)
  let j : C(M, U) := ⟨fun p => ⟨e p, hnear p⟩, e.continuous.subtype_mk hnear⟩
  let q : C(U, M) := ⟨fun z => embeddedThreeNearest e z.val,
    hc.domRestrict⟩
  have hdist (z : U) : dist z.val (e (q z)) < r := by
    change dist z.val (e (embeddedThreeNearest e z.val)) < r
    obtain ⟨y, ⟨p, rfl⟩, hp⟩ :=
      (Metric.infDist_lt_iff (Set.range_nonempty e)).mp z.property
    exact lt_of_le_of_lt (embeddedThreeNearest_minimal e z.val p) hp
  let H : ContinuousMap.Homotopy (j.comp q) (ContinuousMap.id U) :=
    { toFun := fun z =>
        ⟨(1 - (z.1 : Real)) • e (q z.2) + (z.1 : Real) • z.2.val, by
          apply (Metric.infDist_lt_iff (Set.range_nonempty e)).mpr
          refine ⟨e (q z.2), Set.mem_range_self _, ?_⟩
          have heq : (1 - (z.1 : Real)) • e (q z.2) + (z.1 : Real) • z.2.val -
              e (q z.2) = (z.1 : Real) • (z.2.val - e (q z.2)) := by
            module
          rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg z.1.property.1]
          have hle : (z.1 : Real) * ‖z.2.val - e (q z.2)‖ ≤
              ‖z.2.val - e (q z.2)‖ := by
            exact mul_le_of_le_one_left (norm_nonneg _) z.1.property.2
          exact lt_of_le_of_lt hle (by simpa only [dist_eq_norm] using hdist z.2)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (e.continuous.comp (q.continuous.comp continuous_snd))).add
          ((continuous_subtype_val.comp continuous_fst).smul
            (continuous_subtype_val.comp continuous_snd))
      map_zero_left z := by
        apply Subtype.ext
        change (1 - (0 : Real)) • e (q z) + (0 : Real) • z.val = e (q z)
        simp
      map_one_left z := by
        apply Subtype.ext
        change (1 - (1 : Real)) • e (q z) + (1 : Real) • z.val = z.val
        simp }
  refine ⟨N, e, r, hr, hs, he, hi, ?_⟩
  refine ⟨{ toFun := j, invFun := q, left_inv := ?_, right_inv := ⟨H⟩ }, fun _ => rfl⟩
  have hqj : q.comp j = ContinuousMap.id M := by
    ext p
    exact hfix p
  rw [hqj]

end PoincareConjecture.Proofs.M02.Topology

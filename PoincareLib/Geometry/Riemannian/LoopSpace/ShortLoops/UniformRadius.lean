import PoincareLib.Geometry.Riemannian.LoopSpace.Length.Angular
import Mathlib.Topology.UniformSpace.Compact

/-!
# Uniform Riemannian neighborhoods of the diagonal

The compactness step in Morgan--Tian Lemma 18.27, printed p. 434, chooses
one radius for all short loops. Here an arbitrary neighborhood of the
diagonal receives a uniform radius in the explicitly specified metric.
Constructing a contraction on such a neighborhood remains a separate step.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.LoopSpace

/-- A diagonal neighborhood in a compact Riemannian manifold contains all
pairs with sufficiently small Riemannian distance. Source: the uniform-radius
step of MT Lemma 18.27, printed p. 434, in the local-contraction derivation. -/
theorem exists_uniform_riemannian_radius
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (hcompact : IsCompact (univ : Set M))
    {U : Set (M × M)} (hU : IsOpen U) (hdiag : ∀ p, (p, p) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ p q, g.edist p q < ENNReal.ofReal r → (p, q) ∈ U := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric (𝓡 n) M
  have hUnhds : U ∈ 𝓝ˢ (diagonal M) := hU.mem_nhdsSet.mpr (by
    rintro ⟨p, q⟩ hpq
    have hpq' : p = q := hpq
    subst q
    exact hdiag p)
  rw [nhdsSet_diagonal_eq_uniformity] at hUnhds
  obtain ⟨r, hr, hrU⟩ := uniformity_basis_edist_nnreal.mem_iff.mp hUnhds
  refine ⟨r, by exact_mod_cast hr, ?_⟩
  intro p q hpq
  apply hrU
  change g.edist p q < (r : ℝ≥0∞)
  simpa only [ENNReal.ofReal_coe_nnreal] using hpq

/-- One threshold places every short loop in any given diagonal
neighborhood. Source: MT Lemma 18.27, printed p. 434. -/
theorem exists_short_loop_diagonal_radius
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (hcompact : IsCompact (univ : Set M))
    {U : Set (M × M)} (hU : IsOpen U) (hdiag : ∀ p, (p, p) ∈ U) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ γ : C1FreeLoopSpace (M := M),
      freeLoopLength g γ < ζ → ∀ z : LoopCircle, (γ loopCircleBasepoint, γ z) ∈ U := by
  obtain ⟨r, hr, hrU⟩ := exists_uniform_riemannian_radius g hcompact hU hdiag
  refine ⟨r, hr, fun γ hγ z => hrU _ _ ?_⟩
  exact loop_mem_ball_of_length_lt g γ hr hγ z

end PoincareMT.LoopSpace

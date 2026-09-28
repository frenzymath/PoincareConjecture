import PoincareConjecture.Proofs.M47.TerminalGermsCompleteness
import PoincareConjecture.Proofs.M47.TerminalCurvaturePartialInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

theorem terminalCurvature_source_ball_captured
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [ConnectedSpace M]
    {N : ℕ → Type v} [∀ k, TopologicalSpace (N k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (N k)]
    [∀ k, IsManifold (𝓡 3) ∞ (N k)] [∀ k, T3Space (N k)]
    (g : RiemannianMetric 3 M) (h : ∀ k, RiemannianMetric 3 (N k))
    (E : ℕ → Set M) (hE : ∀ j, IsOpen (E j)) (hmono : Monotone E)
    (hcover : (⋃ j, E j) = univ) (p : M) (f : ∀ k, M → N k)
    (hsmooth : ∀ k, IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (f k) (E k))
    (hquad : ∀ K : Set M, IsCompact K → ∀ᶠ k in atTop,
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        (h k).inner (f k x) (mfderiv (𝓡 3) (𝓡 3) (f k) x v)
          (mfderiv (𝓡 3) (𝓡 3) (f k) x v) ≤ 4 * g.inner x v v)
    (hsource : ∀ A : ℝ, 0 < A → ∃ j, ∀ᶠ k in atTop,
      (h k).ball (f k p) A ⊆ f k '' E j)
    (x : M) {R : ℝ} (hR : 0 < R) :
    ∃ j, ∀ᶠ k in atTop, (h k).ball (f k x) R ⊆ f k '' E j := by
  have hd : g.edist p x ≠ ⊤ := by
    let : EMetricSpace M := g.toEMetricSpace
    exact Poincare.edist_ne_top_of_preconnected p x
  let A := (g.edist p x).toReal + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hx : x ∈ g.ball p A := by
    change g.edist p x < ENNReal.ofReal A
    rw [← ENNReal.ofReal_toReal hd]
    exact (ENNReal.ofReal_lt_ofReal_iff hA).mpr (by dsimp only [A]; linarith)
  have hxball := terminalGerms_eventually_mem_ball g h E hE hmono hcover f hsmooth hquad hx
  obtain ⟨j, hj⟩ := hsource (2 * A + R) (by positivity)
  refine ⟨j, ?_⟩
  filter_upwards [hxball, hj] with k hkx hk y hy
  apply hk
  change (h k).edist (f k p) y < ENNReal.ofReal (2 * A + R)
  have htri : (h k).edist (f k p) y ≤
      (h k).edist (f k p) (f k x) + (h k).edist (f k x) y := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N k → Type _) :=
      ⟨(h k).toRiemannianMetric⟩
    exact Manifold.riemannianEDist_triangle
  apply htri.trans_lt
  rw [ENNReal.ofReal_add (by positivity) hR.le]
  exact ENNReal.add_lt_add hkx hy

theorem terminalCurvature_inverse_image_compact
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M]
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    {V : Set M} (hV : V ⊆ phi.source) (hcompact : IsCompact (closure V))
    {B : Set N} (hB : B ⊆ phi '' V) :
    B ⊆ phi.target ∧ phi.symm '' B ⊆ V ∧ IsCompact (closure (phi.symm '' B)) := by
  have hinverse : phi.symm '' B ⊆ V := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hB hy
    change phi.toOpenPartialHomeomorph.symm (phi.toOpenPartialHomeomorph z) ∈ V
    rwa [phi.toOpenPartialHomeomorph.left_inv (hV hz)]
  refine ⟨?_, hinverse, hcompact.of_isClosed_subset isClosed_closure (closure_mono hinverse)⟩
  rintro y hy
  obtain ⟨z, hz, rfl⟩ := hB hy
  exact phi.map_source (hV hz)

theorem terminalCurvature_exists_captured_partial_inverse
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] [T2Space M] [Nonempty M]
    {f : M → N} {U V : Set M} (hU : IsOpen U)
    (hembed : Topology.IsOpenEmbedding (fun x : U => f x))
    (hsmooth : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f U)
    (hVU : V ⊆ U) (hcompact : IsCompact (closure V))
    {B : Set N} (hB : B ⊆ f '' V) :
    ∃ phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞,
      (phi : M → N) = f ∧ phi.source = U ∧ phi.target = f '' U ∧
      B ⊆ phi.target ∧ phi.symm '' B ⊆ V ∧ IsCompact (closure (phi.symm '' B)) := by
  obtain ⟨phi, hf, hsource, htarget⟩ :=
    terminalCurvature_exists_actual_partial_inverse hU hembed hsmooth
  refine ⟨phi, hf, hsource, htarget, ?_⟩
  exact terminalCurvature_inverse_image_compact phi
    (by simpa only [hsource] using hVU) hcompact (by simpa only [hf] using hB)

end PoincareConjecture.M47

import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity.ChartComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity.FrozenMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric

private theorem intrinsic_ball_basis
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {p : M} {V : Set M}
    (hV : V ∈ 𝓝 p) : ∃ c > (0 : ℝ≥0), {y | g.edist p y < c} ⊆ V := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  exact setOfPred_riemannianEDist_lt_subset_nhds (𝓡 n) hV

private theorem eventually_intrinsic_edist_lt
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) {c : ℝ≥0∞} (hc : 0 < c) :
    ∀ᶠ y in 𝓝 p, g.edist p y < c := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  exact eventually_riemannianEDist_lt (𝓡 n) p hc

theorem continuousOn_of_edist_eq
    {n m : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (h : RiemannianMetric m (EuclideanSpace ℝ (Fin m)))
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hdist : ∀ x ∈ U, ∀ y ∈ U, h.edist (f x) (f y) = g.edist x y) :
    ContinuousOn f U := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  apply tendsto_def.mpr
  intro V hV
  obtain ⟨c, hc, hsub⟩ := intrinsic_ball_basis h hV
  filter_upwards [hU.mem_nhds hp, eventually_intrinsic_edist_lt g p
    (show (0 : ℝ≥0∞) < c by exact_mod_cast hc)] with y hy hdy
  exact hsub (by simpa only [mem_ofPred_eq, hdist p hp y hy] using hdy)

private theorem exists_frozen_distance_comparison
    {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (p : EuclideanSpace ℝ (Fin n)) :
    ∃ A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
    ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, ∀ y ∈ U,
        g.edist x y ≤ 2 * EDist.edist (A x) (A y) ∧
        EDist.edist (A x) (A y) ≤ 2 * g.edist x y := by
  let e := OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n))
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiff_id.contMDiffOn
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiff_id.contMDiffOn
  obtain ⟨A, hA, _⟩ := g.exists_frozenPullbackEquiv (f := e) (x := p)
    (by
      change Function.Injective (mfderiv (𝓡 n) (𝓡 n) id p)
      rw [mfderiv_id]
      exact fun _ _ h => h)
  obtain ⟨U, hU, hp, _, hcomp⟩ := g.exists_open_distortion_of_tangentNorm_comparison
    e he hei (show p ∈ e.source from mem_univ _) A (K := 2) (by norm_num)
      (g.eventually_pullbackNorm_comparison contMDiffAt_id A hA (by norm_num))
  exact ⟨A, U, hU, hp, by simpa [e] using hcomp⟩

theorem exists_lipschitzOn_of_edist_eq
    {n m : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (h : RiemannianMetric m (EuclideanSpace ℝ (Fin m)))
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hdist : ∀ x ∈ U, ∀ y ∈ U, h.edist (f x) (f y) = g.edist x y)
    {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ U) :
    ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ ∃ C : ℝ≥0, LipschitzOnWith C f V := by
  obtain ⟨A, V, hV, hpV, hcomp⟩ := exists_frozen_distance_comparison g p
  obtain ⟨B, W, hW, hpW, hcomp'⟩ := exists_frozen_distance_comparison h (f p)
  have hN : U ∩ V ∩ f ⁻¹' W ∈ 𝓝 p := inter_mem
    (inter_mem (hU.mem_nhds hp) (hV.mem_nhds hpV))
    (((g.continuousOn_of_edist_eq h hU hdist).continuousAt (hU.mem_nhds hp)).preimage_mem_nhds
      (hW.mem_nhds hpW))
  obtain ⟨Z, hZN, hZ, hpZ⟩ := mem_nhds_iff.mp hN
  refine ⟨Z, hZ, hpZ, fun x hx => (hZN hx).1.1,
    ‖B.symm.toContinuousLinearMap‖₊ * 2 * 2 * ‖A.toContinuousLinearMap‖₊, ?_⟩
  intro x hx y hy
  have hx' := hZN hx
  have hy' := hZN hy
  calc
    EDist.edist (f x) (f y) ≤ (‖B.symm.toContinuousLinearMap‖₊ : ℝ≥0∞) *
        EDist.edist (B (f x)) (B (f y)) := by
      simpa using B.symm.toContinuousLinearMap.lipschitz (B (f x)) (B (f y))
    _ ≤ (‖B.symm.toContinuousLinearMap‖₊ : ℝ≥0∞) * (2 * g.edist x y) := by
      gcongr
      simpa only [hdist x hx'.1.1 y hy'.1.1] using (hcomp' _ hx'.2 _ hy'.2).2
    _ ≤ (‖B.symm.toContinuousLinearMap‖₊ : ℝ≥0∞) * (2 *
        (2 * ((‖A.toContinuousLinearMap‖₊ : ℝ≥0∞) * EDist.edist x y))) := by
      gcongr
      apply (hcomp x hx'.1.2 y hy'.1.2).1.trans
      gcongr
      exact A.toContinuousLinearMap.lipschitz x y
    _ = _ := by push_cast; ring

end PoincareConjecture.RiemannianMetric

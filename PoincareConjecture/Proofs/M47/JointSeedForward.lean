import PoincareConjecture.Proofs.M47.JointSeedWorldline

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

theorem jointSeed_forward_scalar_comparison
    {u : ℝ → ℝ} {a b A L : ℝ} (hab : a ≤ b) (hA : 0 ≤ A) (hL : 0 < L)
    (hu : ContinuousOn u (Icc a b)) (hinitial : u a ≤ L)
    (hderiv : ∀ w ∈ Ioo a b, L < u w →
      ∃ z : ℝ, HasDerivAt u z w ∧ |z| ≤ A * u w ^ 2)
    (hshort : A * L * (b - a) ≤ 1 / 4) :
    ∀ s ∈ Icc a b, u s ≤ 4 * L / 3 := by
  have hmap : MapsTo (fun s : ℝ => a + b - s) (Icc a b) (Icc a b) := by
    intro s hs
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hcont : ContinuousOn (fun s => u (a + b - s)) (Icc a b) :=
    hu.comp (continuous_const.sub continuous_id).continuousOn hmap
  have hbound := jointSeed_backward_scalar_comparison
    (u := fun s => u (a + b - s)) hab hA hL hcont
    (by simpa only [add_sub_cancel_right] using hinitial) (fun w hw hhigh => ?_) hshort
  · intro s hs
    have h := hbound (a + b - s) (hmap hs)
    simpa only [show a + b - (a + b - s) = s by ring] using h
  · obtain ⟨z, hz, hestimate⟩ := hderiv (a + b - w)
      ⟨by linarith [hw.2], by linarith [hw.1]⟩ hhigh
    refine ⟨-z, ?_, by simpa only [abs_neg] using hestimate⟩
    simpa only [zero_sub, mul_neg_one, Function.comp_def] using
      hz.comp w ((hasDerivAt_const w (a + b)).sub (hasDerivAt_id w))

theorem jointSeed_forward_of_evolution_bound
    (P : M47ScalarPersistencePredecessors.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {J : Set ℝ} (F : RicciFlow 3 M J) {a b A L : ℝ} (q : M)
    (hab : a ≤ b) (hJ : Icc a b ⊆ J) (hA : 0 ≤ A) (hL : 0 < L)
    (hinitial : (F.connection a).scalarCurvature q ≤ L)
    (hestimate : ∀ s ∈ Ioo a b, L < (F.connection s).scalarCurvature q →
      |(F.connection s).laplacian (F.connection s).scalarCurvature q +
          2 * (F.connection s).ricciNormSq q| ≤
        A * (F.connection s).scalarCurvature q ^ 2)
    (hshort : A * L * (b - a) ≤ 1 / 4) :
    ∀ s ∈ Icc a b, (F.connection s).scalarCurvature q ≤ 4 * L / 3 := by
  have hcont : ContinuousOn (fun s => (F.connection s).scalarCurvature q) (Icc a b) := by
    intro s hs
    exact (P.scalar_evolution M J F s (hJ hs) q).continuousWithinAt.mono hJ
  apply jointSeed_forward_scalar_comparison
    (u := fun s => (F.connection s).scalarCurvature q) (a := a) (b := b) (A := A) (L := L)
    hab hA hL hcont hinitial ?_ hshort
  intro s hs hhigh
  refine ⟨(F.connection s).laplacian (F.connection s).scalarCurvature q +
    2 * (F.connection s).ricciNormSq q, ?_, hestimate s hs hhigh⟩
  exact (P.scalar_evolution M J F s (hJ (Ioo_subset_Icc_self hs)) q).hasDerivAt
    (Filter.mem_of_superset (Icc_mem_nhds hs.1 hs.2) hJ)

end PoincareConjecture.M47

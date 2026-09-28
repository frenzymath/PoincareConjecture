import PoincareConjecture.Proofs.M09.ScalarTimeDerivative
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_GuardedScalar

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem ordinary_backward_scalar_le_four_inv_sq
    (hM04 : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow n M J) {T duration B r : ℝ}
    (hB : 0 < B) (hr : 0 < r)
    (hwindow : Icc (T - duration) T ⊆ J) (x : M)
    (hterminal : (F.connection T).scalarCurvature x ≤ 2 * r⁻¹ ^ 2)
    (hrate : ∀ t ∈ Icc (T - duration) T,
      r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x →
      |(F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x| ≤
          B * (F.connection t).scalarCurvature x ^ 2)
    (hshort : 16 * B * r⁻¹ ^ 2 * duration ≤ 1) :
    ∀ t ∈ Icc (T - duration) T,
      (F.connection t).scalarCurvature x ≤ 4 * r⁻¹ ^ 2 := by
  let f (s : ℝ) := (F.connection (T - s)).scalarCurvature x
  let d (s : ℝ) := -((F.connection (T - s)).laplacian
    (F.connection (T - s)).scalarCurvature x +
      2 * (F.connection (T - s)).ricciNormSq x)
  have hderivative (s : ℝ) (hs : s ∈ Icc 0 duration) :
      HasDerivWithinAt f (d s) (Icc 0 duration) s :=
    M09.backward_scalar_hasDerivWithinAt hM04 hwindow le_rfl hs x
  have hcont : ContinuousOn f (Icc 0 duration) := fun s hs =>
    (hderivative s hs).continuousWithinAt
  have hright (s : ℝ) (hs : s ∈ Ico 0 duration) :
      HasDerivWithinAt f (d s) (Ici s) s := by
    apply (hderivative s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE hs.2)
      (fun y hy => ⟨hs.1.trans hy.1, hy.2⟩)
  have hguard (s : ℝ) (hs : s ∈ Ico 0 duration)
      (hhigh : r⁻¹ ^ 2 ≤ f s) : d s ≤ B * f s ^ 2 := by
    exact (neg_le_abs _).trans (hrate (T - s)
      ⟨sub_le_sub_left hs.2.le T, sub_le_self T hs.1⟩ hhigh)
  have hzero : f 0 = (F.connection T).scalarCurvature x :=
    congrArg (fun t => (F.connection t).scalarCurvature x) (sub_zero T)
  have hbound := le_four_inv_sq_of_deriv_le_sq_above hB hr hcont hright
    (hzero.symm ▸ hterminal) hguard
    (by simpa only [sub_zero] using hshort)
  intro t ht
  have hmem : T - t ∈ Icc 0 duration := ⟨sub_nonneg.mpr ht.2, by linarith [ht.1]⟩
  have hvalue : f (T - t) = (F.connection t).scalarCurvature x :=
    congrArg (fun s => (F.connection s).scalarCurvature x) (sub_sub_cancel T t)
  exact hvalue ▸ hbound (T - t) hmem

end PoincareConjecture.Proofs.M46

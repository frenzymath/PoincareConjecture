import PoincareConjecture.Proofs.M63.Adapters
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.SmoothRelabeling










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem intrinsic_regularity_on_shorter_smooth_slab
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    {S T : ℝ} (haS : a < S) (hST : S < T) (hTb : T ≤ b)
    (hc : M63SmoothShrinkingCurveOn F c (Icc a T)) :
    M63IntrinsicRegularityOn F c (Icc a S) := by
  have haT : a < T := haS.trans hST
  have hsub : Icc a T ⊆ Icc a b := fun _ ht => ⟨ht.1, ht.2.trans hTb⟩
  let F' := m63RestrictClosedFlow F a T hsub haT
  have hc' : M62ShrinkingCurve F' c := m63SmoothRestriction hc a T Subset.rfl haT
  have hjet (i : ℕ) : m63CurvatureJet F' c i = m63CurvatureJet F c i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      funext t x
      simp only [m63CurvatureJet, ih]
      rfl
  have hj (i : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z : ℝ × ℝ =>
        (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a T) := by
    simpa only [hjet] using curvatureJet_joint_contMDiff F' c hc' i
  refine ⟨?_, ?_⟩
  · intro i
    rw [interior_Icc]
    exact ((hj i).of_le (by simp)).mono
      (fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans hST⟩)
  · intro s R has _hsR hinside i
    apply (hj i).continuousOn.mono
    intro z hz
    exact ⟨hz.1, has.trans_le hz.2.1, (hinside hz.2).2.trans_lt hST⟩

end PoincareConjecture.M63

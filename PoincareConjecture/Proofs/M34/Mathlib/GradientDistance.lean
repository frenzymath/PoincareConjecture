import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.LocalDistance










set_option autoImplicit false

open Set Manifold
open scoped Manifold ContDiff Bundle ENNReal

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option backward.isDefEq.respectTransparency false in



theorem edist_le_riemannianEDist_of_mfderiv_le_one {f : M → F}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f)
    (hbound : ∀ z, ‖mfderiv I 𝓘(ℝ, F) f z‖ₑ ≤ 1) (x y : M) :
    edist (f x) (f y) ≤ riemannianEDist I x y := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlength⟩ := exists_lt_of_riemannianEDist_lt hb
  have h := edist_le_mul_pathELength_of_mfderiv_le
    (s := univ) (K := 1) (fun z _ => hf.contMDiffAt)
    (fun z _ => hbound z) hγsmooth (mapsTo_univ _ _)
  simp only [hγ0, hγ1, ENNReal.coe_one, one_mul] at h
  exact h.trans hγlength.le

end Poincare

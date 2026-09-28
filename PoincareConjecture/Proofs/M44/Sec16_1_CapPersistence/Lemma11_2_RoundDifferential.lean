import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundPullback
import PoincareConjecture.Proofs.M36.RetainedDifferential










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)




theorem round_forward_mfderiv_isInvertible {X : Type*} [TopologicalSpace X]
    [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 X} {epsilon : ℝ} (R : SingularRoundComponent g epsilon)
    (p : R.model.carrier) : (mfderiv (𝓡 3) (𝓡 3) R.forward p).IsInvertible := by
  have hopen : IsOpen R.carrier := R.forward_image ▸ R.forward_openEmbedding.isOpen_range
  have hp : R.forward p ∈ R.carrier := R.forward_image ▸ mem_range_self p
  have hforward := (R.forward_smooth p).mdifferentiableAt (by simp)
  have hinverse := (R.inverse_smooth.contMDiffAt (hopen.mem_nhds hp)).mdifferentiableAt (by simp)
  have hinj := M36.mfderiv_injective_of_local_leftInverse hforward hinverse
    (Filter.Eventually.of_forall R.left_inverse)
  let L : E →L[ℝ] E := mfderiv (𝓡 3) (𝓡 3) R.forward p
  have hbij : Function.Bijective L := ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L.toLinearMap) rfl).mp hinj⟩
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2), rfl⟩




theorem round_composition_mfderiv_isInvertible {X : Type*} [TopologicalSpace X]
    [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 X} {epsilon : ℝ} (R : SingularRoundComponent g epsilon)
    {e : E → R.model.carrier} {x : E} (he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e x)
    (hinv : (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible) :
    (mfderiv (𝓡 3) (𝓡 3) (R.forward ∘ e) x).IsInvertible := by
  rw [mfderiv_comp x ((R.forward_smooth (e x)).mdifferentiableAt (by simp))
    (he.mdifferentiableAt (by simp))]
  obtain ⟨L, hL⟩ := hinv
  obtain ⟨J, hJ⟩ := round_forward_mfderiv_isInvertible R (e x)
  exact ⟨L.trans J, by rw [← hL, ← hJ]; rfl⟩

end PoincareConjecture.M44

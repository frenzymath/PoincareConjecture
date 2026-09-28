import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic










open Module

namespace PoincareConjecture.Synge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem det_adjoint (f : E →ₗ[ℝ] E) : f.adjoint.det = f.det := by
  let b := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
    Matrix.det_conjTranspose]
  simp [LinearMap.det_toMatrix]


theorem exists_ne_zero_fixed_of_even_det_neg_one (f : E ≃ₗᵢ[ℝ] E)
    (hdim : Even (finrank ℝ E)) (hdet : f.toLinearMap.det = -1) :
    ∃ v : E, v ≠ 0 ∧ f v = v := by
  let A := f.toLinearMap
  have horth : A.adjoint ∘ₗ A = LinearMap.id :=
    f.toLinearIsometry.adjoint_comp_self'
  have hid : A.adjoint ∘ₗ (A - LinearMap.id) =
      -(A - LinearMap.id).adjoint := by
    rw [LinearMap.comp_sub, horth, LinearMap.comp_id, map_sub,
      LinearMap.adjoint_id]
    exact (neg_sub _ _).symm
  have heq := congrArg LinearMap.det hid
  rw [LinearMap.det_comp, det_adjoint, hdet] at heq
  have hneg : (-(A - LinearMap.id).adjoint).det = (A - LinearMap.id).det := by
    rw [← neg_one_smul ℝ, LinearMap.det_smul, hdim.neg_one_pow, one_mul,
      det_adjoint]
  rw [hneg] at heq
  have hz : (A - LinearMap.id).det = 0 := by linarith
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz)
  refine ⟨v, hv0, ?_⟩
  change A v = v
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] using hv


theorem exists_ne_zero_fixed_of_finrank_two_det_neg_one (f : E ≃ₗᵢ[ℝ] E)
    (hdim : finrank ℝ E = 2) (hdet : f.toLinearMap.det = -1) :
    ∃ v : E, v ≠ 0 ∧ f v = v :=
  exists_ne_zero_fixed_of_even_det_neg_one f (hdim ▸ by decide) hdet




theorem exists_ne_zero_orthogonal_fixed_of_finrank_three_det_neg_one
    (f : E ≃ₗᵢ[ℝ] E) (hdim : finrank ℝ E = 3)
    (hdet : f.toLinearMap.det = -1) {v : E} (hv : v ≠ 0) (hfv : f v = v) :
    ∃ w : E, w ≠ 0 ∧ inner ℝ v w = 0 ∧ f w = w := by
  let K : Submodule ℝ E := ℝ ∙ v
  have hK : ∀ x : K, f x = x := by
    intro x
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.property
    rw [← ha, map_smul, hfv]
  have hnormal : Kᗮ ≤ Kᗮ.comap f.toLinearMap := by
    intro x hx
    change f x ∈ Kᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hx ⊢
    rw [← hfv, f.inner_map_map]
    exact hx
  let g : Kᗮ →ₗᵢ[ℝ] Kᗮ :=
    { f.toLinearMap.restrict hnormal with norm_map' x := f.norm_map x }
  let gEquiv : Kᗮ ≃ₗᵢ[ℝ] Kᗮ := LinearIsometryEquiv.ofSurjective g
    (LinearMap.injective_iff_surjective.mp g.injective)
  let e : (K × Kᗮ) ≃ₗ[ℝ] E := K.prodEquivOfIsCompl Kᗮ K.isCompl_orthogonal
  have hconj : e.symm.toLinearMap ∘ₗ f.toLinearMap ∘ₗ e.toLinearMap =
      (LinearMap.id : K →ₗ[ℝ] K).prodMap g.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply e.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    change f ((x.1 : E) + (x.2 : E)) = (x.1 : E) + f (x.2 : E)
    rw [map_add, hK]
  have hgdet : gEquiv.toLinearMap.det = -1 := by
    have he := LinearMap.det_conj f.toLinearMap e.symm
    rw [LinearEquiv.symm_symm, hconj, LinearMap.det_prodMap, LinearMap.det_id,
      one_mul] at he
    exact he.trans hdet
  have hnormaldim : finrank ℝ Kᗮ = 2 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal K
    rw [show finrank ℝ K = 1 from finrank_span_singleton hv, hdim] at hsum
    omega
  obtain ⟨w, hw, hgw⟩ :=
    exists_ne_zero_fixed_of_finrank_two_det_neg_one gEquiv hnormaldim hgdet
  refine ⟨w, ?_, ?_, ?_⟩
  · exact fun h => hw (Subtype.ext h)
  · exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
  · exact congrArg Subtype.val hgw

end PoincareConjecture.Synge

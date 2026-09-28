import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryInverseLift













set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff NNReal

namespace PoincareConjecture.M64Uniformization

private theorem lipschitz_of_C1_shift {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {p : ℝ} (hp : 0 < p) (hshift : ∀ x, f (x + p) = f x + p) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  have hperiod : Function.Periodic (deriv f) p := by
    intro x
    have hfun : (fun y => f (y + p)) = fun y => f y + p := funext hshift
    have h := ((hf.differentiable (by norm_num) (x + p)).hasDerivAt.comp x
      ((hasDerivAt_id x).add_const p))
    have h' := (hf.differentiable (by norm_num) x).hasDerivAt.add_const p
    change HasDerivAt (fun y => f (y + p)) _ x at h
    rw [hfun] at h
    simpa only [mul_one] using h.unique h'
  obtain ⟨C, hC⟩ := (hperiod.compact_of_continuous hp.ne'
    (hf.continuous_deriv (by norm_num))).exists_bound_of_continuousOn continuousOn_id
  let K : ℝ≥0 := ⟨max 0 C, le_max_left _ _⟩
  refine ⟨K, lipschitzWith_of_nnnorm_deriv_le (hf.differentiable (by norm_num)) ?_⟩
  intro x
  change ‖deriv f x‖ ≤ max 0 C
  exact (hC _ ⟨x, rfl⟩).trans (le_max_right _ _)





theorem exists_positive_degree_one_homeomorph
    {f d : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (d x) x) (hdc : Continuous d)
    (hdpos : ∀ x, 0 < d x) {p : ℝ} (hp : 0 < p)
    (hshift : ∀ x, f (x + p) = f x + p) :
    ∃ phi : ℝ ≃ₜ ℝ,
      (phi : ℝ → ℝ) = f ∧ StrictMono phi ∧ StrictMono phi.symm ∧
      ContDiff ℝ 1 (phi : ℝ → ℝ) ∧ ContDiff ℝ 1 (phi.symm : ℝ → ℝ) ∧
      (∀ x, phi (x + p) = phi x + p) ∧
      (∀ y, phi.symm (y + p) = phi.symm y + p) ∧
      (∀ y, HasDerivAt phi.symm (d (phi.symm y))⁻¹ y) ∧
      ∃ K L : ℝ≥0, LipschitzWith K phi ∧ LipschitzWith L phi.symm := by
  have hderiv : deriv f = d := funext (fun x => (hd x).deriv)
  have hf : ContDiff ℝ 1 f := contDiff_one_iff_deriv.mpr
    ⟨fun x => (hd x).differentiableAt, hderiv ▸ hdc⟩
  have hmono : StrictMono f := strictMono_of_hasDerivAt_pos hd hdpos
  have hperiod : Function.Periodic (fun x => f x - x) p := by
    intro x
    change f (x + p) - (x + p) = f x - x
    rw [hshift]
    ring
  obtain ⟨C, hC⟩ := (hperiod.compact_of_continuous hp.ne'
    (hf.continuous.sub continuous_id)).exists_bound_of_continuousOn continuousOn_id
  have hbound (x : ℝ) : |f x - x| ≤ C := hC _ ⟨x, rfl⟩
  have htop : Tendsto f atTop atTop := by
    apply tendsto_atTop_mono (f := fun x : ℝ => x - C) (fun x => ?_)
      (by simpa only [sub_eq_add_neg, id_eq] using
        tendsto_atTop_add_const_right atTop (-C) tendsto_id)
    have h := (abs_le.mp (hbound x)).1
    linarith
  have hbot : Tendsto f atBot atBot := by
    apply tendsto_atBot_mono (f := fun x : ℝ => x + C) (fun x => ?_)
      (tendsto_atBot_add_const_right atBot C tendsto_id)
    have h := (abs_le.mp (hbound x)).2
    linarith
  have hsurj : Function.Surjective f := hf.continuous.surjective htop hbot
  let orderIso := StrictMono.orderIsoOfSurjective f hmono hsurj
  let phi : ℝ ≃ₜ ℝ := orderIso.toHomeomorph
  have hphi (x : ℝ) : HasDerivAt phi (d x) x := hd x
  have hphis : ContDiff ℝ 1 (phi : ℝ → ℝ) := hf
  have hphii : ContDiff ℝ 1 (phi.symm : ℝ → ℝ) :=
    phi.contDiff_symm_deriv (fun x => (hdpos x).ne') hphi hphis
  have hinvshift (y : ℝ) : phi.symm (y + p) = phi.symm y + p := by
    apply phi.injective
    rw [phi.apply_symm_apply]
    change y + p = f (phi.symm y + p)
    rw [hshift]
    exact congrArg (fun z : ℝ => z + p) (phi.apply_symm_apply y).symm
  obtain ⟨K, hK⟩ := lipschitz_of_C1_shift hphis hp hshift
  obtain ⟨L, hL⟩ := lipschitz_of_C1_shift hphii hp hinvshift
  refine ⟨phi, rfl, orderIso.strictMono, orderIso.symm.strictMono, hphis, hphii,
    hshift, hinvshift, ?_, K, L, hK, hL⟩
  intro y
  exact (hphi (phi.symm y)).of_local_left_inverse phi.symm.continuous.continuousAt
    (hdpos _).ne' (Eventually.of_forall phi.apply_symm_apply)

end PoincareConjecture.M64Uniformization

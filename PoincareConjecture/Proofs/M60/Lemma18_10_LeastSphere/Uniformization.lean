import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationPuncturedMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

noncomputable section

namespace PoincareConjecture.M60

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem sphere_uniformization (q : RiemannianMetric 2 UnitTwoSphere) :
    ∃ phi : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere, M60WeaklyConformal q phi := by
  obtain ⟨F, c, -, hcp, hmetric⟩ := exists_punctured_conformal_developing_map q
  obtain ⟨H, hHp, hH, hHs, hHi⟩ := exists_sphere_compactification F.symm
  have hs (p : UnitTwoSphere) (hp : p ≠ m60SpherePole) :
      ContMDiffAt (𝓡 2) (𝓡 2) ∞ H p := hHs.contMDiffAt (isOpen_compl_singleton.mem_nhds hp)
  have hi (p : UnitTwoSphere) (hp : p ≠ H m60SpherePole) :
      ContMDiffAt (𝓡 2) (𝓡 2) ∞ H.symm p :=
    hHi.contMDiffAt (isOpen_compl_singleton.mem_nhds (hHp ▸ hp))
  have hc (p : UnitTwoSphere) (hp : p ≠ m60SpherePole) : ∃ s : ℝ, 0 < s ∧ ∀ v w,
      q.inner (H p) (mfderiv (𝓡 2) (𝓡 2) H p v) (mfderiv (𝓡 2) (𝓡 2) H p w) =
        s * m60RoundSphereMetric.inner p v w := by
    have hps : p ∈ m60SphereChart.source := by simpa [m60SphereChart] using hp
    obtain ⟨z, rfl⟩ : ∃ z, m60SphereParameter z = p :=
      ⟨m60SphereChart p, m60SphereChart.left_inv hps⟩
    have hEq : (H : _ → _) ∘ m60SphereParameter = m60SphereParameter ∘ F.symm := funext hH
    have hd := mfderiv_comp z ((hs _ hp).mdifferentiableAt (by simp))
      (m60SphereParameter_contMDiff.mdifferentiable (by simp) _)
    rw [hEq, mfderiv_comp z (m60SphereParameter_contMDiff.mdifferentiable (by simp) _)
        (F.symm.contMDiff.mdifferentiable (by simp) _), mfderiv_eq_fderiv] at hd
    have hchain (v : Plane) := congrArg (fun L => L v) hd.symm
    have hFi := fderiv_comp z
      ((contMDiff_iff_contDiff.mp F.contMDiff).differentiable (by simp) _)
      ((contMDiff_iff_contDiff.mp F.symm.contMDiff).differentiable (by simp) _)
    rw [show (F : _ → _) ∘ F.symm = id from funext F.apply_symm_apply,
      fderiv_id] at hFi
    have hFinv (v : Plane) : fderiv ℝ F (F.symm z) (fderiv ℝ F.symm z v) = v := by
      simpa only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using congrArg (fun L => L v) hFi.symm
    let t : ℝ := 16 / (‖z‖ ^ 2 + 4) ^ 2
    have ht : 0 < t := by dsimp [t]; positivity
    refine ⟨c (F.symm z) / t, div_pos (hcp _) ht, ?_⟩
    intro v w
    obtain ⟨v, rfl⟩ := (m60SphereParameter_mfderiv_isInvertible z).surjective v
    obtain ⟨w, rfl⟩ := (m60SphereParameter_mfderiv_isInvertible z).surjective w
    have hm := hmetric (F.symm z) (fderiv ℝ F.symm z v) (fderiv ℝ F.symm z w)
    rw [hFinv v, hFinv w] at hm
    erw [hH z, hchain v, hchain w]
    change q.pullbackCoefficients m60SphereParameter (F.symm z)
      (fderiv ℝ F.symm z v) (fderiv ℝ F.symm z w) = _
    rw [hm, m60RoundSphereMetric_inner, m60SphereParameter_inner]
    change _ = (c (F.symm z) / t) * (t * inner ℝ v w)
    rw [← mul_assoc, div_mul_cancel₀ _ ht.ne']
  obtain ⟨phi, hphi⟩ := diffeomorph_of_conformal_sphere_puncture
    m60RoundSphereMetric q H m60SpherePole hs hi hc
  refine ⟨phi, m60WeaklyConformal_of_compl_singleton q phi phi.contMDiff m60SpherePole ?_⟩
  intro p hp
  obtain ⟨s, hsp, hsm⟩ := hc p hp
  refine ⟨s, hsp.le, ?_⟩
  rw [hphi]
  simpa only [m60RoundSphereMetric_inner] using hsm
end PoincareConjecture.M60

end

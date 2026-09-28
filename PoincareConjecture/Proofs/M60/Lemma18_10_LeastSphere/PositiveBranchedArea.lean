import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Integrability
import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.GramRank










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem m60SphereParameter_injective : Function.Injective m60SphereParameter := by
  have ht : m60SphereChart.target = univ := by simp [m60SphereChart]
  intro z w hzw
  exact m60SphereChart.symm.injOn
    (by change z ∈ m60SphereChart.target; rw [ht]; trivial)
    (by change w ∈ m60SphereChart.target; rw [ht]; trivial) hzw




theorem m60SphereParameter_mfderiv_injective (z : LoopPlane) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z) := by
  intro v w hvw
  change LoopPlane at v w
  have hd : mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have h := m60SphereParameter_inner z (v - w) (v - w)
  rw [hd] at h
  have hc : (16 : ℝ) / (‖z‖ ^ 2 + 4) ^ 2 ≠ 0 := by positivity
  have hi : inner ℝ (v - w) (v - w) = 0 := by
    have hzero : m60RoundSphereInner (m60SphereParameter z) 0 0 = 0 := by
      simp only [m60RoundSphereInner, map_zero]
      change inner ℝ (0 : LoopAmbient) 0 = 0
      simp
    rw [hzero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  have hsub : (v - w : LoopPlane) = 0 := inner_self_eq_zero.mp hi
  change @Eq LoopPlane v w
  exact sub_eq_zero.mp hsub

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m60AreaDensity_pos_of_mfderiv_injective (g : RiemannianMetric n M)
    (F : LoopPlane → M) (z : LoopPlane)
    (hF : Function.Injective (mfderiv (𝓡 2) (𝓡 n) F z)) :
    0 < m60AreaDensity g F z := by
  have hli := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.linearIndependent.map'
    (mfderiv (𝓡 2) (𝓡 n) F z).toLinearMap (LinearMap.ker_eq_bot.mpr hF)
  have hne := (m60AreaGram_det_ne_zero_iff g F z).mpr hli
  have hpos := lt_of_le_of_ne (m60AreaGram_det_nonneg g F z) (Ne.symm hne)
  exact Real.sqrt_pos.mpr (lt_max_of_lt_right hpos)



theorem m60SphereArea_pos_of_finite_branch_set [T2Space M] [SecondCountableTopology M]
    (g : RiemannianMetric n M) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (hfinite : (m60SphereBranchSet (n := n) f).Finite)
    (himm : ∀ p : UnitTwoSphere, p ∉ m60SphereBranchSet (n := n) f →
      Function.Injective (mfderiv (𝓡 2) (𝓡 n) f p)) :
    0 < m60SphereArea g f := by
  have hpre : (m60SphereParameter ⁻¹' m60SphereBranchSet (n := n) f).Finite :=
    hfinite.preimage m60SphereParameter_injective.injOn
  obtain ⟨z, hz⟩ := hpre.exists_notMem
  have hinj : Function.Injective (mfderiv (𝓡 2) (𝓡 n) (f ∘ m60SphereParameter) z) := by
    rw [mfderiv_comp z (hf.mdifferentiable (by simp) _)
      (m60SphereParameter_contMDiff.mdifferentiable (by simp) _)]
    exact (himm _ hz).comp (m60SphereParameter_mfderiv_injective z)
  have hpos := m60AreaDensity_pos_of_mfderiv_injective g (f ∘ m60SphereParameter) z hinj
  exact integral_pos_of_integrable_nonneg_nonzero
    (m60AreaDensity_continuous g (hf.comp (m60SphereParameter_contMDiff.of_le (by simp))))
    (m60SphereAreaDensity_integrable g f hf)
    (m60AreaDensity_nonneg g (f ∘ m60SphereParameter)) hpos.ne'



theorem m60BranchedMinimalSphere_area_pos [T2Space M] [SecondCountableTopology M]
    {g : RiemannianMetric n M} {f : UnitTwoSphere → M} (hf : M60BranchedMinimalSphere g f) :
    0 < m60SphereArea g f :=
  m60SphereArea_pos_of_finite_branch_set g f (hf.smooth.of_le (by simp))
    hf.finite_branch_set hf.injective_off_branch_set

end PoincareConjecture

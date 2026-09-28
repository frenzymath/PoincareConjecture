import PoincareConjecture.Proofs.M47.CanonicalNeckRotationalTip
import PoincareConjecture.Definitions.M44CapPersistence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M47



theorem source_rotational_tip_ricci_eq_scalar
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x v w : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x w) = g.inner x v w)
    (v : StandardCapSpace) :
    D.ricci 0 v v = (D.scalarCurvature 0 / 3) * g.inner 0 v v := by
  let b := g.orthonormalBasis 0
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) (0 : StandardCapSpace)) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    exact finrank_euclideanSpace_fin
  have hunit (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) (0 : StandardCapSpace)))) :
      g.inner 0 (b i) (b i) = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one]
    norm_num
  have htrace : 3 * D.ricci 0 v v = D.scalarCurvature 0 * g.inner 0 v v := by
    calc
      _ = ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3)
          (0 : StandardCapSpace))), D.ricci 0 v v := by simp [hdim]
      _ = ∑ i, D.ricci 0 (b i) (b i) * g.inner 0 v v := by
        apply Finset.sum_congr rfl
        intro i _
        have h := Proofs.M47.rotational_tip_ricci_isotropic D hrotation v (b i)
        simpa only [hunit, mul_one] using h
      _ = _ := by rw [← Finset.sum_mul]; rfl
  linarith only [htrace]



theorem exists_source_standard_tip_ricci_lower {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ Ico 0 P.standard_cap.flow.base.lifetime,
      ∀ v : StandardCapSpace,
        (c / 3) * (P.standard_cap.flow.metric s).inner 0 v v ≤
          (P.standard_cap.flow.connection s).ricci 0 v v := by
  obtain ⟨c, hc, hrate⟩ := (Classical.choice P.standard_cap_uniqueness).scalar_lower_bound
  refine ⟨c, hc, ?_⟩
  intro s hs v
  have hsOne : s < 1 := by simpa only [P.standard_cap.lifetime_one] using hs.2
  have hdenom : 0 < 1 - s := sub_pos.mpr hsOne
  have hfloor : c ≤ c / (1 - s) := by
    apply (le_div_iff₀ hdenom).mpr
    nlinarith only [mul_nonneg hc.le hs.1]
  have hscalar := hfloor.trans (hrate s hs 0)
  have hmetric : 0 ≤ (P.standard_cap.flow.metric s).inner 0 v v := by
    by_cases hv : v = 0
    · simp only [hv, map_zero, le_refl]
    · exact ((P.standard_cap.flow.metric s).pos 0 v hv).le
  rw [source_rotational_tip_ricci_eq_scalar (P.standard_cap.flow.connection s)
    (P.standard_cap.rotation_invariant s hs)]
  exact mul_le_mul_of_nonneg_right (by linarith only [hscalar]) hmetric

end PoincareConjecture.M47

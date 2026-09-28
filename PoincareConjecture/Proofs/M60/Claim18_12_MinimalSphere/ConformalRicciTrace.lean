import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.StereographicConformal
import PoincareConjecture.Proofs.M60.Claim18_13_FixedMap.RicciQuadratic









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem m60AreaGram_eq_diagonal_of_weaklyConformal (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (hc : M60WeaklyConformal g f) (z : LoopPlane) :
    m60AreaGram g (f ∘ m60SphereParameter) z =
      Matrix.diagonal (fun _ : Fin 2 => m60SphereAreaDensity g f z) := by
  obtain ⟨s, -, hs⟩ := m60AreaGram_of_weaklyConformal g f hf hc z
  have harea : m60SphereAreaDensity g f z = s * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
    rw [m60SphereDensity_eq_of_weaklyConformal g f hf hc]
    unfold m60SphereEnergyDensity m60EnergyDensity
    rw [Matrix.trace_fin_two, hs, hs]
    simp only [real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow, mul_one]
    ring
  ext i j
  rw [hs, Matrix.diagonal_apply, harea]
  fin_cases i <;> fin_cases j <;>
    simp [EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]



theorem m60SphereRicciTraceDensity_eq_of_weaklyConformal
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (hc : M60WeaklyConformal g f)
    (z : LoopPlane) :
    m60SphereRicciTraceDensity D f z =
      ∑ i : Fin 2, D.ricci ((f ∘ m60SphereParameter) z)
        (mfderiv (𝓡 2) (𝓡 n) (f ∘ m60SphereParameter) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 n) (f ∘ m60SphereParameter) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  let a := m60SphereAreaDensity g f z
  let v := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 n) (f ∘ m60SphereParameter) z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hg := m60AreaGram_eq_diagonal_of_weaklyConformal g f hf hc z
  by_cases ha : a = 0
  · have hv (i : Fin 2) : v i = 0 := by
      have h := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G i i) hg
      simp only [Matrix.diagonal_apply_eq] at h
      change g.inner _ (v i) (v i) = a at h
      by_contra hi
      have hp := g.pos _ (v i) hi
      rw [h, ha] at hp
      exact lt_irrefl 0 hp
    obtain ⟨B, hB⟩ := m60Ricci_exists_bilinear D hD ((f ∘ m60SphereParameter) z)
    change m60SphereRicciTraceDensity D f z = ∑ i : Fin 2, D.ricci _ (v i) (v i)
    simp only [← hB, hv, map_zero, Finset.sum_const_zero]
    have hz : Matrix.det (m60AreaGram g (f ∘ m60SphereParameter) z) = 0 := by
      rw [hg, Matrix.det_diagonal]
      change (∏ _ : Fin 2, a) = 0
      simp [ha]
    simp only [m60SphereRicciTraceDensity, hz, if_true]
  · have hdet : Matrix.det (m60AreaGram g (f ∘ m60SphereParameter) z) ≠ 0 := by
      rw [hg, Matrix.det_diagonal]
      change (∏ _ : Fin 2, a) ≠ 0
      simpa only [Fin.prod_univ_two] using mul_ne_zero ha ha
    have hunit : IsUnit (fun _ : Fin 2 => a) :=
      ⟨⟨fun _ => a, fun _ => a⁻¹, by ext; simp [ha], by ext; simp [ha]⟩, rfl⟩
    have hcancel (i : Fin 2) : Ring.inverse (fun _ : Fin 2 => a) i * a = 1 :=
      congrFun (Ring.inverse_mul_cancel _ hunit) i
    unfold m60SphereRicciTraceDensity
    rw [if_neg hdet, hg, Matrix.inv_diagonal]
    change (∑ i : Fin 2, ∑ j : Fin 2,
      (Matrix.diagonal (Ring.inverse (fun _ : Fin 2 => a))) i j *
        D.ricci _ (v j) (v i)) * a = ∑ i : Fin 2, D.ricci _ (v i) (v i)
    simp only [Matrix.diagonal_apply]
    simp only [Fin.sum_univ_two]
    norm_num
    calc
      _ = (Ring.inverse (fun _ : Fin 2 => a) 0 * a) * D.ricci _ (v 0) (v 0) +
          (Ring.inverse (fun _ : Fin 2 => a) 1 * a) * D.ricci _ (v 1) (v 1) := by ring
      _ = _ := by rw [hcancel, hcancel]; simp

end PoincareConjecture

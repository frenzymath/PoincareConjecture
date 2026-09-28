import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Trace







noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M]
  {g : RiemannianMetric (m + 1) M}



theorem two_mul_ricci_unit_le_scalarCurvature_add
    (D : LeviCivitaData g) (x : M) (K : ℝ) (hK : 0 ≤ K)
    (hsec : ∀ v w : TangentSpace (𝓡 (m + 1)) x,
      -K ≤ D.sectionalCurvature x v w)
    (N : TangentSpace (𝓡 (m + 1)) x) (hN : g.inner x N N = 1) :
    2 * D.ricci x N N ≤ D.scalarCurvature x + (m : ℝ) ^ 2 * K := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 (m + 1)) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin (m + 1)))
      (TangentSpace (𝓡 (m + 1))) x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 (m + 1)) x) =
      Fintype.card (Option (Fin m)) := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin (m + 1))),
      finrank_euclideanSpace]
    simp
  have hsingle : Orthonormal ℝ
      (({none} : Set (Option (Fin m))).domRestrict (fun _ => N)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := by
      apply Subtype.ext
      have hi : i.val = none := Set.mem_singleton_iff.mp i.property
      have hj : j.val = none := Set.mem_singleton_iff.mp j.property
      exact hi.trans hj.symm
    subst j
    simp only
    exact hN
  obtain ⟨B, hB⟩ := hsingle.exists_orthonormalBasis_extension_of_card_eq hdim
  have hB0 : B none = N := hB none (by simp)
  have hzero : D.curvatureTensor x N N N N = 0 := by
    have hz := D.curvatureTensor_swap_first x N N N N
    linarith
  have hricci : D.ricci x N N =
      ∑ i : Fin m, D.curvatureTensor x N (B (some i)) N (B (some i)) := by
    have ht := bilinear_sum_orthonormalBasis_eq
      (D.curvatureTensor_bilinear_first_third x N N) (g.orthonormalBasis x) B
    simp only [curvatureTensor_bilinear_first_third_apply] at ht
    simp_rw [← D.curvatureTensor_diagonal_pair_swap x N] at ht
    simpa only [ricci, Fintype.sum_option, hB0, hzero, zero_add] using ht
  have htrace :
      (∑ i : Fin m, ∑ j : Fin m,
        D.curvatureTensor x (B (some i)) (B (some j))
          (B (some i)) (B (some j))) =
        D.scalarCurvature x - 2 * D.ricci x N N := by
    have hs := D.scalarCurvature_eq_sum_orthonormalBasis x B
    simp only [Fintype.sum_option, hB0, hzero, zero_add,
      Finset.sum_add_distrib] at hs
    simp_rw [← D.curvatureTensor_diagonal_pair_swap x N] at hs
    rw [← hricci] at hs
    linarith
  have hinner (i j : Option (Fin m)) :
      g.inner x (B i) (B j) = if i = j then 1 else 0 := B.inner_eq_ite i j
  have hterm (i j : Fin m) : -K ≤
      D.curvatureTensor x (B (some i)) (B (some j))
        (B (some i)) (B (some j)) := by
    by_cases hij : i = j
    · subst j
      have hz := D.curvatureTensor_swap_first x
        (B (some i)) (B (some i)) (B (some i)) (B (some i))
      linarith
    · have hs := hsec (B (some i)) (B (some j))
      simpa [sectionalCurvature, hinner, hij] using hs
  have hlower : -(m : ℝ) ^ 2 * K ≤
      ∑ i : Fin m, ∑ j : Fin m,
        D.curvatureTensor x (B (some i)) (B (some j))
          (B (some i)) (B (some j)) := by
    calc
      -(m : ℝ) ^ 2 * K = ∑ _i : Fin m, ∑ _j : Fin m, -K := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  rw [htrace] at hlower
  linarith

end PoincareConjecture.LeviCivitaData

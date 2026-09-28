import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialComparisonBounds
import PoincareConjecture.Proofs.M04.TensorNormBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle BigOperators

universe u v

namespace PoincareConjecture.M44

theorem abs_scalar_le_curvatureTensorNorm {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M) :
    |D.scalarCurvature x| ≤ (n : ℝ) ^ 2 * D.curvatureTensorNorm x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i) : g.inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    simp
  calc
    _ ≤ ∑ i, |D.ricci x (b i) (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        (n : ℝ) * D.curvatureTensorNorm x := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [hb, mul_one] using M04.abs_ricci_le_curvatureTensorNorm D x (b i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul]
      ring

local notation "E" => StandardCapSpace

noncomputable local instance initialChartCoefficientNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance initialChartCoefficientNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

theorem exists_initial_chart_bounds (g0 : StandardInitialMetric)
    {K : Set E} (hK : IsCompact K) (m : ℕ) :
    ∃ delta alpha Z K0 : ℝ, 0 < delta ∧ 0 < alpha ∧ 1 ≤ Z ∧ 1 ≤ K0 ∧
      ∀ (S : GeneralizedSliceCarrier.{u}) (g : RiemannianMetric 3 S.carrier)
        (tip : S.carrier) (scale eta : ℝ) (Q : SurgeryCapClose g0 S g tip scale eta),
      eta ≤ delta → ∀ (N : GeneralizedSliceCarrier.{v}) (gN : RiemannianMetric 3 N.carrier)
        (D : LeviCivitaData gN) (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E N.carrier ∞),
      e.source ⊆ K → EqOn (gN.pullbackCoefficients e) Q.normalizedCoefficients e.source →
      (∀ x ∈ e.source,
        (∀ w : E, alpha * ‖w‖ ^ 2 ≤ gN.pullbackCoefficients e x w w) ∧
        (∀ w : E, gN.pullbackCoefficients e x w w ≤ Z * ‖w‖ ^ 2) ∧
        ∀ j ≤ m + 2, ‖iteratedFDeriv ℝ j (gN.pullbackCoefficients e) x‖ ≤ Z) ∧
      (∀ y ∈ e.target, ∀ j ≤ m, D.curvatureDerivativeNorm j y ≤ K0) ∧
      (∀ y ∈ e.target, D.scalarCurvature y ≤ 9 * K0) := by
  obtain ⟨delta, alpha, Z, hdelta, halpha, hZ, hcoeff⟩ :=
    exists_initial_comparison_metric_bounds.{u} g0 hK (m + 2)
  obtain ⟨K0, hK0, hcurv⟩ := exists_uniform_pullback_curvature_bound m halpha Z
  refine ⟨delta, alpha, Z, K0, hdelta, halpha, hZ, hK0, ?_⟩
  intro S g tip scale eta Q hsmall N gN D e hsub hlink
  obtain ⟨_hdomain, hmetric⟩ := hcoeff S g tip scale eta Q hsmall
  have hjets (x : E) (hx : x ∈ e.source) :
      (∀ w : E, alpha * ‖w‖ ^ 2 ≤ gN.pullbackCoefficients e x w w) ∧
      ∀ j ≤ m + 2, ‖iteratedFDeriv ℝ j (gN.pullbackCoefficients e) x‖ ≤ Z := by
    have heq : gN.pullbackCoefficients e =ᶠ[𝓝 x] Q.normalizedCoefficients :=
      eventually_of_mem (e.open_source.mem_nhds hx) hlink
    refine ⟨?_, ?_⟩
    · rw [heq.eq_of_nhds]
      exact (hmetric x (hsub hx)).1
    · intro j hj
      rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds]
      exact (hmetric x (hsub hx)).2 j hj
  have hphysical (y : N.carrier) (hy : y ∈ e.target) (j : ℕ) (hj : j ≤ m) :
      D.curvatureDerivativeNorm j y ≤ K0 := by
    have hx := e.map_target hy
    have h := hcurv gN D e.open_source e.contMDiffOn (fun x hx =>
      ⟨(e.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx).mfderivToContinuousLinearEquiv
        (by simp), rfl⟩) (e.invFun y) hx (hjets _ hx).1 (hjets _ hx).2 j hj
    exact (congrArg (fun z => D.curvatureDerivativeNorm j z) (e.right_inv hy)).symm.trans_le h
  refine ⟨?_, hphysical, ?_⟩
  · intro x hx
    refine ⟨(hjets x hx).1, ?_, (hjets x hx).2⟩
    intro w
    have hnorm : ‖gN.pullbackCoefficients e x‖ ≤ Z := by
      simpa only [norm_iteratedFDeriv_zero] using (hjets x hx).2 0 (Nat.zero_le _)
    calc
      _ ≤ |gN.pullbackCoefficients e x w w| := le_abs_self _
      _ ≤ ‖gN.pullbackCoefficients e x‖ * ‖w‖ * ‖w‖ :=
        (gN.pullbackCoefficients e x).le_opNorm₂ w w
      _ ≤ Z * ‖w‖ ^ 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖w‖)]
  · intro y hy
    have h0 := hphysical y hy 0 (Nat.zero_le m)
    rw [D.curvatureDerivativeNorm_zero] at h0
    have hscalar := abs_scalar_le_curvatureTensorNorm D y
    norm_num only [Nat.cast_ofNat, Nat.reducePow] at hscalar
    exact (le_abs_self _).trans (hscalar.trans (mul_le_mul_of_nonneg_left h0 (by norm_num)))

end PoincareConjecture.M44

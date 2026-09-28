import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.ParametrizedComparison









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture

private theorem scalar_normalized_jet_comparison
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X Y W : V) {s D δ B Z η : ℝ}
    (hs : (1 / 2 : ℝ) ≤ s) (hsone : s ≤ 1) (hscalar : 1 - s ≤ D * δ)
    (hZ : ‖W‖ ≤ Z)
    (hinit : ‖Y - s⁻¹ • W‖ ≤ η) (htime : ‖X - Y‖ ≤ B * δ) :
    ‖X - W‖ ≤ η + (B + 2 * D * Z) * δ := by
  have hspos : 0 < s := by linarith
  have hDδ : 0 ≤ D * δ := (sub_nonneg.mpr hsone).trans hscalar
  have hinv : |s⁻¹ - 1| ≤ 2 * D * δ := by
    have heq : s⁻¹ - 1 = (1 - s) / s := by field_simp
    rw [heq, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hsone) hspos.le)]
    apply (div_le_iff₀ hspos).mpr
    have h := mul_le_mul_of_nonneg_left hs hDδ
    nlinarith
  have hmodel : ‖s⁻¹ • W - W‖ ≤ 2 * D * Z * δ := by
    rw [show s⁻¹ • W - W = (s⁻¹ - 1) • W by simp only [sub_smul, one_smul],
      norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (2 * D * δ) * Z := mul_le_mul hinv hZ (norm_nonneg _) (by linarith)
      _ = _ := by ring
  have htri := (norm_sub_le_norm_sub_add_norm_sub X Y W).trans
    (add_le_add htime ((norm_sub_le_norm_sub_add_norm_sub Y (s⁻¹ • W) W).trans
      (add_le_add hinit hmodel)))
  calc
    _ ≤ B * δ + (η + 2 * D * Z * δ) := htri
    _ = _ := by ring



theorem exists_roundCylinder_buffered_comparison_constants
    {J : Set ℝ} (hJ : IsCompact J) (d : ℕ) :
    ∃ C Z : ℝ, 0 ≤ C ∧ 0 ≤ Z ∧
      ∀ {M : Type*} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        (g₀ g₁ : RiemannianMetric 3 M) {f : RoundCylinderSpace → M}
        {U : Set RoundCylinderSpace}, IsOpen U →
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f U →
        ∀ (z : RoundCylinderSpace), z ∈ U → z.2 ∈ J →
        ∀ {s D δ B η : ℝ}, (1 / 2 : ℝ) ≤ s → s ≤ 1 →
        0 ≤ D → 0 ≤ δ → 0 ≤ B → 0 ≤ η → 1 - s ≤ D * δ →
        (∀ j ≤ d,
          ‖iteratedFDeriv ℝ j (g₀.parametrizedCoefficients
              (fun p => f ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm p.1, p.2)))
                (0, z.2) -
            s⁻¹ • iteratedFDeriv ℝ j roundCylinderModelCoefficients (0, z.2)‖ ≤ η) →
        (∀ j ≤ d,
          ‖iteratedFDeriv ℝ j (g₁.parametrizedCoefficients
              (fun p => f ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm p.1, p.2)))
                (0, z.2) -
            iteratedFDeriv ℝ j (g₀.parametrizedCoefficients
              (fun p => f ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm p.1, p.2)))
                (0, z.2)‖ ≤ B * δ) →
        roundCylinderJetErrorSquared 0 (roundCylinderPullback g₁ f) d z ≤
          C * (η + (B + 2 * D * Z) * δ) ^ 2 := by
  classical
  let K : Set RoundCylinderCoordinates := {0} ×ˢ J
  have hK : IsCompact K := isCompact_singleton.prod hJ
  choose Z₀ hZ₀ hmodel using fun j => exists_roundCylinderModelCoefficients_jet_bound hK j
  let Z := ∑ j ∈ Finset.range (d + 1), Z₀ j
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun j _ => hZ₀ j
  obtain ⟨C, hC, hcompare⟩ := exists_roundCylinderJetErrorSquared_bound_of_parametrizedJets hJ d
  refine ⟨C, Z, hC, hZ, ?_⟩
  intro M _ _ _ g₀ g₁ f U hU hf z hz hzJ s D δ B η hs hsone hD hδ hB hη hscalar
    hinit htime
  let e : RoundCylinderCoordinates → M :=
    fun p => f ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm p.1, p.2)
  have hmap : ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ e (0, z.2) := by
    have hz' : ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).symm
        (0 : EuclideanSpace ℝ (Fin 2)), z.2) ∈ U := by
      simpa only [Poincare.Geometry.Riemannian.SpaceForm.sphere_chart_symm_zero] using hz
    exact (hf.contMDiffAt (hU.mem_nhds hz')).comp (0, z.2)
      (cylinderChart_symm_smooth z.1 (0, z.2))
  have hA := g₁.contDiffAt_parametrizedCoefficients hmap
  have hW := contDiff_roundCylinderModelCoefficients.contDiffAt (x := (0, z.2))
  have hbound := hcompare g₁ hU hf 1 z hz hzJ
    (η + (B + 2 * D * Z) * δ) (by positivity) ?_
  · simpa only [one_mul] using hbound
  intro j hj
  simp only [one_smul]
  change ‖iteratedFDeriv ℝ j
    (g₁.parametrizedCoefficients e - roundCylinderModelCoefficients) (0, z.2)‖ ≤ _
  rw [iteratedFDeriv_sub_apply (hA.of_le (by exact_mod_cast le_top))
    (hW.of_le (by exact_mod_cast le_top))]
  apply scalar_normalized_jet_comparison _ _ _ hs hsone hscalar _ (hinit j hj) (htime j hj)
  exact (hmodel j (0, z.2) ⟨rfl, hzJ⟩).trans
    (Finset.single_le_sum (fun l _ => hZ₀ l) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))



theorem exists_roundCylinder_terminal_error_tolerance
    {ε C B : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ {δ : ℝ}, 0 ≤ δ → δ ≤ η →
      C * (η + B * δ) ^ 2 ≤ ε ^ 2 / 4 := by
  let η := ε / (2 * (C + 1) * (B + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη
  have heq : (C + 1) * (η + B * η) = ε / 2 := by dsimp [η]; field_simp; ring
  have hE : 0 ≤ η + B * δ := by positivity
  have hEc : (C + 1) * (η + B * δ) ≤ ε / 2 := by
    rw [← heq]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (le_refl η) (mul_le_mul_of_nonneg_left hδη hB)) (by positivity)
  have hsq := (sq_le_sq₀ (mul_nonneg (by positivity) hE)
    (by positivity : 0 ≤ ε / 2)).mpr hEc
  have hCC : C ≤ (C + 1) ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hCC (sq_nonneg (η + B * δ))
  nlinarith

end PoincareConjecture

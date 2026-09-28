import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CornerModels
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.UniversalProperty

noncomputable section
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem PoincareConjecture.RiemannianMetric.exists_empty_corner_model
    {n : ℕ} {M : Type} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    (δ : ℝ) (p : M) :
    ∃ A : PointedCornerModel n 0 δ 0, A.weightedRatio =
      (∫ x in g.ball p 1, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) /
      (1+g.volumeMeasure.real (g.ball p 2)) := by
  classical
  let f : Fin 0 → M → ℝ := fun _ _ => 0
  let P : M → Fin 0 → ℝ := fun _ _ => 0
  let c : Fin 0 → ℝ := 0
  let U : Opens M := ⊤
  have hP : ContMDiff (𝓡 n) 𝓘(ℝ,Fin 0 → ℝ) ∞ P := contMDiff_const
  have hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 n) 𝓘(ℝ,Fin 0 → ℝ) P x) := by
    intro x _ z
    refine ⟨0, ?_⟩
    change (_ : Fin 0 → ℝ) = _
    exact Subsingleton.elim _ _
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n+0) := ⟨by simp⟩
  let := openFiberChartedSpace (m := n) hP U hreg c
  let := isManifold_openFiber (m := n) hP U hreg c
  let L := openFiber P U c
  let incl := openFiberIncl P U c
  let gL := g.openRegularFiberMetric (m := n) (k := 0) hP U hreg c
  let e₀ : L ≃ M :=
    { toFun := incl
      invFun := fun x => ⟨⟨x, mem_univ x⟩, Subsingleton.elim _ _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e : L ≃ₘ⟮𝓡 n,𝓡 n⟯ M :=
    { e₀ with
      contMDiff_toFun := contMDiff_openFiberIncl (m := n) hP U hreg c
      contMDiff_invFun := by
        intro x
        apply (contMDiffAt_into_openFiber_iff (m := n) hP c U hreg e₀.symm x).mpr
        exact contMDiffAt_id }
  have hmetric : ∀ x (v w : TangentSpace (𝓡 n) x),
      gL.inner x v w = g.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w) :=
    fun _ _ _ => rfl
  have hscalar (x : L) : gL.leviCivitaData.scalarCurvature x = D.scalarCurvature (incl x) :=
    gL.leviCivitaData.scalarCurvature_eq_of_local_isometry D isOpen_univ
      e.contMDiff.contMDiffOn (fun x _ => hmetric x) (mem_univ x)
  have hsecL : ∀ x (v w : TangentSpace (𝓡 n) x),
      -(1:ℝ) ≤ gL.leviCivitaData.sectionalCurvature x v w := by
    intro x v w
    rw [gL.sectionalCurvature_diffeomorph g e hmetric gL.leviCivitaData D]
    exact hsec _ _ _
  let A : PointedCornerModel n 0 δ 0 :=
    { carrier := M
      metric := g
      connection := D
      complete := hc
      sectional_lower := hsec
      f := f
      h := f
      f_smooth := fun i => Fin.elim0 i
      h_smooth := fun i => Fin.elim0 i
      domain := U
      unit := fun _ _ i => Fin.elim0 i
      opposite := fun _ _ i => Fin.elim0 i
      cross := fun _ _ i => Fin.elim0 i
      tight := fun _ _ i => Fin.elim0 i
      hessian_upper := fun _ _ i => Fin.elim0 i
      regular := hreg
      value := c
      point := e.symm p
      buffer := fun y _ => mem_univ y
      error := fun _ => 1
      error_continuous := continuous_const
      error_nonneg := fun _ => zero_le_one
      error_sectional_lower := hsecL }
  refine ⟨A, ?_⟩
  have htransport (s : Set M) (v : M → ℝ) :
      (∫ x in incl ⁻¹' s, v (incl x) ∂gL.volumeMeasure) =
        ∫ y in s, v y ∂g.volumeMeasure := by
    have ht := (gL.measurePreserving_diffeomorph g e hmetric).setIntegral_image_emb
      e.toHomeomorph.measurableEmbedding v (e ⁻¹' s)
    have himage : e '' (e ⁻¹' s) = s :=
      Set.image_preimage_eq s (show Surjective (e : L → M) from e.surjective)
    rw [himage] at ht
    exact ht.symm
  change
    (∫ x in incl ⁻¹' g.ball p 1, max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure) /
      (1+∫ x in incl ⁻¹' g.ball p 2, (1:ℝ) ∂gL.volumeMeasure) = _
  simp_rw [hscalar]
  rw [htransport (g.ball p 1) (fun x => max 0 (D.scalarCurvature x)),
    htransport (g.ball p 2) (fun _ => 1)]
  simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_one]

theorem PoincareConjecture.exists_uniform_unitBall_scalar_integral_bound_of_corner_models
    (n : ℕ) (hn : 2 ≤ n) (δ : ℝ)
    (hbound : ∃ B : ℝ, ∀ A : PointedCornerModel n 0 δ 0, A.weightedRatio ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M]
        (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g),
        PoincareConjecture.MetricComplete g →
        (∀ (x : M) (v w : TangentSpace (𝓡 n) x),
          -1 ≤ D.sectionalCurvature x v w) →
        ∀ p : M,
          (∫ x in g.ball p 1, D.scalarCurvature x ∂g.volumeMeasure) ≤ C := by
  classical
  obtain ⟨B, hbound⟩ := hbound
  let B₀ := max 0 B
  have hB₀ : 0 ≤ B₀ := le_max_left _ _
  let V := RiemannianMetric.modelVolume n 1 2
  have hV : 0 < V :=
    RiemannianMetric.modelVolume_pos (by omega) (by norm_num) (by norm_num)
  let C := B₀*(1+V)+1
  have hC : 0 < C := by
    have hp : 0 ≤ B₀*(1+V) := mul_nonneg hB₀ (by linarith)
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ g D hc hsec p
  apply g.scalar_integral_le_of_small_connected_bound D hc hsec C ?_ p
  intro Q _ _ _ _ _ _ _ g D hc hsec p
  obtain ⟨A, hratio⟩ := g.exists_empty_corner_model D hc hsec δ p
  have hb : A.weightedRatio ≤ B₀ := (hbound A).trans (le_max_right _ _)
  rw [hratio] at hb
  have hden : 0 < 1+g.volumeMeasure.real (g.ball p 2) := by
    have hv : 0 ≤ g.volumeMeasure.real (g.ball p 2) := ENNReal.toReal_nonneg
    linarith
  have hpos := (div_le_iff₀ hden).mp hb
  have hvol := g.volumeMeasure_real_ball_le_modelVolume_of_sectional_lower_bound
    p (by omega) hc D hsec (by norm_num : (0:ℝ)<2)
  have hunit : (∫ x in g.ball p 1, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      B₀*(1+V) :=
    hpos.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hvol) hB₀)
  have hiR := g.integrableOn_ball_of_continuous hc D.continuous_scalarCurvature p 1
  have hiP := g.integrableOn_ball_of_continuous hc
    ((continuous_const (y := (0:ℝ))).max D.continuous_scalarCurvature) p 1
  exact ((integral_mono hiR hiP (fun _ => le_max_right _ _)).trans hunit).trans
    (le_add_of_nonneg_right zero_le_one)

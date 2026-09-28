import PoincareConjecture.Proofs.M32.Mathlib.LastLevel
import PoincareConjecture.Proofs.M32.Thm11_31.SeedEndCut.Seed
import PoincareConjecture.Proofs.M32.Cor11_36.Propagation
import PoincareConjecture.Proofs.M32.Thm11_31.Levels












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32





theorem exists_deepHornConclusion_of_contained_necks :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        (A : RepairedNeckCapTopologyTheory.{u})
        (H : SingularTimeAssumptions F T M) (Q : SingularLimitConclusion H)
        {epsilon : ℝ},
        0 < epsilon → epsilon ≤ tau → epsilon ≤ A.epsilon₀ →
        ∀ (horn : StrongHorn Q.extension epsilon) {C rho delta h : ℝ},
          0 < C → 0 < rho → 0 < delta → delta ≤ tau → 0 < h →
          h ≤ min (rho * delta) (min (rho / 2) ((rho / (2 * C)) / 2)) →
          HornBoundaryBelow horn (rho / (2 * C)) →
          (∀ x ∈ horn.carrier, h⁻¹ ^ 2 ≤
            (Q.extension.extended.connection T).scalarCurvature x →
            ∃ N : TerminalStrongNeck Q.extension delta,
              N.center = x ∧ N.carrier ⊆ horn.carrier) →
          Nonempty (DeepHornNeckConclusion Q.extension epsilon C rho delta horn h) := by
  obtain ⟨epsilonSeed, hSeedPos, hSeedSmall, _hSeedCollar, hseed⟩ :=
    exists_horn_seed_endCut_threshold.{u}
  obtain ⟨tauPropagation, hPropPos, _hPropSmall, hprop⟩ := exists_hornCut_propagation.{u}
  refine ⟨min epsilonSeed tauPropagation, lt_min hSeedPos hPropPos,
    (min_le_left _ _).trans hSeedSmall, ?_⟩
  intro F T M _ _ _ _ _ _ _ _ A H Q epsilon hepsilon hsmall hA
    horn C rho delta h hC hrho hdelta hdsmall hh hupper hboundary hnecks
  let b := rho / (2 * C)
  let q := 2 * max (rho⁻¹ ^ 2) (b⁻¹ ^ 2)
  have hb : 0 < b := div_pos hrho (mul_pos (by norm_num) hC)
  have hhalf (r : ℝ) (hr : 0 < r) (hhr : h ≤ r / 2) :
      2 * r⁻¹ ^ 2 < h⁻¹ ^ 2 := by
    have hinv : (r / 2)⁻¹ ≤ h⁻¹ := (inv_le_inv₀ (half_pos hr) hh).2 hhr
    have heq : (r / 2)⁻¹ = 2 * r⁻¹ := by rw [inv_div]; ring
    rw [heq] at hinv
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * r⁻¹) hinv 2
    nlinarith [sq_pos_of_pos (inv_pos.mpr hr)]
  have hhRho : h ≤ rho / 2 := hupper.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhB : h ≤ b / 2 := hupper.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlevel : q < h⁻¹ ^ 2 := by
    dsimp only [q]
    rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact max_lt (hhalf rho hrho hhRho) (hhalf b hb hhB)
  have hlow : rho⁻¹ ^ 2 ≤ q / 2 := by
    dsimp only [q]
    nlinarith [le_max_left (rho⁻¹ ^ 2) (b⁻¹ ^ 2)]
  have hboundaryQ : ∀ y ∈ horn.boundary_sphere,
      (Q.extension.extended.connection T).scalarCurvature y ≤ q / 2 := by
    intro y hy
    have hby : (Q.extension.extended.connection T).scalarCurvature y ≤ b⁻¹ ^ 2 :=
      hboundary y hy
    dsimp only [q]
    nlinarith [le_max_right (rho⁻¹ ^ 2) (b⁻¹ ^ 2)]
  obtain ⟨N0, hN0, hN0high, _hN0carrier, ⟨cut0⟩⟩ :=
    hseed A H Q hepsilon (hsmall.trans (min_le_left _ _)) hA horn rho (h⁻¹ ^ 2)
  let z0 := horn.coordinate.symm ⟨N0.center, hN0⟩
  let gamma : ℝ → (Q.extension.extended.slice T).carrier :=
    fun t => horn.parameterization (z0.1, t)
  let R := (Q.extension.extended.connection T).scalarCurvature
  have hendpoint : gamma z0.2 = N0.center := by
    change horn.parameterization (z0.1, (z0.2 : ℝ)) = N0.center
    rw [← horn.coordinate_eq]
    exact congrArg Subtype.val (horn.coordinate.apply_symm_apply ⟨N0.center, hN0⟩)
  have hgamma : ContinuousOn gamma (Icc 0 (z0.2 : ℝ)) := by
    apply horn.parameterization_smooth.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro t ht
    exact ⟨mem_univ _, (neg_lt_zero.mpr horn.collar_pos).trans_le ht.1,
      ht.2.trans_lt z0.2.property.2⟩
  have hgammaH (t : ℝ) (ht : t ∈ Icc 0 (z0.2 : ℝ)) : gamma t ∈ horn.carrier := by
    have hmem := (horn.coordinate (z0.1, ⟨t, ht.1, ht.2.trans_lt z0.2.property.2⟩)).property
    simpa only [horn.coordinate_eq] using hmem
  have hf : ContinuousOn (R ∘ gamma) (Icc 0 (z0.2 : ℝ)) :=
    (Q.extension.extended.connection T).continuous_scalarCurvature.comp_continuousOn hgamma
  have hzeroBoundary : gamma 0 ∈ horn.boundary_sphere := by
    rw [horn.boundary_sphere_eq]
    exact ⟨(z0.1, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hzeroLevel : (R ∘ gamma) 0 ≤ h⁻¹ ^ 2 := by
    have hqnonneg : 0 ≤ q := by dsimp [q]; positivity
    exact (hboundaryQ _ hzeroBoundary).trans (by linarith)
  have hlastLevel : h⁻¹ ^ 2 ≤ (R ∘ gamma) z0.2 := by
    simpa only [Function.comp_apply, hendpoint, R] using hN0high.le
  obtain ⟨a, ha, hRa, htail⟩ :=
    exists_last_level_Icc z0.2.property.1 hf hzeroLevel hlastLevel
  let s : Set (Q.extension.extended.slice T).carrier := gamma '' Icc a (z0.2 : ℝ)
  have hinterval : Icc a (z0.2 : ℝ) ⊆ Icc 0 (z0.2 : ℝ) :=
    Icc_subset_Icc ha.1 le_rfl
  have hs : IsPreconnected s := isPreconnected_Icc.image gamma (hgamma.mono hinterval)
  have hsH : s ⊆ horn.carrier := by
    rintro _ ⟨t, ht, rfl⟩
    exact hgammaH t (hinterval ht)
  have hsR : ∀ y ∈ s, q < R y := by
    rintro _ ⟨t, ht, rfl⟩
    exact hlevel.trans_le (htail t ht)
  have hN0s : N0.center ∈ s :=
    ⟨z0.2, ⟨ha.2, le_rfl⟩, hendpoint⟩
  have hxs : gamma a ∈ s := mem_image_of_mem gamma ⟨le_rfl, ha.2⟩
  obtain ⟨N, hN, hNcarrier⟩ := hnecks (gamma a) (hsH hxs) hRa.ge
  let alpha := max epsilon delta
  have healpha : epsilon ≤ alpha := le_max_left _ _
  have hdalpha : delta ≤ alpha := le_max_right _ _
  have halpha : alpha ≤ tauPropagation := max_le
    (hsmall.trans (min_le_right _ _)) (hdsmall.trans (min_le_right _ _))
  obtain ⟨cutAlpha⟩ := hprop horn healpha halpha hlow hboundaryQ hs hsH hsR
    (restrictNeckAccuracy N0 healpha) hN0s ⟨restrictHornCutAccuracy cut0 healpha⟩
    (restrictNeckAccuracy N hdalpha) (by change N.center ∈ s; rw [hN]; exact hxs)
  let cut := hornEndCut_of_centralSphere_eq horn
    (restrictNeckAccuracy N hdalpha) N rfl cutAlpha
  refine ⟨{
    h_pos := hh
    h_upper := le_min (hupper.trans (min_le_left _ _)) (hhB.trans (by linarith))
    deep_neck := hnecks
    selected_neck := ⟨N, ?_, hNcarrier, ?_, ⟨cut⟩⟩ }⟩
  · rw [hN]
    exact hsH hxs
  · rw [hN]
    exact hRa

end PoincareConjecture.M32

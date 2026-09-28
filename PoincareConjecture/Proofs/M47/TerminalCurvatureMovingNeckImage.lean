import PoincareConjecture.Proofs.M47.TerminalCurvaturePartialChartJets
import PoincareConjecture.Proofs.M47.TerminalCurvatureNeckErrorJets
import PoincareConjecture.Proofs.M47.TerminalCurvatureDoubleImage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M47

open M34

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_double_neck_derivative_budget
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2) :
    Nat.floor (2 * epsilon)⁻¹ + 1 ≤ Nat.floor epsilon⁻¹ := by
  have hi : (1 / 2 : ℝ)⁻¹ ≤ epsilon⁻¹ := inv_anti₀ hepsilon (by linarith)
  norm_num at hi
  have hgap : (2 * epsilon)⁻¹ + 1 ≤ epsilon⁻¹ := by
    rw [mul_inv_rev]
    norm_num
    linarith
  simpa only [Nat.floor_add_one (by positivity : 0 ≤ (2 * epsilon)⁻¹)] using
    Nat.floor_mono hgap

theorem terminalCurvature_exists_moving_neck_image_tolerance
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    {b K : ℝ} (hb : 0 < b) (hK : 1 ≤ K) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 / 2 ∧
      ∀ (M : Type u) (X : Type v) [TopologicalSpace M] [TopologicalSpace X]
        [ChartedSpace E M] [ChartedSpace E X]
        [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X] [T2Space M]
        (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 X)
        (N : EpsilonNeck g), N.epsilon = epsilon →
      ∀ (D : LeviCivitaData h) (psi : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞),
      N.carrier ⊆ psi.source →
      (∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ →
        ∃ c : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞,
          N.coordinate_map (q, s) ∈ c.source ∧ ‖c (N.coordinate_map (q, s))‖ ≤ K ∧
          let B := RiemannianMetric.pullbackCoefficients
            (M13.scaleSmoothMetric g (N.scale⁻¹ ^ 2)
              (sq_pos_of_pos (inv_pos.mpr N.scale_pos))) c.symm
          let T := fun y => N.scale⁻¹ ^ 2 •
            (h.pullbackCoefficients (psi ∘ c.symm) y - g.pullbackCoefficients c.symm y)
          (∀ j ≤ Nat.floor (2 * epsilon)⁻¹ + 1,
            ‖iteratedFDeriv ℝ j B (c (N.coordinate_map (q, s)))‖ ≤ K) ∧
          (∀ v, b * ‖v‖ ^ 2 ≤ B (c (N.coordinate_map (q, s))) v v) ∧
          (∀ j ≤ Nat.floor (2 * epsilon)⁻¹,
            ‖iteratedFDeriv ℝ j T (c (N.coordinate_map (q, s)))‖ ≤ delta)) →
      |N.scale ^ 2 * D.scalarCurvature (psi N.center) - 1| ≤ sigma →
      ∃ W : EpsilonNeck h,
        W.epsilon = 2 * epsilon ∧ W.center = psi N.center ∧ W.connection = D ∧
        W.carrier = psi '' N.region (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ ∧
        W.coordinate_map = psi ∘ N.coordinate_map := by
  let m := Nat.floor (2 * epsilon)⁻¹
  have hm : m + 1 ≤ Nat.floor epsilon⁻¹ :=
    terminalCurvature_double_neck_derivative_budget hepsilon hsmall
  obtain ⟨D0, hD0, hmap⟩ :=
    terminalCurvature_exists_neck_partial_chart_jet_bound_uniform.{u} m hm hb hK
  obtain ⟨C, hC, herror⟩ :=
    terminalCurvature_exists_neck_chart_error_constant_uniform.{u, v} m hD0
  obtain ⟨rho, hrho, sigma, hsigma, hsigmaHalf, himage⟩ :=
    terminalCurvature_exists_double_image_tolerance_uniform.{u, v} hepsilon hsmall
  let delta := rho / (C + 1)
  have hdelta : 0 < delta := div_pos hrho (by positivity)
  have hsmallError : C * delta ≤ rho := by
    have heq : (C + 1) * delta = rho := by dsimp only [delta]; field_simp
    nlinarith
  refine ⟨delta, hdelta, sigma, hsigma, hsigmaHalf, ?_⟩
  intro M X _ _ _ _ _ _ _ g h N hN D psi hsource hcharts hscalar
  apply himage M X g h N hN D psi hsource ?_ hscalar
  intro q s hs j hj a d
  obtain ⟨c, hc, hcenter, hBj, hfloor, hTj⟩ := hcharts q s hs
  have hinv : (2 * epsilon)⁻¹ ≤ epsilon⁻¹ := inv_anti₀ hepsilon (by linarith)
  have hsold : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    ⟨(neg_le_neg hinv).trans_lt hs.1, hs.2.trans_le hinv⟩
  have hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by simpa only [hN] using hsold
  have hmapj := hmap M g N hN c q s hsold hc hcenter hBj hfloor
  have hf0 : ((c : M → E) ∘ N.capPersistenceEuclideanMap q s) 0 =
      c (N.coordinate_map (q, s)) :=
    congrArg c (congrArg N.coordinate_map (capPersistenceSphereChart_zero q s))
  apply (herror M X g N h psi hsource c q s hsN hc
    (fun l hl => hmapj l (by omega)) delta hdelta.le (fun l hl => ?_)
    j hj a d).trans hsmallError
  rw [hf0]
  exact hTj l hl

end PoincareConjecture.M47

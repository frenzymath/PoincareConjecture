import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryAngularPositive
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPositiveDegreeOne













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)





theorem exists_actual_scalar_boundary_coordinates
    {H : Plane → ℝ} {V : Cover → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P)
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P) :
    ∃ (J : Plane → Plane →L[ℝ] ℝ) (K : ℝ≥0) (W : Cover → ℝ),
      ContinuousOn J (closure scalarAnnulus) ∧ EqOn J (fderiv ℝ H) scalarAnnulus ∧
      LipschitzWith K W ∧ EqOn W V scalarCoverStrip ∧
      (∀ z ∈ closure scalarCoverStrip, W (z + (0, 1)) = W z + P) ∧
      ∀ r : ℝ, r = 1 ∨ r = 2 →
        ∃ (phi : ℝ ≃ₜ ℝ) (sigma : M64PeriodicDegreeOneLift),
          (∀ x : ℝ, phi x = (curvePeriod / P) * W (r, x / curvePeriod)) ∧
          sigma.map = phi.symm ∧
          ContDiff ℝ 1 (phi : ℝ → ℝ) ∧ ContDiff ℝ 1 sigma.map ∧
          StrictMono phi ∧ StrictMono sigma.map ∧
          (∀ x : ℝ, phi (x + curvePeriod) = phi x + curvePeriod) ∧
          (∀ x : ℝ, HasDerivAt phi
            (scalarCoverFormOfDifferential g J (r, x / curvePeriod) (0, 1) / P) x) ∧
          ∀ y : ℝ, HasDerivAt sigma.map
            (scalarCoverFormOfDifferential g J (r, sigma.map y / curvePeriod) (0, 1) / P)⁻¹ y := by
  obtain ⟨J, K, W, hJc, hJeq, -, hW, hWV, hBc, hperiod, hdW⟩ :=
    exists_scalar_conjugate_closed_differential D hHc hHs hlap hinner houter hdV P hdeck
  refine ⟨J, K, W, hJc, hJeq, hW, hWV, hperiod, ?_⟩
  intro r hr
  have hrcc : r ∈ Icc (1 : ℝ) 2 := by rcases hr with rfl | rfl <;> norm_num
  have hp : 0 < curvePeriod := by unfold curvePeriod; positivity
  let f : ℝ → ℝ := fun x => (curvePeriod / P) * W (r, x / curvePeriod)
  let d : ℝ → ℝ := fun x =>
    scalarCoverFormOfDifferential g J (r, x / curvePeriod) (0, 1) / P
  have hd (x : ℝ) : HasDerivAt f (d x) x := by
    have h := ((scalar_closed_strip_hasDerivAt_angle hdW hrcc (x / curvePeriod)).comp x
      ((hasDerivAt_id x).div_const curvePeriod)).const_mul (curvePeriod / P)
    convert! h using 1
    dsimp only [d]
    field_simp
  have hdc : Continuous d := by
    have hc : Continuous (fun x : ℝ =>
        scalarCoverFormOfDifferential g J (r, x / curvePeriod)) := by
      apply continuousOn_univ.mp
      apply hBc.comp (continuous_const.prodMk (continuous_id.div_const curvePeriod)).continuousOn
      intro x _
      rw [scalarCoverStrip_closure]
      exact hrcc
    exact (hc.clm_apply continuous_const).div_const P
  have hdpos (x : ℝ) : 0 < d x := div_pos
    (scalarCoverForm_boundary_angular_pos D hHc hHs hlap hinner houter
      hJc hJeq hr (x / curvePeriod)) hP
  have hshift (x : ℝ) : f (x + curvePeriod) = f x + curvePeriod := by
    have hz : (r, x / curvePeriod) ∈ closure scalarCoverStrip := by
      rw [scalarCoverStrip_closure]
      exact hrcc
    have hs := hperiod (r, x / curvePeriod) hz
    simp only [Prod.mk_add_mk, add_zero] at hs
    dsimp only [f]
    rw [add_div, div_self hp.ne', hs]
    field_simp
  obtain ⟨phi, hphif, hmono, himono, hphis, hphisi, hphisft, hinvsft, hinvd, L, L', -, hL'⟩ :=
    exists_positive_degree_one_homeomorph hd hdc hdpos hp hshift
  let sigma : M64PeriodicDegreeOneLift :=
    { map := phi.symm
      monotone := himono.monotone
      period_shift := hinvsft
      lipschitz_constant := L'
      lipschitz_nonnegative := L'.coe_nonneg
      lipschitz_on := by
        intro x y
        simpa only [Real.dist_eq] using hL'.dist_le_mul x y }
  refine ⟨phi, sigma, ?_, rfl, hphis, hphisi, hmono, himono, hphisft, ?_, hinvd⟩
  · intro x
    exact congrFun hphif x
  · intro x
    rw [hphif]
    exact hd x

end PoincareConjecture.M64Uniformization

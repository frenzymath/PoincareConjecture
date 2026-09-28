import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarActualBoundaryCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

private theorem scalarClosedCover_forward_identity
    {H : Plane → ℝ} {V W : Cover → ℝ} {F : Cover → Plane} {P : ℝ}
    (hHc : Continuous H) (hWc : Continuous W) (hFc : Continuous F)
    (hWV : EqOn W V scalarCoverStrip) (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P)
    (hFeq : EqOn F (scalarInverseCoverMap e) e.target) :
    ∀ z ∈ closure scalarCoverStrip,
      F (H (scalarCoverMap z), W z / P) = scalarCoverMap z := by
  apply closure_minimal _ (isClosed_eq
    (hFc.comp ((hHc.comp scalarCoverMap_smooth.continuous).prodMk (hWc.div_const P)))
    scalarCoverMap_smooth.continuous)
  intro z hz
  change F (H (scalarCoverMap z), W z / P) = scalarCoverMap z
  have hzs : z ∈ e.source := hsource ▸ hz
  have hzmap : (H (scalarCoverMap z), W z / P) = e z := by
    rw [he, hWV hz]
    rfl
  rw [hzmap, hFeq (e.map_source hzs)]
  simp only [scalarInverseCoverMap, Function.comp_apply, e.left_inv hzs]

private theorem scalarClosedCover_inverse_boundary
    {H : Plane → ℝ} {V W : Cover → ℝ} {F : Cover → Plane} {P : ℝ}
    (hHc : Continuous H) (hWc : Continuous W) (hFc : Continuous F)
    (hWV : EqOn W V scalarCoverStrip) (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P)
    (hFeq : EqOn F (scalarInverseCoverMap e) e.target)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {r : ℝ} (hr : r = 1 ∨ r = 2) (phi : ℝ ≃ₜ ℝ)
    (hphi : ∀ x : ℝ, phi x = (curvePeriod / P) * W (r, x / curvePeriod)) (x : ℝ) :
    F (r - 1, x / curvePeriod) = scalarCoverMap (r, phi.symm x / curvePeriod) := by
  have hp : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hrad : r ∈ Icc (1 : ℝ) 2 := by rcases hr with rfl | rfl <;> norm_num
  have hz : (r, phi.symm x / curvePeriod) ∈ closure scalarCoverStrip := by
    rw [scalarCoverStrip_closure]
    exact hrad
  have hid := scalarClosedCover_forward_identity hHc hWc hFc hWV e hsource he hFeq
    (r, phi.symm x / curvePeriod) hz
  have hH : H (scalarCoverMap (r, phi.symm x / curvePeriod)) = r - 1 := by
    rcases hr with rfl | rfl
    · rw [hinner]
      · norm_num
      · norm_num [scalarCoverMap, scalarCirclePoint_norm]
    · rw [houter]
      · norm_num
      · norm_num [scalarCoverMap, scalarCirclePoint_norm]
  have hangle : W (r, phi.symm x / curvePeriod) / P = x / curvePeriod := by
    apply (eq_div_iff hp.ne').mpr
    calc
      _ = (curvePeriod / P) * W (r, phi.symm x / curvePeriod) := by ring
      _ = phi (phi.symm x) := (hphi (phi.symm x)).symm
      _ = x := phi.apply_symm_apply x
  simpa only [hH, hangle] using hid

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem exists_scalarClosedCover_boundary_lifts
    {H : Plane → ℝ} {V : Cover → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P) (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P)
    (hdeck : ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1))
    {F : Cover → Plane} (hFc : Continuous F)
    (hFeq : EqOn F (scalarInverseCoverMap e) e.target) :
    ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
      ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
      StrictMono sigma0.map ∧ StrictMono sigma1.map ∧
      (∀ x : ℝ, 0 < deriv sigma0.map x) ∧ (∀ x : ℝ, 0 < deriv sigma1.map x) ∧
      (∀ x : ℝ, F (0, x / curvePeriod) = scalarCoverMap (1, sigma0.map x / curvePeriod)) ∧
      ∀ x : ℝ, F (1, x / curvePeriod) = scalarCoverMap (2, sigma1.map x / curvePeriod) := by
  have hVdeck (z : Cover) (hz : z ∈ scalarCoverStrip) : V (z + (0, 1)) = V z + P := by
    have h := congrArg Prod.snd (hdeck z (hsource ▸ hz))
    rw [he] at h
    change V (z + (0, 1)) / P = V z / P + 1 at h
    calc
      _ = (V (z + (0, 1)) / P) * P := (div_mul_cancel₀ _ hP.ne').symm
      _ = (V z / P + 1) * P := congrArg (fun a : ℝ => a * P) h
      _ = _ := by field_simp
  obtain ⟨J, K, W, hJc, hJeq, hW, hWV, -, hcoordinates⟩ :=
    exists_actual_scalar_boundary_coordinates D hHc hHs hlap hinner houter hdV hP hVdeck
  obtain ⟨phi0, sigma0, hphi0, hsigma0, -, hs0, -, hsm0, -, -, hd0⟩ :=
    hcoordinates 1 (Or.inl rfl)
  obtain ⟨phi1, sigma1, hphi1, hsigma1, -, hs1, -, hsm1, -, -, hd1⟩ :=
    hcoordinates 2 (Or.inr rfl)
  refine ⟨sigma0, sigma1, hs0, hs1, hsm0, hsm1, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [(hd0 x).deriv]
    exact inv_pos.mpr (div_pos (scalarCoverForm_boundary_angular_pos D
      hHc hHs hlap hinner houter hJc hJeq (Or.inl rfl) _) hP)
  · intro x
    rw [(hd1 x).deriv]
    exact inv_pos.mpr (div_pos (scalarCoverForm_boundary_angular_pos D
      hHc hHs hlap hinner houter hJc hJeq (Or.inr rfl) _) hP)
  · intro x
    rw [hsigma0]
    simpa only [sub_self] using scalarClosedCover_inverse_boundary hHc hW.continuous hFc hWV
      e hsource he hFeq hinner houter (Or.inl rfl) phi0 hphi0 x
  · intro x
    rw [hsigma1]
    convert! scalarClosedCover_inverse_boundary hHc hW.continuous hFc hWV
      e hsource he hFeq hinner houter (Or.inr rfl) phi1 hphi1 x using 1
    norm_num

end PoincareConjecture.M64Uniformization

import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPositiveDegreeOne
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeBoundaryTransport
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Def19_12_PositiveDegree













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff NNReal

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem degreeOneRamp_eq_of_circle_eq
    (P : M62.CircleProductData F circumference) {gamma : ℝ → P.charts.Point}
    (hp : Function.Periodic gamma curvePeriod) (L : M63PositiveDegreeLift P gamma)
    (hdegree : L.degree = 1) {x y : ℝ} (hcircle : (gamma x).2 = (gamma y).2) :
    gamma x = gamma y := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hmono : StrictMono L.lift := strictMono_of_deriv_pos L.derivative_positive
  obtain ⟨x', hx', hxx⟩ := hp.exists_mem_Ico₀ hP x
  obtain ⟨y', hy', hyy⟩ := hp.exists_mem_Ico₀ hP y
  rw [hxx, hyy] at hcircle ⊢
  have hend : L.lift curvePeriod = L.lift 0 + circumference := by
    simpa only [zero_add, hdegree, Nat.cast_one, one_mul] using L.period_shift 0
  have hmem (z : ℝ) (hz : z ∈ Ico (0 : ℝ) curvePeriod) :
      L.lift z ∈ Ico (L.lift 0) (L.lift 0 + circumference) :=
    ⟨hmono.monotone hz.1, (hmono hz.2).trans_eq hend⟩
  have hquot : (L.lift x' : AddCircle circumference) = (L.lift y' : AddCircle circumference) :=
    (L.quotient_eq x').trans (hcircle.trans (L.quotient_eq y').symm)
  have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hmem x' hx') (hmem y' hy')).mp hquot
  exact congrArg gamma (hmono.injective heq)

private theorem degreeOneRamp_phase_homeomorph
    (P : M62.CircleProductData F circumference) {gamma : ℝ → P.charts.Point}
    (L : M63PositiveDegreeLift P gamma) (hdegree : L.degree = 1) :
    ∃ phi : ℝ ≃ₜ ℝ,
      (∀ x, phi x = curvePeriod / circumference * L.lift x) ∧
      StrictMono phi ∧ StrictMono phi.symm ∧
      ContDiff ℝ 1 (phi : ℝ → ℝ) ∧ ContDiff ℝ 1 (phi.symm : ℝ → ℝ) ∧
      (∀ x, phi (x + curvePeriod) = phi x + curvePeriod) ∧
      (∀ x, phi.symm (x + curvePeriod) = phi.symm x + curvePeriod) ∧
      ∃ K J : ℝ≥0, LipschitzWith K phi ∧ LipschitzWith J phi.symm := by
  let k := curvePeriod / circumference
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hk : 0 < k := div_pos hP P.circle.positive
  have hd (x : ℝ) : HasDerivAt (fun y => k * L.lift y) (k * deriv L.lift x) x :=
    ((L.regular.differentiable (by norm_num)) x).hasDerivAt.const_mul k
  have hdc : Continuous (fun x => k * deriv L.lift x) :=
    continuous_const.mul (L.regular.continuous_deriv (by norm_num))
  have hshift (x : ℝ) : k * L.lift (x + curvePeriod) = k * L.lift x + curvePeriod := by
    rw [L.period_shift, hdegree, Nat.cast_one, one_mul, mul_add]
    have hkP : k * circumference = curvePeriod := div_mul_cancel₀ _ P.circle.positive.ne'
    rw [hkP]
  obtain ⟨phi, hphi, hm, hmi, hc, hci, hp, hpi, -, K, J, hK, hJ⟩ :=
    M64Uniformization.exists_positive_degree_one_homeomorph hd hdc
      (fun x => mul_pos hk (L.derivative_positive x)) hP hshift
  exact ⟨phi, fun x => congrFun hphi x, hm, hmi, hc, hci, hp, hpi, K, J, hK, hJ⟩



theorem coincident_degreeOneRamps_reparametrize
    (P : M62.CircleProductData F circumference) {gamma0 gamma1 : ℝ → P.charts.Point}
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (L0 : M63PositiveDegreeLift P gamma0) (L1 : M63PositiveDegreeLift P gamma1)
    (hd0 : L0.degree = 1) (hd1 : L1.degree = 1)
    (himage : range gamma0 = range gamma1) :
    ∃ sigma : M64PeriodicDegreeOneLift,
      ContDiff ℝ 1 sigma.map ∧ StrictMono sigma.map ∧ gamma0 ∘ sigma.map = gamma1 := by
  obtain ⟨phi0, he0, hm0, hmi0, hc0, hci0, hp0', hpi0, K0, J0, hK0, hJ0⟩ :=
    degreeOneRamp_phase_homeomorph P L0 hd0
  obtain ⟨phi1, he1, hm1, hmi1, hc1, hci1, hp1', hpi1, K1, J1, hK1, hJ1⟩ :=
    degreeOneRamp_phase_homeomorph P L1 hd1
  let sigma : M64PeriodicDegreeOneLift := {
    map := phi0.symm ∘ phi1
    monotone := hmi0.monotone.comp hm1.monotone
    period_shift := by
      intro x
      change phi0.symm (phi1 (x + curvePeriod)) = phi0.symm (phi1 x) + curvePeriod
      rw [hp1', hpi0]
    lipschitz_constant := J0 * K1
    lipschitz_nonnegative := (J0 * K1).property
    lipschitz_on := by
      intro x y
      simpa only [Real.dist_eq, NNReal.coe_mul] using (hJ0.comp hK1).dist_le_mul x y }
  refine ⟨sigma, hci0.comp hc1, hmi0.comp hm1, ?_⟩
  funext x
  have hscale : 0 < curvePeriod / circumference :=
    div_pos (by unfold curvePeriod; positivity) P.circle.positive
  have hphase : L0.lift (sigma.map x) = L1.lift x := by
    apply mul_left_cancel₀ hscale.ne'
    calc
      curvePeriod / circumference * L0.lift (sigma.map x) = phi0 (sigma.map x) :=
        (he0 _).symm
      _ = phi1 x := phi0.apply_symm_apply _
      _ = curvePeriod / circumference * L1.lift x := he1 x
  obtain ⟨y, hy⟩ := (show gamma1 x ∈ range gamma0 by rw [himage]; exact mem_range_self x)
  have hcircle : (gamma0 (sigma.map x)).2 = (gamma0 y).2 := by
    rw [← L0.quotient_eq, hphase, L1.quotient_eq, hy]
  exact (degreeOneRamp_eq_of_circle_eq P hp0 L0 hd0 hcircle).trans hy



theorem coincident_degreeOneRamps_zero_annulus [T2Space M]
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {gamma0 gamma1 : ℝ → P.charts.Point}
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 gamma0)
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (L0 : M63PositiveDegreeLift P gamma0) (L1 : M63PositiveDegreeLift P gamma1)
    (hd0 : L0.degree = 1) (hd1 : L1.degree = 1)
    (himage : range gamma0 = range gamma1) :
    ∃ A : M64Annulus (P.flow.metric t) gamma0 gamma1,
      A.area = 0 ∧ m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 = 0 := by
  obtain ⟨sigma, hsigma, -, htrace⟩ := coincident_degreeOneRamps_reparametrize
    P hp0 L0 L1 hd0 hd1 himage
  obtain ⟨A, -, hA⟩ := m64_zero_area_boundary_collar (P.flow.metric t) gamma0 sigma.map
    hc0.continuous hp0 (m64PeriodicC1Curve_metric_lipschitz (P.flow.metric t) hc0 hp0)
    hsigma.continuous sigma.period_shift
    ⟨sigma.lipschitz_constant, sigma.lipschitz_nonnegative, sigma.lipschitz_on⟩
  have hinf : m64LeastAnnulusArea (P.flow.metric t) gamma0 (gamma0 ∘ sigma.map) = 0 :=
    le_antisymm ((m64LeastAnnulusArea_le_annulus A).trans_eq hA)
      (m64LeastAnnulusArea_nonneg A)
  rw [← htrace]
  exact ⟨A, hA, hinf⟩

end PoincareConjecture.M64

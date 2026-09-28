import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusCurvatureConormal
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeLabelRegularity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeBoundaryTransport
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusBoundaryRegularity














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}





theorem m64CurvatureVector_comp_of_deriv_pos_at
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    {sigma : ℝ → ℝ} {t x : ℝ}
    (hc : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) (fun y => c y t))
    (hsigma : ContDiff ℝ 1 sigma) (hpos : 0 < deriv sigma x)
    (hS : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨c y t, spatialUnitTangent F c t y⟩ : TangentBundle (𝓡 n) M))
      (sigma x)) :
    m62CurvatureVector F (fun y s => c (sigma y) s) t x =
      m62CurvatureVector F c t (sigma x) := by
  have hnear : ∀ᶠ y in 𝓝 x, 0 < deriv sigma y :=
    hsigma.continuous_deriv_one.continuousAt (Ioi_mem_nhds hpos)
  have hunit : ∀ᶠ y in 𝓝 x,
      spatialUnitTangent F (fun z s => c (sigma z) s) t y =
        spatialUnitTangent F c t (sigma y) := by
    filter_upwards [hnear] with y hy
    exact M63.spatialUnitTangent_comp F c (hc (sigma y))
      ((hsigma.differentiable one_ne_zero) y).hasDerivAt hy
  have hcongr := M62.pullback_congr (F.connection t) hunit
  change (curveSpeed F (fun y s => c (sigma y) s) t x)⁻¹ •
    rampHorizontalCovariantDerivative (F.connection t) (fun y => c (sigma y) t)
      (spatialUnitTangent F (fun y s => c (sigma y) s) t) x = _
  rw [hcongr]
  exact M63.spatialDerivative_comp F c hS
    ((hsigma.differentiable one_ne_zero) x).hasDerivAt hpos

variable [T2Space M] [CompactSpace M]






theorem m64FreeAnnulus_modulus_boundary_conormal_factor
    (F : RicciFlow n M (Icc a b)) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric t) c0 c1)
    {r : ℝ} (hr : 0 < r)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (F.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (F.metric t) A.map p 1 1 ∧
        m60AreaGram (F.metric t) A.map p 0 1 = 0)
    (sigma : M64PeriodicDegreeOneLift) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hboundary : ∀ y, A.map (annulusPoint y s) = c (sigma.map y) t)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) curvePeriod) :
    let p := annulusPoint x s
    let E := m64ModulusEnergyDensity (F.metric t) r A.map p
    let J := (F.metric t).inner (A.map p)
      (m62CurvatureVector F c t (sigma.map x))
      (curveVelocity (fun z => A.map (annulusPoint x z)) s)
    E * J = -(1 / 2 : ℝ) *
      fderiv ℝ (m64ModulusEnergyDensity (F.metric t) r A.map) p
        (EuclideanSpace.single (1 : Fin 2) 1) ∧ (E = 0 → J = 0) := by
  let p := annulusPoint x s
  let E := m64ModulusEnergyDensity (F.metric t) r A.map
  let Z := curveVelocity (n := n) (fun z => A.map (annulusPoint x z)) s
  let J := (F.metric t).inner (A.map p) (m62CurvatureVector F c t (sigma.map x)) Z
  have hp : p ∈ m64AnnulusDomain := ⟨hx.1, hx.2, hs.1, hs.2⟩
  have hmd := (hA.contMDiffAt (hO.mem_nhds (hdom hp))).mdifferentiableAt (by simp)
  have hconf := m64Annulus_modulus_conformal_on_domain_of_ae A r hO hdom hA hconformal p hp
  have henergy : E p = r * m60AreaGram (F.metric t) A.map p 0 0 := by
    dsimp only [E, m64ModulusEnergyDensity]
    rw [← hconf.1]
    ring
  have hZsq : (F.metric t).inner (A.map p) Z Z =
      m60AreaGram (F.metric t) A.map p 1 1 := by
    dsimp only [Z, p]
    rw [m64Annulus_vertical_velocity hmd]
    simp only [m60AreaGram, EuclideanSpace.basisFun_apply]
  have hZzero (hE : E p = 0) : Z = 0 := by
    have h00 : m60AreaGram (F.metric t) A.map p 0 0 = 0 := by
      nlinarith [henergy]
    have h11 : m60AreaGram (F.metric t) A.map p 1 1 = 0 := by
      rw [h00, mul_zero] at hconf
      exact (mul_eq_zero.mp hconf.1.symm).resolve_left (inv_ne_zero hr.ne')
    by_contra hZ
    have hpos := (F.metric t).pos (A.map p) Z hZ
    rw [hZsq, h11] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  have hJzero (hE : E p = 0) : J = 0 := by
    simp only [J, hZzero hE, map_zero]
  change E p * J = _ ∧ (E p = 0 → J = 0)
  refine ⟨?_, hJzero⟩
  by_cases hE : E p = 0
  · have hacc := m64Annulus_modulus_acceleration_conormal_eq (F.connection t) A r
      hO hdom hA hconformal hp
    change r * (F.metric t).inner (A.map p) _ Z = _ at hacc
    rw [hZzero hE, map_zero, mul_zero] at hacc
    rw [hE, zero_mul]
    exact hacc
  · have hEpos : 0 < E p := lt_of_le_of_ne
      (m64ModulusEnergyDensity_nonneg r hr.le A.map p) (Ne.symm hE)
    have hanchor : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => c (sigma.map y) t) :=
      (m64Annulus_slice_contMDiff A hO hdom hA hs).congr (fun y => (hboundary y).symm)
    have hsigma2 := m64C2ShrinkingCurve_free_label_contDiff_two F hc ht
      (m64PeriodicDegreeOneLift_continuous_map sigma) hanchor
    have hsigma1 : ContDiff ℝ 1 sigma.map := hsigma2.of_le (by norm_num)
    have hcder := (hc.spatial_regular t ht).mdifferentiable (by norm_num)
    have hvel : curveVelocity (n := n) (fun y => A.map (annulusPoint y s)) x =
        deriv sigma.map x • curveVelocity (n := n) (fun y => c y t) (sigma.map x) := by
      rw [show (fun y => A.map (annulusPoint y s)) =
        (fun y => c (sigma.map y) t) from funext hboundary]
      exact M63.curveVelocity_comp (hcder (sigma.map x))
        ((hsigma1.differentiable one_ne_zero) x).hasDerivAt
    have hpos : 0 < deriv sigma.map x := by
      have hnonneg : 0 ≤ deriv sigma.map x := sigma.monotone.deriv_nonneg
      by_contra! hn
      have hzero : deriv sigma.map x = 0 := le_antisymm hn hnonneg
      have hcol : mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single (0 : Fin 2) 1) = 0 := by
        rw [← m64Annulus_horizontal_velocity hmd, hvel, hzero, zero_smul]
      have h00 : m60AreaGram (F.metric t) A.map p 0 0 = 0 := by
        simp only [m60AreaGram, EuclideanSpace.basisFun_apply, hcol, map_zero]
      rw [h00, mul_zero] at henergy
      exact hE henergy
    have hcurv := m64CurvatureVector_comp_of_deriv_pos_at F c hcder hsigma1 hpos
      (((M63.unitTangent_contMDiff_of_c2 F c (hc.spatial_regular t ht)
        (hc.immersed t ht)) (sigma.map x)).mdifferentiableAt one_ne_zero)
    have hlog := m64Annulus_modulus_curvature_conormal_eq F A hr hO hdom hA hconformal
      hp hEpos
    have hcurve : (fun y (_ : ℝ) => A.map (annulusPoint y s)) =
        (fun y _ => c (sigma.map y) t) := funext fun y => funext fun _ => hboundary y
    rw [hcurve] at hlog
    change (F.metric t).inner (A.map p)
      (m62CurvatureVector F (fun y z => c (sigma.map y) z) t x) Z = _ at hlog
    rw [hcurv] at hlog
    change J = -(1 / 2 : ℝ) *
      (fderiv ℝ E p (EuclideanSpace.single (1 : Fin 2) 1) / E p) at hlog
    rw [hlog]
    field_simp [hE]
    rfl

end PoincareConjecture

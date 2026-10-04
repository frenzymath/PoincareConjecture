import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.CoverRegular
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.ConjugateConformal

/-!
# The actual inverse covering metric

The normalized potential and conjugate have independent differential
coordinates. Applying the proved conjugate identity to the derivative of
their genuine inverse yields its anisotropic conformal pullback metric.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

/-- The planar inverse of the actual normalized covering chart. Source: Morgan--Tian (2007),
Lemma 19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
def scalarInverseCoverMap (e : OpenPartialHomeomorph Cover Cover) : Cover → Plane :=
  scalarCoverMap ∘ e.symm

/-- The inverse polar map is smooth on the actual target of the chart. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarInverseCoverMap_smooth (e : OpenPartialHomeomorph Cover Cover)
    (hei : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (scalarInverseCoverMap e) e.target := by
  intro y hy
  exact (scalarCoverMap_smooth.contDiffAt.comp y
    (hei.contDiffAt (e.open_target.mem_nhds hy))).contDiffWithinAt

/-- The genuine inverse respects the deck shift because the actual covering chart is
injective on its source. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit
project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarInverseCoverMap_periodic (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (htarget : e.target = scalarPotentialStrip)
    (hdeck : ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1))
    {y : Cover} (hy : y ∈ e.target) :
    scalarInverseCoverMap e (y + (0, 1)) = scalarInverseCoverMap e y := by
  have hy' : y + (0, 1) ∈ e.target := by
    rw [htarget] at hy ⊢
    simpa [scalarPotentialStrip] using hy
  have hz : e.symm y ∈ e.source := e.map_target hy
  have hz' : e.symm y + (0, 1) ∈ e.source := by
    rw [hsource] at hz ⊢
    simpa [scalarCoverStrip] using hz
  have hinv : e.symm (y + (0, 1)) = e.symm y + (0, 1) := by
    apply e.injOn (e.map_target hy') hz'
    rw [e.right_inv hy', hdeck _ hz, e.right_inv hy]
  simp only [scalarInverseCoverMap, Function.comp_apply, hinv, scalarCoverMap_periodic]

/-- The two rows of the normalized covering differential are the actual potential
differential and the normalized conjugate form. Source: Morgan--Tian (2007), Lemma 19.15,
pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarNormalizedCoverMap_fderiv_apply {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    (P : ℝ) {z : Cover} (hz : z ∈ scalarCoverStrip) (v : Cover) :
    fderiv ℝ (scalarNormalizedCoverMap H V P) z v =
      (fderiv ℝ H (scalarCoverMap z) (fderiv ℝ scalarCoverMap z v),
        scalarConjugateForm D H (scalarCoverMap z) (fderiv ℝ scalarCoverMap z v) / P) := by
  have hHc : ContDiffAt ℝ ∞ H (scalarCoverMap z) := contMDiffAt_iff_contDiffAt.mp
    (hHs.contMDiffAt (scalarAnnulus_isOpen.mem_nhds (scalarCoverMap_mem hz)))
  have hH := (hHc.differentiableAt (by simp)).hasFDerivAt
  have hC := (scalarCoverMap_smooth.differentiable (by simp) z).hasFDerivAt
  have hVnorm : HasFDerivAt (fun y => V y / P) (P⁻¹ • scalarCoverForm D H z) z := by
    convert! (hdV z hz).const_smul P⁻¹ using 1
    ext y
    simp [div_eq_mul_inv, mul_comm]
  have hF := (hH.comp z hC).prodMk hVnorm
  change HasFDerivAt (scalarNormalizedCoverMap H V P) _ z at hF
  rw [hF.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    smul_apply, smul_eq_mul, scalarCoverForm, div_eq_mul_inv, mul_comm]

/-- The inverse has the literal differential coordinates `(ds,P*dtheta)`; these equations
come from differentiating the genuine inverse identity. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarInverseCoverMap_coordinates {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    (P : ℝ) (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P)
    (hes : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {y : Cover} (hy : y ∈ e.target) (v : Cover) :
    (fderiv ℝ H (scalarInverseCoverMap e y)
        (fderiv ℝ (scalarInverseCoverMap e) y v),
      scalarConjugateForm D H (scalarInverseCoverMap e y)
        (fderiv ℝ (scalarInverseCoverMap e) y v) / P) = v := by
  have hz : e.symm y ∈ e.source := e.map_target hy
  have hz' : e.symm y ∈ scalarCoverStrip := hsource ▸ hz
  have hed := (hes.contDiffAt (e.open_source.mem_nhds hz)).differentiableAt (by simp)
  have heid := (hei.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  have hcomp : (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) =
      ContinuousLinearMap.id ℝ Cover := by
    rw [← fderiv_comp y hed heid]
    have heq : (e : Cover → Cover) ∘ e.symm =ᶠ[𝓝 y] id := by
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      exact e.right_inv hz
    simpa only [fderiv_id] using heq.fderiv_eq (𝕜 := ℝ)
  have hF : fderiv ℝ (scalarInverseCoverMap e) y =
      (fderiv ℝ scalarCoverMap (e.symm y)).comp (fderiv ℝ e.symm y) :=
    fderiv_comp y (scalarCoverMap_smooth.differentiable (by simp) _) heid
  have h := congrArg (fun A : Cover →L[ℝ] Cover => A v) hcomp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  rw [he, scalarNormalizedCoverMap_fderiv_apply D hHs hdV P hz'] at h
  rw [hF]
  exact h

/-- The retained source metric in inverse potential-conjugate coordinates. The formula is
derived from the actual harmonic conjugate, including its normalization by the conserved
period. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project
construction is recorded in `proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarInverseCoverMap_metric_identity {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : P ≠ 0) (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P)
    (hes : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {y : Cover} (hy : y ∈ e.target) (v w : Cover) :
    g.inner (scalarInverseCoverMap e y)
        (D.gradient H (scalarInverseCoverMap e y))
        (D.gradient H (scalarInverseCoverMap e y)) *
      g.inner (scalarInverseCoverMap e y)
        (fderiv ℝ (scalarInverseCoverMap e) y v)
        (fderiv ℝ (scalarInverseCoverMap e) y w) =
      v.1 * w.1 + P ^ 2 * v.2 * w.2 := by
  have hv := scalarInverseCoverMap_coordinates D hHs hdV P e hsource he hes hei hy v
  have hw := scalarInverseCoverMap_coordinates D hHs hdV P e hsource he hes hei hy w
  have hv0 := congrArg Prod.fst hv
  have hw0 := congrArg Prod.fst hw
  dsimp only at hv0 hw0
  have hv1 : scalarConjugateForm D H (scalarInverseCoverMap e y)
      (fderiv ℝ (scalarInverseCoverMap e) y v) = v.2 * P :=
    (div_eq_iff hP).mp (congrArg Prod.snd hv)
  have hw1 : scalarConjugateForm D H (scalarInverseCoverMap e y)
      (fderiv ℝ (scalarInverseCoverMap e) y w) = w.2 * P :=
    (div_eq_iff hP).mp (congrArg Prod.snd hw)
  rw [← scalarConjugateForm_metric_identity D H, hv0, hw0, hv1, hw1]
  ring

/-- The actual inverse differential is injective, directly from its two differential
coordinates. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project
construction is recorded in `proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarInverseCoverMap_fderiv_injective {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    (P : ℝ) (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P)
    (hes : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {y : Cover} (hy : y ∈ e.target) :
    Function.Injective (fderiv ℝ (scalarInverseCoverMap e) y) := by
  intro v w hvw
  have hv := scalarInverseCoverMap_coordinates D hHs hdV P e hsource he hes hei hy v
  have hw := scalarInverseCoverMap_coordinates D hHs hdV P e hsource he hes hei hy w
  rw [hvw] at hv
  exact hv.symm.trans hw

end PoincareMT.M64Uniformization

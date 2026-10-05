import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.LocalizedSource

/-!
# Rectangle preservation for actual localized source changes

The derivative bound makes every horizontal slice strictly increasing.
The fixed seam faces then force preservation of the whole rectangle,
while arbitrary radial cutoffs remain available at the two boundaries.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT

local notation "S" => interior m64AnnulusDomain
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/-- The actual horizontal source slice has the derivative supplied by the source
differential. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-26-raw-harmonic-stress.md`. -/
theorem m64Source_horizontalSlice_hasDerivAt
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T) (x s : ℝ) :
    HasDerivAt (fun y => T (annulusPoint y s) 0)
      (fderiv ℝ T (annulusPoint x s) e0 0) x := by
  have hline : HasDerivAt (fun y : ℝ => annulusPoint y s) e0 x := by
    convert! ((hasDerivAt_id x).smul_const e0).add_const (s • e1) using 1
    · funext y
      ext i
      fin_cases i <;> simp [annulusPoint]
    · simp
  have hcurve := (hT (annulusPoint x s)).hasFDerivAt.comp_hasDerivAt x hline
  exact (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
    x hcurve

/-- A source differential within one half of the identity has positive horizontal entry.
Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-26-raw-harmonic-stress.md`. -/
theorem m64Source_horizontal_derivative_pos
    {T : LoopPlane → LoopPlane}
    (hclose : ∀ p, ‖fderiv ℝ T p - ContinuousLinearMap.id ℝ LoopPlane‖ ≤ 1 / 2)
    (p : LoopPlane) : 0 < fderiv ℝ T p e0 0 := by
  have hop := (fderiv ℝ T p - ContinuousLinearMap.id ℝ LoopPlane).le_opNorm e0
  have hnorm : ‖e0‖ = 1 := by simp
  rw [hnorm, mul_one] at hop
  have hc := (PiLp.norm_apply_le
    ((fderiv ℝ T p - ContinuousLinearMap.id ℝ LoopPlane) e0) (0 : Fin 2)).trans
      (hop.trans (hclose p))
  have hfirst : |fderiv ℝ T p e0 0 - 1| ≤ 1 / 2 := by
    simpa only [sub_apply, ContinuousLinearMap.id_apply, PiLp.sub_apply,
      PiLp.single_apply, ite_true, Real.norm_eq_abs] using hc
  have hh := (abs_le.mp hfirst).1
  linarith

/-- A source differential close to the identity makes every horizontal slice increasing.
Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-26-raw-harmonic-stress.md`. -/
theorem m64Source_horizontalSlice_strictMono
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T)
    (hclose : ∀ p, ‖fderiv ℝ T p - ContinuousLinearMap.id ℝ LoopPlane‖ ≤ 1 / 2)
    (s : ℝ) : StrictMono (fun x => T (annulusPoint x s) 0) :=
  strictMono_of_hasDerivAt_pos (fun x => m64Source_horizontalSlice_hasDerivAt hT x s)
    (fun x => m64Source_horizontal_derivative_pos hclose (annulusPoint x s))

/-- An increasing triangular map fixing the angular faces preserves the annular interior.
Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-26-raw-harmonic-stress.md`. -/
theorem m64TriangularSource_preimage_interior
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T)
    (hclose : ∀ p, ‖fderiv ℝ T p - ContinuousLinearMap.id ℝ LoopPlane‖ ≤ 1 / 2)
    (hsecond : ∀ p, T p 1 = p 1)
    (hzero : ∀ s, T (annulusPoint 0 s) = annulusPoint 0 s)
    (hperiod : ∀ s, T (annulusPoint curvePeriod s) = annulusPoint curvePeriod s) :
    T ⁻¹' S = S := by
  ext p
  have hpoint : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  have hm := m64Source_horizontalSlice_strictMono hT hclose (p 1)
  have h0 : T (annulusPoint 0 (p 1)) 0 = 0 := by rw [hzero]; rfl
  have hP : T (annulusPoint curvePeriod (p 1)) 0 = curvePeriod := by rw [hperiod]; rfl
  have hlo : 0 < T p 0 ↔ 0 < p 0 := by
    simpa only [h0, hpoint] using hm.lt_iff_lt (a := 0) (b := p 0)
  have hhi : T p 0 < curvePeriod ↔ p 0 < curvePeriod := by
    simpa only [hP, hpoint] using hm.lt_iff_lt (a := p 0) (b := curvePeriod)
  simp only [mem_preimage, m64AnnulusInterior_coordinates, hsecond, hlo, hhi]

/-- Small localized horizontal variations are actual smooth rectangle-preserving
diffeomorphisms. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-26-raw-harmonic-stress.md`. -/
theorem m64_exists_localized_horizontal_rectangle_source
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod) (hzero : eta 0 = 0)
    (hrho : ContDiff ℝ ∞ rho) (hcompact : HasCompactSupport rho) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, |t| < delta →
      ∃ T : LoopPlane ≃ₜ LoopPlane,
        (∀ x s, T (annulusPoint x s) = annulusPoint (x + t * eta x * rho s) s) ∧
        ContDiff ℝ ∞ T ∧ ContDiff ℝ ∞ T.symm ∧
        (∀ p, ‖fderiv ℝ T p - ContinuousLinearMap.id ℝ LoopPlane‖ ≤ 1 / 2) ∧
        T ⁻¹' S = S ∧
        (∀ s, StrictMono (fun x => T (annulusPoint x s) 0)) ∧
        (∀ s, T (annulusPoint 0 s) = annulusPoint 0 s) ∧
        (∀ s, T (annulusPoint curvePeriod s) = annulusPoint curvePeriod s) ∧
        ∀ x s, T (annulusPoint (x + curvePeriod) s) =
          T (annulusPoint x s) + annulusPoint curvePeriod 0 := by
  obtain ⟨delta, hd, hvar⟩ := m64_exists_smooth_localized_horizontal_source
    heta hperiod hrho hcompact
  refine ⟨delta, hd, ?_⟩
  intro t ht
  obtain ⟨T, hT, hs, hi, hclose⟩ := hvar t ht
  have hpoint (x s : ℝ) : T (annulusPoint x s) =
      annulusPoint (x + t * eta x * rho s) s := by
    rw [hT]
    ext i
    fin_cases i <;> simp [annulusPoint, mul_assoc]
  have hzeroT (s : ℝ) : T (annulusPoint 0 s) = annulusPoint 0 s := by
    rw [hpoint, hzero]
    simp
  have hetaP : eta curvePeriod = 0 := by simpa only [zero_add, hzero] using hperiod 0
  have hperiodT (s : ℝ) : T (annulusPoint curvePeriod s) = annulusPoint curvePeriod s := by
    rw [hpoint, hetaP]
    simp
  have hsecond (p : LoopPlane) : T p 1 = p 1 := by
    rw [hT]
    simp
  refine ⟨T, hpoint, hs, hi, hclose,
    m64TriangularSource_preimage_interior (hs.differentiable (by simp)) hclose
      hsecond hzeroT hperiodT,
    fun s => m64Source_horizontalSlice_strictMono (hs.differentiable (by simp)) hclose s,
    hzeroT, hperiodT, ?_⟩
  intro x s
  rw [hpoint, hpoint, hperiod]
  ext i
  fin_cases i <;> simp [annulusPoint]
  ring

end PoincareMT

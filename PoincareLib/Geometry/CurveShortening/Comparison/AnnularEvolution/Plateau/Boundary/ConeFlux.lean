import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.ConeFields

/-!
# Actual polar flux derivatives in arbitrary dimension

The coordinate-dependent calculation from M65 `InteriorRegularityConeFlux`
is generalized to a proper real Banach coordinate space. Its generic
AC composition, interpolation and polar transport lemmas are reused
from the independent authorized M65 closure. Source: Morrey ICM 1950,
pp. 183-185; M64 derivation `2026-09-26-general-half-cone.md`.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal InnerProductSpace

namespace PoincareMT.M64BoundaryCone

open M65Interior

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- The actual radial cone flux includes its polar Jacobian. Proof expansion for Morgan-Tian
(2007), Lemma 19.15, pp. 447-449; M64 derivation 2026-09-26-general-half-cone.md. -/
noncomputable def coneRadialFlux (g : C → ℝ)
    (r : ℝ) (v0 : C) (v : ℝ → C)
    (x : LoopPlane) (test : LoopPlane → ℝ) (i : Fin 2) (s θ : ℝ) : ℝ :=
  s * Proofs.M58.angularPoint θ i * g (coneCoordinates r v0 v s θ) *
    test (polarPlane x (s, θ))

/-- The actual angular cone flux has no radial Jacobian factor. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-general-half-cone.md. -/
noncomputable def coneAngularFlux (g : C → ℝ)
    (r : ℝ) (v0 : C) (v : ℝ → C)
    (x : LoopPlane) (test : LoopPlane → ℝ) (i : Fin 2) (s θ : ℝ) : ℝ :=
  Proofs.M58.angularVector θ i * g (coneCoordinates r v0 v s θ) *
    test (polarPlane x (s, θ))

private theorem polar_frame_coordinate (A : LoopPlane →L[ℝ] ℝ) (θ : ℝ) (i : Fin 2) :
    Proofs.M58.angularPoint θ i * A (Proofs.M58.angularPoint θ) +
      Proofs.M58.angularVector θ i * A (Proofs.M58.angularVector θ) =
        A (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  have hframe : Proofs.M58.angularPoint θ i • Proofs.M58.angularPoint θ +
      Proofs.M58.angularVector θ i • Proofs.M58.angularVector θ =
        EuclideanSpace.basisFun (Fin 2) ℝ i := by
    ext j
    fin_cases i <;> fin_cases j <;>
      simp [Proofs.M58.angularPoint, Proofs.M58.angularVector, EuclideanSpace.single] <;>
      nlinarith [Real.cos_sq_add_sin_sq θ]
  calc
    _ = A (Proofs.M58.angularPoint θ i • Proofs.M58.angularPoint θ +
        Proofs.M58.angularVector θ i • Proofs.M58.angularVector θ) := by
      simp only [map_add, map_smul, smul_eq_mul]
    _ = _ := congrArg A hframe

/-- The radial flux has its genuine derivative even at radius zero. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-general-half-cone.md. -/
theorem coneRadialFlux_hasDerivAt {g : C → ℝ}
    (r : ℝ) (v0 : C) (v : ℝ → C)
    (x : LoopPlane) (test : LoopPlane → ℝ) (i : Fin 2) (s θ : ℝ)
    (hg : DifferentiableAt ℝ g (coneCoordinates r v0 v s θ))
    (ht : DifferentiableAt ℝ test (polarPlane x (s, θ))) :
    HasDerivAt (fun q => coneRadialFlux g r v0 v x test i q θ)
      (Proofs.M58.angularPoint θ i * g (coneCoordinates r v0 v s θ) *
          test (polarPlane x (s, θ)) +
        s * Proofs.M58.angularPoint θ i *
          (r⁻¹ * fderiv ℝ g (coneCoordinates r v0 v s θ) (v θ - v0) *
              test (polarPlane x (s, θ)) +
            g (coneCoordinates r v0 v s θ) *
              fderiv ℝ test (polarPlane x (s, θ)) (Proofs.M58.angularPoint θ))) s := by
  have hp : HasDerivAt (fun q => polarPlane x (q, θ)) (Proofs.M58.angularPoint θ) s := by
    simpa only [polarPlane, one_smul, id_eq] using
      ((hasDerivAt_id s).smul_const (Proofs.M58.angularPoint θ)).const_add x
  have htest := ht.hasFDerivAt.comp_hasDerivAt s hp
  have hcone := cone_reconstruction_radial r v0 v s θ hg
  have hprod := (((hasDerivAt_id s).mul_const (Proofs.M58.angularPoint θ i)).mul
    hcone).mul htest
  change HasDerivAt (fun q => coneRadialFlux g r v0 v x test i q θ) _ s at hprod
  convert! hprod using 1
  simp only [Function.comp_def, Pi.mul_apply, smul_eq_mul, one_mul, id_eq]
  ring

/-- The actual circle derivative gives the genuine angular cone flux derivative. The
derivative is not inferred from a value on a null circle. Proof expansion for Morgan-Tian
(2007), Lemma 19.15, pp. 447-449; M64 derivation 2026-09-26-general-half-cone.md. -/
theorem coneAngularFlux_hasDerivAt {g : C → ℝ}
    (r : ℝ) (v0 : C)
    (v d : ℝ → C) (x : LoopPlane)
    (test : LoopPlane → ℝ) (i : Fin 2) (s θ : ℝ)
    (hv : HasDerivAt v (d θ) θ)
    (hg : DifferentiableAt ℝ g (coneCoordinates r v0 v s θ))
    (ht : DifferentiableAt ℝ test (polarPlane x (s, θ))) :
    HasDerivAt (fun q => coneAngularFlux g r v0 v x test i s q)
      (-Proofs.M58.angularPoint θ i * g (coneCoordinates r v0 v s θ) *
          test (polarPlane x (s, θ)) +
        Proofs.M58.angularVector θ i *
          ((s / r) * fderiv ℝ g (coneCoordinates r v0 v s θ) (d θ) *
              test (polarPlane x (s, θ)) +
            g (coneCoordinates r v0 v s θ) * s *
              fderiv ℝ test (polarPlane x (s, θ)) (Proofs.M58.angularVector θ))) θ := by
  have hc : HasDerivAt (fun q => coneCoordinates r v0 v s q) ((s / r) • d θ) θ := by
    simpa +instances only [coneCoordinates, Pi.smul_apply] using!
      ((hv.sub_const v0).const_smul (s / r)).const_add v0
  have hcone := hg.hasFDerivAt.comp_hasDerivAt θ hc
  have hp : HasDerivAt (fun q => polarPlane x (s, q)) (s • Proofs.M58.angularVector θ) θ :=
    ((Proofs.M58.hasDerivAt_angularPoint θ).const_smul s).const_add x
  have htest := ht.hasFDerivAt.comp_hasDerivAt θ hp
  have hτ := (EuclideanSpace.proj i : LoopPlane →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt θ
    (m65AngularVector_hasDerivAt θ)
  change HasDerivAt (fun q => Proofs.M58.angularVector q i) (-Proofs.M58.angularPoint θ i) θ at hτ
  have hprod := (hτ.mul hcone).mul htest
  change HasDerivAt (fun q => coneAngularFlux g r v0 v x test i s q) _ θ at hprod
  convert! hprod using 1
  simp only [Function.comp_def, Pi.mul_apply, map_smul, smul_eq_mul]
  ring

/-- The two genuine polar derivatives recover exactly the Cartesian Green integrand of the
literal cone field. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64
derivation 2026-09-26-general-half-cone.md. -/
theorem coneFlux_derivative_sum {g : C → ℝ}
    (r : ℝ) (v0 : C)
    (v d : ℝ → C) (x : LoopPlane)
    (test : LoopPlane → ℝ) (i : Fin 2) (s θ : ℝ)
    (hv : HasDerivAt v (d θ) θ)
    (hg : DifferentiableAt ℝ g (coneCoordinates r v0 v s θ))
    (ht : DifferentiableAt ℝ test (polarPlane x (s, θ))) :
    deriv (fun q => coneRadialFlux g r v0 v x test i q θ) s +
        deriv (fun q => coneAngularFlux g r v0 v x test i s q) θ =
      s * (coneCartesianField g r v0 v d s θ i * test (polarPlane x (s, θ)) +
        g (coneCoordinates r v0 v s θ) *
          fderiv ℝ test (polarPlane x (s, θ)) (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  rw [(coneRadialFlux_hasDerivAt r v0 v x test i s θ hg ht).deriv,
    (coneAngularFlux_hasDerivAt r v0 v d x test i s θ hv hg ht).deriv]
  simp only [coneCartesianField, smul_eq_mul, div_eq_mul_inv]
  have hframe := polar_frame_coordinate (fderiv ℝ test (polarPlane x (s, θ))) θ i
  linear_combination s * g (coneCoordinates r v0 v s θ) * hframe

end PoincareMT.M64BoundaryCone

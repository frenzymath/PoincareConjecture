import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.InteriorWeightedVariation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Area-preserving source rescaling for the weak modulus equation

The two reciprocal source factors turn the modulus-weighted Dirichlet
form into its ordinary form. The actual distributional columns and
restricted integrals are transported by the same linear equivalence.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT

open Poincare.Analysis.Sobolev.Weak

/-- The reciprocal coordinate factors of the determinant-one source rescaling. Source:
Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
def m64SourceScaleFactor (s : ℝ) (i : Fin 2) : ℝ := if i = 0 then s else s⁻¹

/-- The actual reciprocal diagonal source linear equivalence. Source: Morgan-Tian Lemma
19.15, pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
def m64SourceScale (s : ℝ) (hs : s ≠ 0) : LoopPlane ≃L[ℝ] LoopPlane :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun p => (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun i => m64SourceScaleFactor s i * p i)
    invFun := fun p => (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun i => (m64SourceScaleFactor s i)⁻¹ * p i)
    map_add' := by intros; ext i; simp [mul_add]
    map_smul' := by intros; ext i; simp [mul_left_comm]
    left_inv := by
      intro p
      ext i
      change (m64SourceScaleFactor s i)⁻¹ * (m64SourceScaleFactor s i * p i) = p i
      simp only [m64SourceScaleFactor]
      split_ifs <;> simp [hs]
    right_inv := by
      intro p
      ext i
      change m64SourceScaleFactor s i * ((m64SourceScaleFactor s i)⁻¹ * p i) = p i
      simp only [m64SourceScaleFactor]
      split_ifs <;> simp [hs] }

/-- The source rescaling acts coordinatewise by its reciprocal factors. Source: Morgan-Tian
Lemma 19.15, pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
theorem m64SourceScale_apply (s : ℝ) (hs : s ≠ 0) (p : LoopPlane) (i : Fin 2) :
    m64SourceScale s hs p i = m64SourceScaleFactor s i * p i := rfl

/-- The inverse source rescaling acts by inverse factors. Source: Morgan-Tian Lemma 19.15,
pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
theorem m64SourceScale_symm_apply (s : ℝ) (hs : s ≠ 0) (p : LoopPlane) (i : Fin 2) :
    (m64SourceScale s hs).symm p i = (m64SourceScaleFactor s i)⁻¹ * p i := rfl

/-- The source rescaling multiplies each standard basis vector by its coordinate factor.
Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-26-raw-harmonic-stress.md`. -/
theorem m64SourceScale_basis (s : ℝ) (hs : s ≠ 0) (i : Fin 2) :
    m64SourceScale s hs (EuclideanSpace.single i 1) =
      m64SourceScaleFactor s i • EuclideanSpace.single i 1 := by
  ext j
  by_cases hij : i = j
  · subst j; simp [m64SourceScale_apply]
  · simp [m64SourceScale_apply, Ne.symm hij]

/-- The reciprocal source rescaling has determinant one. Source: Morgan-Tian Lemma 19.15,
pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
theorem m64SourceScale_det (s : ℝ) (hs : s ≠ 0) :
    LinearMap.det (m64SourceScale s hs).toLinearMap = 1 := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, m64SourceScale_apply, m64SourceScaleFactor, hs]

/-- The reciprocal source rescaling preserves plane volume. Source: Morgan-Tian Lemma 19.15,
pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
theorem m64SourceScale_measurePreserving (s : ℝ) (hs : s ≠ 0) :
    MeasurePreserving (m64SourceScale s hs) volume volume := by
  refine ⟨(m64SourceScale s hs).continuous.measurable, ?_⟩
  have hd : LinearMap.det (m64SourceScale s hs).toLinearMap ≠ 0 := by
    rw [m64SourceScale_det]; exact one_ne_zero
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure LoopPlane) hd
  simp only [m64SourceScale_det, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  exact h

/-- The source rescaling preserves the corresponding restricted volume. Source: Morgan-Tian
Lemma 19.15, pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
theorem m64SourceScale_restrict_measurePreserving (s : ℝ) (hs : s ≠ 0)
    (O : Set LoopPlane) :
    MeasurePreserving (m64SourceScale s hs)
      (volume.restrict ((m64SourceScale s hs) ⁻¹' O)) (volume.restrict O) :=
  (m64SourceScale_measurePreserving s hs).restrict_preimage_emb
    (m64SourceScale s hs).toHomeomorph.measurableEmbedding O

/-- The source rescaling transports the actual restricted integral. Source: Morgan-Tian
Lemma 19.15, pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
theorem m64SourceScale_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (s : ℝ) (hs : s ≠ 0) (O : Set LoopPlane) (f : LoopPlane → E) :
    (∫ p in (m64SourceScale s hs) ⁻¹' O, f (m64SourceScale s hs p)) = ∫ p in O, f p :=
  (m64SourceScale_restrict_measurePreserving s hs O).integral_comp
    (m64SourceScale s hs).toHomeomorph.measurableEmbedding f

/-- The classical derivative of a rescaled composition has the actual coordinate factor.
Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-26-raw-harmonic-stress.md`. -/
theorem m64SourceScale_fderiv_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℝ) (hs : s ≠ 0) {f : LoopPlane → E} (hf : Differentiable ℝ f)
    (p : LoopPlane) (i : Fin 2) :
    fderiv ℝ (f ∘ m64SourceScale s hs) p (EuclideanSpace.single i 1) =
      m64SourceScaleFactor s i •
        fderiv ℝ f (m64SourceScale s hs p) (EuclideanSpace.single i 1) := by
  rw [fderiv_comp p (hf _) (m64SourceScale s hs).differentiableAt,
    ContinuousLinearMap.comp_apply, (m64SourceScale s hs).fderiv]
  change fderiv ℝ f (m64SourceScale s hs p)
    (m64SourceScale s hs (EuclideanSpace.single i 1)) = _
  rw [m64SourceScale_basis, map_smul]

/-- Weak partial derivatives transform by the reciprocal source factors. Source: Morgan-Tian
Lemma 19.15, pp. 447-449; M64 derivation `2026-09-26-raw-harmonic-stress.md`. -/
theorem m64SourceScale_weakPartial {O : Set LoopPlane} {u V : LoopPlane → ℝ}
    {i : Fin 2} (hw : HasWeakPartialDeriv i V u O) (s : ℝ) (hs : s ≠ 0) :
    HasWeakPartialDeriv i
      (fun p => m64SourceScaleFactor s i * V (m64SourceScale s hs p))
      (u ∘ m64SourceScale s hs) ((m64SourceScale s hs) ⁻¹' O) := by
  intro phi hp hc hsupport
  let D := m64SourceScale s hs
  let psi := phi ∘ D.symm
  have hpc : ContDiff ℝ ∞ psi := hp.comp D.symm.contDiff
  have hps : tsupport psi ⊆ O := by
    change tsupport (phi ∘ D.toHomeomorph.symm) ⊆ O
    rw [tsupport_comp_eq_preimage]
    intro p h
    have hpD := hsupport h
    change D (D.symm p) ∈ O at hpD
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hpD
  have hcomp : psi ∘ D = phi := by funext p; simp [psi]
  have hd (p : LoopPlane) :
      m64SourceScaleFactor s i * fderiv ℝ psi (D p) (EuclideanSpace.single i 1) =
        fderiv ℝ phi p (EuclideanSpace.single i 1) := by
    have h := m64SourceScale_fderiv_comp s hs (hpc.differentiable (by simp)) p i
    rw [hcomp] at h
    exact h.symm
  have hleft :
      (∫ p in D ⁻¹' O, u (D p) * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        m64SourceScaleFactor s i * ∫ p in O, u p * fderiv ℝ psi p (EuclideanSpace.single i 1) := by
    simp_rw [← hd]
    simp_rw [show ∀ p, u (D p) *
      (m64SourceScaleFactor s i * fderiv ℝ psi (D p) (EuclideanSpace.single i 1)) =
        m64SourceScaleFactor s i * (u (D p) * fderiv ℝ psi (D p) (EuclideanSpace.single i 1))
      from fun p => by ring]
    rw [integral_const_mul]
    exact congrArg (fun z : ℝ => m64SourceScaleFactor s i * z)
      (m64SourceScale_integral s hs O
        (fun p => u p * fderiv ℝ psi p (EuclideanSpace.single i 1)))
  have hright :
      (∫ p in D ⁻¹' O, (m64SourceScaleFactor s i * V (D p)) * phi p) =
        m64SourceScaleFactor s i * ∫ p in O, V p * psi p := by
    calc
      _ = ∫ p in D ⁻¹' O, m64SourceScaleFactor s i * (V (D p) * psi (D p)) := by
        apply integral_congr_ae
        filter_upwards [] with p
        have hpp : psi (D p) = phi p := congrFun hcomp p
        rw [hpp]
        ring
      _ = _ := by
        rw [integral_const_mul]
        exact congrArg (fun z : ℝ => m64SourceScaleFactor s i * z)
          (m64SourceScale_integral s hs O (fun p => V p * psi p))
  change (∫ p in D ⁻¹' O, u (D p) * fderiv ℝ phi p (EuclideanSpace.single i 1)) = _
  rw [hleft, hright, hw psi hpc (hc.comp_homeomorph D.symm.toHomeomorph) hps, mul_neg]

end PoincareMT

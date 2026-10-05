import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Source.AffineGeometry
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Source.ScaleStress

/-! Classical derivatives, quadratic forcing and Gram entries under
the actual translated modulus normalization. Source: Morrey boundary
coordinates; M64 finite-boundary-regularity derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareMT

/-- Translated normalization is ordinary translation after the original reciprocal diagonal
normalization. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64SourceAffine_comp {E : Type*} (f : LoopPlane → E)
    (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) :
    f ∘ m64SourceAffine a s hs = fun z =>
      (f ∘ m64SourceScale s hs) ((m64SourceScale s hs).symm a + z) := by
  funext z
  simp only [Function.comp_apply, map_add, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The actual first derivative is the translated normalized derivative. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64SourceAffine_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : LoopPlane → E) (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) (p : LoopPlane) :
    fderiv ℝ (f ∘ m64SourceAffine a s hs) p =
      fderiv ℝ (f ∘ m64SourceScale s hs) ((m64SourceScale s hs).symm a + p) := by
  rw [m64SourceAffine_comp, fderiv_comp_add_left]

/-- Both actual derivative orders commute with the translation. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64SourceAffine_second_fderiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : LoopPlane → E) (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) (p : LoopPlane) :
    fderiv ℝ (fderiv ℝ (f ∘ m64SourceAffine a s hs)) p =
      fderiv ℝ (fderiv ℝ (f ∘ m64SourceScale s hs))
        ((m64SourceScale s hs).symm a + p) := by
  have hfirst : fderiv ℝ (f ∘ m64SourceAffine a s hs) = fun z =>
      fderiv ℝ (f ∘ m64SourceScale s hs) ((m64SourceScale s hs).symm a + z) :=
    funext (m64SourceAffine_fderiv f a s hs)
  rw [hfirst, fderiv_comp_add_left]

/-- The same quadratic forcing constant works after centering at any physical boundary
point. No smoothness outside the original domain is used. Proof expansion for Morgan-Tian
(2007), Lemma 19.15, pp. 447-449. -/
theorem m64SourceAffine_quadratic_growth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : LoopPlane → E) (a : LoopPlane) (s : ℝ) (hs : s ≠ 0)
    {O : Set LoopPlane} {C : ℝ}
    (hgrowth : ∀ p ∈ m64SourceScale s hs ⁻¹' O,
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ (f ∘ m64SourceScale s hs)) p
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
        C * ∑ i : Fin 2, ‖fderiv ℝ (f ∘ m64SourceScale s hs) p
          (EuclideanSpace.single i 1)‖ ^ 2) :
    ∀ p ∈ m64SourceAffine a s hs ⁻¹' O,
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ (f ∘ m64SourceAffine a s hs)) p
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
        C * ∑ i : Fin 2, ‖fderiv ℝ (f ∘ m64SourceAffine a s hs) p
          (EuclideanSpace.single i 1)‖ ^ 2 := by
  intro p hp
  simp only [m64SourceAffine_second_fderiv, m64SourceAffine_fderiv]
  apply hgrowth
  change m64SourceScale s hs ((m64SourceScale s hs).symm a + p) ∈ O
  change a + m64SourceScale s hs p ∈ O at hp
  simpa only [map_add, ContinuousLinearEquiv.apply_symm_apply] using hp

/-- The genuine intrinsic Gram entries acquire precisely the two source factors. This
identity includes vanishing derivatives. Proof expansion for Morgan-Tian (2007), Lemma
19.15, pp. 447-449. -/
theorem m64AreaGram_sourceAffine {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (a : LoopPlane) (s : ℝ) (hs : s ≠ 0)
    {f : LoopPlane → M} {p : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (m64SourceAffine a s hs p)) (i j : Fin 2) :
    m60AreaGram g (f ∘ m64SourceAffine a s hs) p i j =
      m64SourceScaleFactor s i * m64SourceScaleFactor s j *
        m60AreaGram g f (m64SourceAffine a s hs p) i j := by
  let Phi := m64SourceAffine a s hs
  let D := m64SourceScale s hs
  have hPhi : HasFDerivAt Phi D.toContinuousLinearMap p := D.hasFDerivAt.const_add a
  have hd := mfderiv_comp p hf
    (mdifferentiableAt_iff_differentiableAt.mpr hPhi.differentiableAt)
  rw [mfderiv_eq_fderiv, hPhi.fderiv] at hd
  have hv (i : Fin 2) : mfderiv (𝓡 2) (𝓡 n) (f ∘ Phi) p
      (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      m64SourceScaleFactor s i • mfderiv (𝓡 2) (𝓡 n) f (Phi p)
        (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    rw [hd]
    change mfderiv (𝓡 2) (𝓡 n) f (Phi p)
      (D (EuclideanSpace.basisFun (Fin 2) ℝ i)) = _
    rw [EuclideanSpace.basisFun_apply, m64SourceScale_basis, map_smul]
  change g.inner (f (Phi p))
    (mfderiv (𝓡 2) (𝓡 n) (f ∘ Phi) p (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (mfderiv (𝓡 2) (𝓡 n) (f ∘ Phi) p (EuclideanSpace.basisFun (Fin 2) ℝ j)) = _
  rw [hv i, hv j]
  simp only [map_smul, smul_apply, smul_eq_mul]
  change _ = _ * _ * g.inner (f (Phi p)) _ _
  ring

/-- The original weighted conformality becomes ordinary conformality after the actual
square-root modulus normalization, also at branches. Proof expansion for Morgan-Tian (2007),
Lemma 19.15, pp. 447-449. -/
theorem m64AreaGram_sourceAffine_conformal {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (a : LoopPlane) {r : ℝ} (hr : 0 < r)
    {f : LoopPlane → M} {p : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f
      (m64SourceAffine a (Real.sqrt r) (Real.sqrt_pos.mpr hr).ne' p))
    (hconf : let q := m64SourceAffine a (Real.sqrt r) (Real.sqrt_pos.mpr hr).ne' p
      r * m60AreaGram g f q 0 0 = r⁻¹ * m60AreaGram g f q 1 1 ∧
        m60AreaGram g f q 0 1 = 0) :
    let F := f ∘ m64SourceAffine a (Real.sqrt r) (Real.sqrt_pos.mpr hr).ne'
    m60AreaGram g F p 0 0 = m60AreaGram g F p 1 1 ∧ m60AreaGram g F p 0 1 = 0 := by
  have hss : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  have his : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ = r⁻¹ := by
    rw [← mul_inv_rev, hss]
  have hpair := m64AreaGram_sourceAffine g a (Real.sqrt r) (Real.sqrt_pos.mpr hr).ne' hf
  constructor
  · rw [hpair 0 0, hpair 1 1]
    simpa only [m64SourceScaleFactor, if_pos rfl, show (1 : Fin 2) ≠ 0 from by decide,
      if_true, if_false, hss, his] using hconf.1
  · rw [hpair 0 1, hconf.2, mul_zero]

end PoincareMT

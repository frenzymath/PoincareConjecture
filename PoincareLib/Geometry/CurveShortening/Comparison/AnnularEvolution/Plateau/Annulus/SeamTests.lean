import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.AnnulusClass

/-!
# Actual weak tests across the periodic angular seam

A compact test on the two-copy open strip is folded to the fundamental
rectangle by adding one translated copy. Its angular endpoint values
agree, and its radial boundary values vanish. The two stored Green
identities therefore give the genuine zero-flux test identity needed by
the periodic weak extension.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareMT

/-- The open two-copy rectangle extending across the angular cut. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
def m64AnnulusSeamDomain : Set LoopPlane :=
  {p | -curvePeriod < p 0 ∧ p 0 < curvePeriod ∧ 0 < p 1 ∧ p 1 < 1}

/-- The source translation by one full angular period. Proof expansion for Morgan-Tian
(2007), Lemma 19.15, pp. 447-449. -/
def m64AnnulusSeamTranslation : LoopPlane := annulusPoint curvePeriod 0

/-- Fold an actual test by adding its copy translated by one angular period. Proof expansion
for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
def m64AnnulusSeamTest (phi : LoopPlane → ℝ) (p : LoopPlane) : ℝ :=
  phi p + phi (p - m64AnnulusSeamTranslation)

/-- The actual two-copy domain across the angular cut is open. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusSeamDomain_isOpen : IsOpen m64AnnulusSeamDomain := by
  have h0 : IsOpen {p : LoopPlane | -curvePeriod < p 0 ∧ p 0 < curvePeriod} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous continuous_const)
  have h1 : IsOpen {p : LoopPlane | 0 < p 1 ∧ p 1 < 1} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous).inter
      (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous continuous_const)
  simpa only [m64AnnulusSeamDomain, Set.ofPred_and, inter_assoc] using h0.inter h1

/-- Subtracting the angular translation reduces the actual angular coordinate by one period.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusPoint_sub_seamTranslation (x s : ℝ) :
    annulusPoint x s - m64AnnulusSeamTranslation = annulusPoint (x - curvePeriod) s := by
  ext i
  fin_cases i <;> simp [m64AnnulusSeamTranslation, annulusPoint]

/-- The folded test is smooth when the original test is smooth. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusSeamTest_contDiff {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) :
    ContDiff ℝ ∞ (m64AnnulusSeamTest phi) :=
  hp.add (hp.comp (contDiff_id.sub contDiff_const))

/-- Compute the actual derivative of the folded angular test. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusSeamTest_fderiv {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi)
    (p : LoopPlane) (i : Fin 2) :
    fderiv ℝ (m64AnnulusSeamTest phi) p (EuclideanSpace.single i 1) =
      fderiv ℝ phi p (EuclideanSpace.single i 1) +
        fderiv ℝ phi (p - m64AnnulusSeamTranslation) (EuclideanSpace.single i 1) := by
  have hsub := (hasFDerivAt_id (𝕜 := ℝ) p).sub_const m64AnnulusSeamTranslation
  have hcomp := ((hp.differentiable (by simp)) _).hasFDerivAt.comp p hsub
  have hd := congrArg (fun L : LoopPlane →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
    ((((hp.differentiable (by simp)) p).hasFDerivAt.add hcomp).fderiv)
  change fderiv ℝ (fun q => phi q + phi (q - m64AnnulusSeamTranslation)) p
    (EuclideanSpace.single i 1) = _
  simpa only [m64AnnulusSeamTest, Pi.add_def, Function.comp_def, id_eq,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hd

/-- Support in the two-copy domain makes the folded test agree on the angular boundaries.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusSeamTest_periodic_boundary {phi : LoopPlane → ℝ}
    (hs : tsupport phi ⊆ m64AnnulusSeamDomain) (s : ℝ) :
    m64AnnulusSeamTest phi (annulusPoint curvePeriod s) =
      m64AnnulusSeamTest phi (annulusPoint 0 s) := by
  have hp : phi (annulusPoint curvePeriod s) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl curvePeriod) (hs h).2.1)
  have hm : phi (annulusPoint (-curvePeriod) s) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl (-curvePeriod)) (hs h).1)
  simp only [m64AnnulusSeamTest, m64AnnulusPoint_sub_seamTranslation, sub_self,
    zero_sub, hp, hm, zero_add, add_zero]

/-- Support in the two-copy domain makes the folded test vanish on both radial boundaries.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusSeamTest_radial_boundary {phi : LoopPlane → ℝ}
    (hs : tsupport phi ⊆ m64AnnulusSeamDomain) (x : ℝ) :
    m64AnnulusSeamTest phi (annulusPoint x 0) = 0 ∧
      m64AnnulusSeamTest phi (annulusPoint x 1) = 0 := by
  have hzero (y : ℝ) (s : ℝ) (h : s = 0 ∨ s = 1) : phi (annulusPoint y s) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    rcases h with rfl | rfl
    · exact (lt_irrefl (0 : ℝ)) (hs hp).2.2.1
    · exact (lt_irrefl (1 : ℝ)) (hs hp).2.2.2
  simp only [m64AnnulusSeamTest, m64AnnulusPoint_sub_seamTranslation,
    hzero _ _ (Or.inl rfl), hzero _ _ (Or.inr rfl), add_zero, and_self]

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

/-- The two stored Green identities give the actual zero-flux identity for a folded test.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem M64ObservedWeakAnnulus.seam_folded_green
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi)
    (hs : tsupport phi ⊆ m64AnnulusSeamDomain) (i : Fin 2) :
    (∫ p in interior m64AnnulusDomain,
      (phi p + phi (p - m64AnnulusSeamTranslation)) • A.column i p) +
      (∫ p in interior m64AnnulusDomain,
        (fderiv ℝ phi p (EuclideanSpace.single i 1) +
          fderiv ℝ phi (p - m64AnnulusSeamTranslation) (EuclideanSpace.single i 1)) •
            e (A.map p)) = 0 := by
  have hpsi := (m64AnnulusSeamTest_contDiff hp).of_le (m := 1) (by simp)
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · have h := A.seam (m64AnnulusSeamTest phi) hpsi
      (fun s _ => m64AnnulusSeamTest_periodic_boundary hs s)
    simpa only [m64AnnulusSeamTest_fderiv hp, m64AnnulusSeamTest] using h
  · have h := A.boundary (m64AnnulusSeamTest phi) hpsi
    have hz : (∫ x in Icc (0 : ℝ) curvePeriod,
        m64AnnulusSeamTest phi (annulusPoint x 1) • e (c1 x) -
          m64AnnulusSeamTest phi (annulusPoint x 0) • e (c0 x)) = 0 := by
      simp only [(m64AnnulusSeamTest_radial_boundary hs _).1,
        (m64AnnulusSeamTest_radial_boundary hs _).2, zero_smul, sub_zero, integral_zero]
    rw [hz] at h
    simpa only [m64AnnulusSeamTest_fderiv hp, m64AnnulusSeamTest] using h

end PoincareMT

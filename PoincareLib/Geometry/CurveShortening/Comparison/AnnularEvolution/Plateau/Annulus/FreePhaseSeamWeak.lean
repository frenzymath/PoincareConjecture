import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.FreePhaseSeamTests

/-! The stored real phase seam flux cancels the affine correction.
Thus the actual phase has H1 regularity across the angular cut.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareMT.M64FreeWeakPhaseAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusSeamDomain

/-- The affine seam extension of the phase and its translated columns are genuinely L2.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem phase_seam_extension_memLp
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D) :
    MemLp (m64AnnulusAffineSeamExtend A.phase D) 2 (volume.restrict O) ∧
      ∀ i : Fin 2,
        MemLp (m64AnnulusSeamExtend (A.phaseColumn i : LoopPlane → ℝ)) 2
          (volume.restrict O) :=
  ⟨m64AnnulusAffineSeamExtend_memLp (Lp.memLp A.phase) D,
    fun i => m64AnnulusSeamExtend_memLp (Lp.memLp (A.phaseColumn i))⟩

/-- The extended real phase satisfies the zero-flux interior Green formula across the cut.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem phase_seam_extension_green
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ O) (i : Fin 2) :
    (∫ p in O, phi p * m64AnnulusSeamExtend (A.phaseColumn i : LoopPlane → ℝ) p) +
      (∫ p in O, fderiv ℝ phi p (EuclideanSpace.single i 1) *
        m64AnnulusAffineSeamExtend A.phase D p) = 0 := by
  have ht := m64AnnulusSeam_test_memLp hp hc i
  have hcol := m64AnnulusSeam_integral_smul (Lp.memLp (A.phaseColumn i)) ht.1
  simp only [smul_eq_mul] at hcol
  rw [hcol, m64AnnulusAffineSeam_integral_mul (Lp.memLp A.phase) D ht.2]
  linarith [A.phase_seam_folded_green hp hs i]

/-- The translated phase columns are the actual weak derivatives of the affine seam
extension. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem phase_seam_extension_weak_partial
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D) (i : Fin 2) :
    HasWeakPartialDeriv i (m64AnnulusSeamExtend (A.phaseColumn i : LoopPlane → ℝ))
      (m64AnnulusAffineSeamExtend A.phase D) O := by
  intro phi hp hc hs
  have h := A.phase_seam_extension_green hp hc hs i
  simp only [mul_comm] at h ⊢
  linarith

end PoincareMT.M64FreeWeakPhaseAnnulus

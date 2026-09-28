import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryHalfDiskPolynomialTests
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

theorem M64ObservedWeakAnnulus.vector_test_green
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {Z : LoopPlane → LoopPlane} (hZ : ContDiff ℝ 1 Z)
    (hperiod : ∀ s ∈ Icc (0 : ℝ) 1,
      Z (annulusPoint curvePeriod s) 0 = Z (annulusPoint 0 s) 0) :
    (∫ p in S, Z p 0 • A.column 0 p) +
        (∫ p in S, Z p 1 • A.column 1 p) +
        (∫ p in S, fderiv ℝ (fun q => Z q 0) p e0 • e (A.map p)) +
        (∫ p in S, fderiv ℝ (fun q => Z q 1) p e1 • e (A.map p)) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        Z (annulusPoint x 1) 1 • e (c1 x) -
          Z (annulusPoint x 0) 1 • e (c0 x) := by
  let phi0 : LoopPlane → ℝ := fun p => Z p 0
  let phi1 : LoopPlane → ℝ := fun p => Z p 1
  have hphi0 : ContDiff ℝ 1 phi0 := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) 0).contDiff.comp hZ
  have hphi1 : ContDiff ℝ 1 phi1 := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) 1).contDiff.comp hZ
  have hs := A.seam phi0 hphi0 (fun s hs => by
    exact hperiod s hs)
  have hb := A.boundary phi1 hphi1
  change (∫ p in S, phi0 p • A.column 0 p) +
      (∫ p in S, phi1 p • A.column 1 p) +
      (∫ p in S, fderiv ℝ phi0 p e0 • e (A.map p)) +
      (∫ p in S, fderiv ℝ phi1 p e1 • e (A.map p)) = _
  calc
    _ = ((∫ p in S, phi0 p • A.column 0 p) +
          ∫ p in S, fderiv ℝ phi0 p e0 • e (A.map p)) +
        ((∫ p in S, phi1 p • A.column 1 p) +
          ∫ p in S, fderiv ℝ phi1 p e1 • e (A.map p)) := by abel
    _ = 0 + (∫ x in Icc (0 : ℝ) curvePeriod,
          phi1 (annulusPoint x 1) • e (c1 x) -
            phi1 (annulusPoint x 0) • e (c0 x)) := by rw [hs, hb]
    _ = ∫ x in Icc (0 : ℝ) curvePeriod,
          phi1 (annulusPoint x 1) • e (c1 x) -
            phi1 (annulusPoint x 0) • e (c0 x) := by simp

theorem M64ObservedWeakAnnulus.polynomial_test_zero_green
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {psi : ℝ → ℝ} (hpsi : ContDiff ℝ 1 psi) (x : ℝ)
    (hperiod : ∀ s ∈ Icc (0 : ℝ) 1,
      m64HalfDiskPolynomialTestZeroAt x psi (annulusPoint curvePeriod s) 0 =
        m64HalfDiskPolynomialTestZeroAt x psi (annulusPoint 0 s) 0) :
    (∫ p in S, m64HalfDiskPolynomialTestZeroAt x psi p 0 • A.column 0 p) +
        (∫ p in S, m64HalfDiskPolynomialTestZeroAt x psi p 1 • A.column 1 p) +
        (∫ p in S, fderiv ℝ (fun q =>
          m64HalfDiskPolynomialTestZeroAt x psi q 0) p e0 • e (A.map p)) +
        (∫ p in S, fderiv ℝ (fun q =>
          m64HalfDiskPolynomialTestZeroAt x psi q 1) p e1 • e (A.map p)) =
      ∫ y in Icc (0 : ℝ) curvePeriod,
        m64HalfDiskPolynomialTestZeroAt x psi (annulusPoint y 1) 1 • e (c1 y) -
          m64HalfDiskPolynomialTestZeroAt x psi (annulusPoint y 0) 1 • e (c0 y) := by
  exact A.vector_test_green
    (m64HalfDisk_polynomialTestAt_contDiff hpsi x).1 hperiod

theorem M64ObservedWeakAnnulus.polynomial_test_one_green
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {psi : ℝ → ℝ} (hpsi : ContDiff ℝ 1 psi) (x : ℝ)
    (hperiod : ∀ s ∈ Icc (0 : ℝ) 1,
      m64HalfDiskPolynomialTestOneAt x psi (annulusPoint curvePeriod s) 0 =
        m64HalfDiskPolynomialTestOneAt x psi (annulusPoint 0 s) 0) :
    (∫ p in S, m64HalfDiskPolynomialTestOneAt x psi p 0 • A.column 0 p) +
        (∫ p in S, m64HalfDiskPolynomialTestOneAt x psi p 1 • A.column 1 p) +
        (∫ p in S, fderiv ℝ (fun q =>
          m64HalfDiskPolynomialTestOneAt x psi q 0) p e0 • e (A.map p)) +
        (∫ p in S, fderiv ℝ (fun q =>
          m64HalfDiskPolynomialTestOneAt x psi q 1) p e1 • e (A.map p)) =
      ∫ y in Icc (0 : ℝ) curvePeriod,
        m64HalfDiskPolynomialTestOneAt x psi (annulusPoint y 1) 1 • e (c1 y) -
          m64HalfDiskPolynomialTestOneAt x psi (annulusPoint y 0) 1 • e (c0 y) := by
  exact A.vector_test_green
    (m64HalfDisk_polynomialTestAt_contDiff hpsi x).2 hperiod

end PoincareConjecture

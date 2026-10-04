import PoincareLib.Geometry.CurveShortening.Deformation.AreaContinuity.SmallAnnulus

/-!
# Filling-area convergence at an actual C1 limit

The endpoint passage used after Claim 19.28 and Remark 19.29,
Morgan--Tian pp. 459-461. Genuine small C1 annuli supply a filling disk
for the limit before M64's two-sided infimum comparison is applied.
The metric is one fixed included flow metric. See M65 derivation 26.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {circumference : ℝ}

/-- Actual C1 convergence of filled loops supplies both a genuine limit
disk and convergence of the actual filling infima; the endpoint passage
in Claim 19.28 and Remark 19.29, pp. 459-461. -/
theorem m65FillingArea_tendsto_of_C1
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (disks : M64DiskAreaComparison P t) (compact : IsCompact (univ : Set M))
    (loops : ℕ → C1FreeLoopSpace (M := M)) (gamma : C1FreeLoopSpace (M := M))
    (hconv : Tendsto loops atTop (𝓝 gamma))
    (hfill : ∀ n, Nonempty (LipschitzSpanningDisk (F.metric t) (loops n))) :
    Nonempty (LipschitzSpanningDisk (F.metric t) gamma) ∧
      Tendsto (fun n => fillingArea (F.metric t) (loops n)) atTop
        (𝓝 (fillingArea (F.metric t) gamma)) := by
  have hnear (epsilon : ℝ) (hepsilon : 0 < epsilon) :=
    hconv.eventually (m65Eventually_smallC1Annulus (F.metric t) compact gamma hepsilon)
  have hcompare (n : ℕ)
      (A : M64Annulus (F.metric t) (periodicFreeLoop gamma) (periodicFreeLoop (loops n)))
      (hA : ContMDiff (𝓡 2) (𝓡 3) 1 A.map) :
      ∃ _D : LipschitzSpanningDisk (F.metric t) gamma,
        |fillingArea (F.metric t) (loops n) - fillingArea (F.metric t) gamma| ≤ A.area := by
    obtain ⟨Dn⟩ := hfill n
    exact m65BaseAnnulus_fillingComparison P t disks gamma (loops n) A.map hA
      A.periodic A.lower_boundary A.upper_boundary Dn
  constructor
  · obtain ⟨n, A, hA, _⟩ := (hnear 1 zero_lt_one).exists
    obtain ⟨D, _⟩ := hcompare n A hA
    exact ⟨D⟩
  · apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    filter_upwards [hnear epsilon hepsilon] with n hn
    obtain ⟨A, hA, hsmall⟩ := hn
    obtain ⟨_, hbound⟩ := hcompare n A hA
    simpa only [Real.dist_eq] using hbound.trans_lt hsmall

end PoincareMT

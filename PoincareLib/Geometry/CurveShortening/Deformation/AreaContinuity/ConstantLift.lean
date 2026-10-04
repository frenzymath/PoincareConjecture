import PoincareLib.Geometry.CurveShortening.Deformation.SweptArea.SmoothAnnulus
import PoincareLib.Geometry.CurveShortening.Comparison.AnnulusTheory

/-!
# Static annuli in the selected circle product

The filling-area passage in Morgan--Tian Claim 19.28, printed pp. 459-461.
An actual C1 annulus in the base lifts with constant circle coordinate.
Its projected area is exactly its base area, and M64's reverse gluing
supplies a disk before its infimum comparison is invoked. See derivation 26.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)} {circumference : ℝ}

/-- A C1 annulus lifts to the exact selected circle product with constant
circle coordinate; the comparison used in Claim 19.28, pp. 459-461. -/
noncomputable def m65ConstantCircleAnnulus
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → M} (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 3) 1 f)
    (hp : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (h0 : ∀ x, f (annulusPoint x 0) = c0 x)
    (h1 : ∀ x, f (annulusPoint x 1) = c1 x) :
    M64Annulus (P.flow.metric t)
      (fun x => (c0 x, P.circle.quotient 0))
      (fun x => (c1 x, P.circle.quotient 0)) := by
  let := P.charts.chartedSpace
  have hreg : ContMDiff (𝓡 2) (𝓡 4) 1
      (fun p => (f p, P.circle.quotient 0) : LoopPlane → P.charts.Point) :=
    (P.charts.from_product_smooth.of_le (by norm_num)).comp
      (hf.prodMk contMDiff_const)
  exact m65AnnulusOfContMDiff (P.flow.metric t) _ hreg
    (fun x s => congrArg (fun q => (q, P.circle.quotient 0)) (hp x s))
    (fun x => congrArg (fun q => (q, P.circle.quotient 0)) (h0 x))
    (fun x => congrArg (fun q => (q, P.circle.quotient 0)) (h1 x))

/-- Projection of the constant-circle lift has the literal base area
integral; Claim 19.28, pp. 459-461. -/
theorem m65ConstantCircleAnnulus_projectedArea
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → M} (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 3) 1 f)
    (hp : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (h0 : ∀ x, f (annulusPoint x 0) = c0 x)
    (h1 : ∀ x, f (annulusPoint x 1) = c1 x) :
    m64ProjectedAnnulusArea P t (m65ConstantCircleAnnulus P t f hf hp h0 h1) =
      m64AnnulusArea (F.metric t) f := rfl

/-- A genuine C1 annulus transports a filling witness in the reverse
direction and bounds the actual filling-area difference; the limit passage
in Claim 19.28, pp. 459-461. -/
theorem m65BaseAnnulus_fillingComparison
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (disks : M64DiskAreaComparison P t)
    (gamma eta : C1FreeLoopSpace (M := M))
    (f : LoopPlane → M) (hf : ContMDiff (𝓡 2) (𝓡 3) 1 f)
    (hp : ∀ x s, f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (h0 : ∀ x, f (annulusPoint x 0) = periodicFreeLoop gamma x)
    (h1 : ∀ x, f (annulusPoint x 1) = periodicFreeLoop eta x)
    (Deta : LipschitzSpanningDisk (F.metric t) eta) :
    ∃ _Dgamma : LipschitzSpanningDisk (F.metric t) gamma,
      |fillingArea (F.metric t) eta - fillingArea (F.metric t) gamma| ≤
        m64AnnulusArea (F.metric t) f := by
  let A := m65ConstantCircleAnnulus P t f hf hp h0 h1
  have hglue := disks _ _ A gamma eta (fun _ => rfl) (fun _ => rfl)
  obtain ⟨Dgamma, _⟩ := hglue.reverse 1 zero_lt_one Deta
  exact ⟨Dgamma, hglue.infimum ⟨Dgamma⟩ ⟨Deta⟩⟩

end PoincareMT

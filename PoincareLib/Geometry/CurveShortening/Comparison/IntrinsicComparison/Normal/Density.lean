import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Area.Density
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Normal.Strip
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# The actual uniform normal-strip area density

The product-parameter normal map is transferred to the Euclidean source
used by Riemannian volume. Its constructed metric lower bound yields the
area-density estimate through the first boundary-contact time.

Morgan--Tian context: Claim 19.37, printed pp. 468-469, in the proof of Proposition
19.35. This module supplies actual normal-geodesic data or its coordinate and measure
transport.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle Matrix

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The product-coordinate lower bound transfers through the actual coordinate differential,
with its area normalization unchanged. Source/construction: Morgan--Tian Claim 19.37,
printed pp. 468-469. -/
theorem m64Intrinsic_normal_map_density_lower
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {u : ℝ × ℝ → AnnulusCoordinates} {a t c speed : ℝ}
    (hu : DifferentiableAt ℝ u (a, t))
    (hbound : ∀ v : ℝ × ℝ, c ^ 2 * (speed ^ 2 * v.1 ^ 2 + v.2 ^ 2) ≤
      G.inner (u (a, t)) (fderiv ℝ u (a, t) v) (fderiv ℝ u (a, t) v)) :
    c ^ 2 * speed ≤ G.pullbackVolumeDensity
      (fun z : AnnulusCoordinates => u (z 0, z 1)) !₂[a, t] := by
  let P : AnnulusCoordinates → ℝ × ℝ := fun z => (z 0, z 1)
  have hP : HasFDerivAt P
      ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0).prod
        (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1)) !₂[a, t] :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 !₂[a, t] 0).prodMk
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 !₂[a, t] 1)
  have hchain := hu.hasFDerivAt.comp !₂[a, t] hP
  have hd (v : AnnulusCoordinates) :
      mfderiv (𝓡 2) (𝓡 2) (fun z : AnnulusCoordinates => u (z 0, z 1)) !₂[a, t] v =
        fderiv ℝ u (a, t) (v 0, v 1) := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (u ∘ P) !₂[a, t] v = fderiv ℝ u (a, t) (v 0, v 1)
    rw [hchain.fderiv]
    rfl
  apply m64Intrinsic_pullbackDensity_lower G
  intro v
  rw [hd]
  exact hbound (v 0, v 1)

/-- The public Gaussian upper bound produces a uniform normal map with the actual
area-density lower bound up to every good point's first exit. No global injectivity is
asserted at this stage. Source/construction: Morgan--Tian Claim 19.37, printed pp. 468-469. -/
theorem m64Intrinsic_exists_uniform_normal_density
    (K : ℝ) {delta alpha : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (halpha : 0 ≤ alpha) :
    ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
      ∀ N : IntrinsicAnnulus, N.GaussianCurvatureBound K →
        ∃ u : ℝ × ℝ → AnnulusCoordinates,
          ContDiff ℝ ∞ u ∧ (∀ s, u (s, 0) = intrinsicAnnulusBoundary 1 s) ∧
          ∀ a : ℝ, intrinsicGeodesicCurvature N.metric N.connection 1 a ≤ alpha →
            ∃ b : ℝ, 0 < b ∧ b ≤ R ∧
              (∀ t ∈ Ioo (0 : ℝ) b, 1 < ‖u (a, t)‖ ∧ ‖u (a, t)‖ < 2) ∧
              u (a, b) ∈ standardAnnulusDomain ∧
              (b = R ∨ ‖u (a, b)‖ = 1 ∨ ‖u (a, b)‖ = 2) ∧
              ∀ t ∈ Icc (0 : ℝ) b,
                (1 - delta) ^ 2 * intrinsicBoundarySpeed N.metric 1 a ≤
                  N.metric.pullbackVolumeDensity
                    (fun z : AnnulusCoordinates => u (z 0, z 1)) !₂[a, t] := by
  obtain ⟨R, hR, hRsmall, hstrip⟩ :=
    m64Intrinsic_exists_uniform_normal_strip K hdelta hdelta1 halpha
  refine ⟨R, hR, hRsmall, ?_⟩
  intro N hK
  obtain ⟨_, u, _, hu, _, hinit, _, hpoint⟩ := hstrip N hK
  refine ⟨u, hu, hinit, ?_⟩
  intro a ha
  obtain ⟨b, _, _, hb, hbR, _, _, _, _, _, hinside, hlast, hcontact, hmetric⟩ := hpoint a ha
  refine ⟨b, hb, hbR, hinside, hlast, hcontact, ?_⟩
  intro t ht
  exact m64Intrinsic_normal_map_density_lower N.metric
    (hu.differentiable (by simp) (a, t)) (hmetric t ht).1

end PoincareMT

import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Compactness.Target

/-!
# A chart-readable observation retaining a prescribed smooth current map

The finite compact-target chart observation can include any given smooth
planar map as a fixed linear projection. Applying this to the two real
circle coordinates lets the actual weak extraction retain their current
using linear observations, without assuming a nonlinear weak chain rule.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped Topology Manifold ContDiff

namespace PoincareMT.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "V" => EuclideanSpace ℝ (Fin 2)

/-- Construct the compact observation and a literal linear reader for a specified smooth
planar target map. No coordinate-reader extension is assumed beyond M60's actual finite
bump-chart construction. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-25-free-label-compactness.md`. -/
theorem chartReadable_observation_with_planar_projection
    (f : M → V) (hf : ContMDiff (𝓡 n) (𝓡 2) ∞ f) :
    ∃ (d : ℕ) (e : M → EuclideanSpace ℝ (Fin d))
      (R : EuclideanSpace ℝ (Fin d) →L[ℝ] V),
      ContMDiff (𝓡 n) (𝓡 d) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := n) e ∧ R ∘ e = f := by
  classical
  obtain ⟨d0, e0, he0, hi0, hr0⟩ := M60.suCompactObservation_exists (n := n) (M := M)
  let F := EuclideanSpace ℝ (Fin d0) × V
  let d := Module.finrank ℝ F
  let A : F ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let w : M → F := fun p => (e0 p, f p)
  let e := A ∘ w
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ w := he0.prodMk_space hf
  have he : ContMDiff (𝓡 n) (𝓡 d) ∞ e := A.toDiffeomorph.contMDiff.comp hw
  have hwi : Function.Injective w := by
    intro p q hpq
    exact hi0.injective (congrArg Prod.fst hpq)
  have hei : IsClosedEmbedding e := he.continuous.isClosedEmbedding (A.injective.comp hwi)
  let R : EuclideanSpace ℝ (Fin d) →L[ℝ] V :=
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d0)) V).comp A.symm.toContinuousLinearMap
  refine ⟨d, e, R, he, hei, ?_, ?_⟩
  · intro p
    obtain ⟨b, hb, L, hL⟩ := hr0 p
    let S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      L.comp ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin d0)) V).comp
        A.symm.toContinuousLinearMap)
    refine ⟨b, hb, S, ?_⟩
    filter_upwards [hL] with q hq
    simpa only [S, e, w, Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, A.symm_apply_apply,
      ContinuousLinearMap.coe_fst'] using hq
  · funext p
    simp only [R, e, w, Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, A.symm_apply_apply, ContinuousLinearMap.coe_snd']

end PoincareMT.M64

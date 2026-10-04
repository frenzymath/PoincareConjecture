import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.MovingDensityVariation
import PoincareLib.Geometry.RicciFlow.CurveShortening.Connection.Torsion

/-!
# Torsion freeness for an actual plane-map variation

Restriction to a spatial coordinate line reduces the disk calculation to
the closed M62 two-parameter pullback torsion theorem. The affine-line
velocity is identified with the literal spatial derivative column.
Source: Morgan--Tian Lemma 19.2, p. 438; M65 derivation 24, fifth stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
/-- The velocity of an affine spatial restriction is the actual manifold
derivative on its direction vector. Source: MT Lemma 19.2, p. 438; M65 derivation 24. -/
theorem m65CurveVelocity_affineLine {f : LoopPlane → M} {z : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z) (v : LoopPlane) :
    curveVelocity (fun r : ℝ => f (z + r • v)) 0 = mfderiv (𝓡 2) (𝓡 n) f z v := by
  have hline : HasDerivAt (fun r : ℝ => z + r • v) v 0 := by
    simpa +instances only [zero_add, one_smul] using!
      (hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hlinev : mfderiv (𝓘(ℝ, ℝ)) (𝓡 2) (fun r : ℝ => z + r • v) 0 1 = v := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using! hline.deriv
  have h := mfderiv_comp_apply_of_eq 0 hf hline.differentiableAt.mdifferentiableAt
    (by simp : z + (0 : ℝ) • v = z) (1 : ℝ)
  simpa only [curveVelocity, hlinev, Function.comp_def] using h

/-- Along a smooth plane variation, the time covariant derivative of an
actual spatial column equals the spatial derivative of its time velocity.
Source: MT Lemma 19.2, p. 438; M65 derivation 24, fifth stage. -/
theorem m65PlaneCovariantColumn_commute {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (u : ℝ → LoopPlane → M)
    {U : Set (ℝ × LoopPlane)} (hU : IsOpen U)
    (hu : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (Function.uncurry u) U)
    {t : ℝ} {z : LoopPlane} (htz : (t, z) ∈ U) (v : LoopPlane) :
    rampHorizontalCovariantDerivative D (fun s => u s z)
      (fun s => mfderiv (𝓡 2) (𝓡 n) (u s) z v) t =
      rampHorizontalCovariantDerivative D (fun r => u t (z + r • v))
        (fun r => curveVelocity (fun s => u s (z + r • v)) t) 0 := by
  let σ : ℝ × ℝ → ℝ × LoopPlane := fun q => (q.2, z + q.1 • v)
  let Ω := σ ⁻¹' U
  let c : ℝ → ℝ → M := fun r s => u s (z + r • v)
  have hσ : ContMDiff (𝓘(ℝ, ℝ × ℝ)) ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ∞ σ :=
    contDiff_snd.contMDiff.prodMk
      (contDiff_const.add (contDiff_fst.smul contDiff_const)).contMDiff
  have hΩ : IsOpen Ω := hU.preimage hσ.continuous
  have hmem : ((0 : ℝ), t) ∈ Ω := by
    simpa only [Ω, σ, mem_preimage, zero_smul, add_zero] using htz
  have hc : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
      (fun q : ℝ × ℝ => c q.1 q.2) Ω :=
    hu.comp hσ.contMDiffOn (fun _ hq => hq)
  have htor := M62.pullback_velocity_commute D c hΩ hc hmem
  have htime : (fun s : ℝ => (s, z)) ⁻¹' U ∈ 𝓝 t :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (hU.mem_nhds htz)
  have heq : (fun s => curveVelocity (fun r => u s (z + r • v)) 0) =ᶠ[𝓝 t]
      (fun s => mfderiv (𝓡 2) (𝓡 n) (u s) z v) := by
    filter_upwards [htime] with s hs
    have hsu := (hu (s, z) hs).contMDiffAt (hU.mem_nhds hs)
    have hslice : MDifferentiableAt (𝓡 2) (𝓡 n) (u s) z :=
      (hsu.comp z (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
    exact m65CurveVelocity_affineLine hslice v
  have hcongr := M62.pullback_congr D (γ := fun s => u s z) heq
  have htor' : rampHorizontalCovariantDerivative D (fun s => u s z)
      (fun s => curveVelocity (fun r => u s (z + r • v)) 0) t =
      rampHorizontalCovariantDerivative D (fun r => u t (z + r • v))
        (fun r => curveVelocity (fun s => u s (z + r • v)) t) 0 := by
    dsimp only [c] at htor
    have hpoint : z + (0 : ℝ) • v = z := by simp
    rw [hpoint] at htor
    exact htor
  exact hcongr.symm.trans htor'

end PoincareMT

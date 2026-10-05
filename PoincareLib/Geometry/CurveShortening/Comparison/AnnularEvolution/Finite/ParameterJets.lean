import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Modulus.EnergyDensity

/-! Literal weighted energy under a differentiable parameter map
depends only on its actual first jet. Source: MT Lemma 19.15,
pp. 447-449; finite-conormal-variation derivation. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- The actual source column of a parameterized motion is the pushforward of its genuine
parameter derivative. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp.
447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64ParameterAnnulus_spatial_differential
    {Phi : ℝ × E → M} {h : LoopPlane → E} {s : ℝ} {p : LoopPlane}
    (hPhi : MDifferentiableAt 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (s, h p))
    (hh : DifferentiableAt ℝ h p) (w : LoopPlane) :
    mfderiv (𝓡 2) (𝓡 n) (fun q => Phi (s, h q)) p w =
      mfderiv 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (s, h p) (0, fderiv ℝ h p w) := by
  have harg := (hasFDerivAt_const s p).prodMk hh.hasFDerivAt
  have hd : mfderiv (𝓡 2) 𝓘(ℝ, ℝ × E) (fun q => (s, h q)) p w =
      (0, fderiv ℝ h p w) := by
    rw [mfderiv_eq_fderiv, harg.fderiv]
    rfl
  have hc := mfderiv_comp_apply p hPhi harg.differentiableAt.mdifferentiableAt w
  rw [hd] at hc
  exact hc

/-- Matching parameter first jets give matching genuine source differentials of the moving
map. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project
derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64ParameterAnnulus_differential_eq_of_firstJet
    {Phi : ℝ × E → M} {h k : LoopPlane → E} {s : ℝ} {p : LoopPlane}
    (hPhi : MDifferentiableAt 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (s, h p))
    (hh : DifferentiableAt ℝ h p) (hk : DifferentiableAt ℝ k p)
    (hvalue : h p = k p) (hderiv : fderiv ℝ h p = fderiv ℝ k p) (w : LoopPlane) :
    mfderiv (𝓡 2) (𝓡 n) (fun q => Phi (s, h q)) p w =
      mfderiv (𝓡 2) (𝓡 n) (fun q => Phi (s, k q)) p w := by
  have hp : (h p, fderiv ℝ h p w) = (k p, fderiv ℝ k p w) :=
    Prod.ext hvalue (congrArg (fun L : LoopPlane →L[ℝ] E => L w) hderiv)
  have hjet := congrArg (fun q : E × E =>
    (mfderiv 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (s, q.1) (0, q.2) :
      EuclideanSpace ℝ (Fin n))) hp
  exact (m64ParameterAnnulus_spatial_differential hPhi hh w).trans
    (hjet.trans (m64ParameterAnnulus_spatial_differential (hvalue ▸ hPhi) hk w).symm)

/-- Two actual differentiable parameter maps with the same first jet give exactly the same
weighted energy for a smooth motion at that point. Source: Morgan--Tian (2007), Lemma 19.15
and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64ParameterAnnulus_energy_eq_of_firstJet
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (r : ℝ) {Phi : ℝ × E → M}
    {h k : LoopPlane → E} {s : ℝ} {p : LoopPlane}
    (hPhi : MDifferentiableAt 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (s, h p))
    (hh : DifferentiableAt ℝ h p) (hk : DifferentiableAt ℝ k p)
    (hvalue : h p = k p) (hderiv : fderiv ℝ h p = fderiv ℝ k p) :
    m64ModulusEnergyDensity g r (fun q => Phi (s, h q)) p =
      m64ModulusEnergyDensity g r (fun q => Phi (s, k q)) p := by
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  let L : E × (LoopPlane →L[ℝ] E) → ℝ := fun q =>
    (r * g.inner (Phi (s, q.1))
      (mfderiv 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (s, q.1) (0, q.2 (B 0)))
      (mfderiv 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (s, q.1) (0, q.2 (B 0))) +
    r⁻¹ * g.inner (Phi (s, q.1))
      (mfderiv 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (s, q.1) (0, q.2 (B 1)))
      (mfderiv 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (s, q.1) (0, q.2 (B 1)))) / 2
  have hformula (u : LoopPlane → E) (hu : DifferentiableAt ℝ u p)
      (hP : MDifferentiableAt 𝓘(ℝ, ℝ × E) (𝓡 n) Phi (s, u p)) :
      m64ModulusEnergyDensity g r (fun q => Phi (s, u q)) p = L (u p, fderiv ℝ u p) := by
    simp only [m64ModulusEnergyDensity, m60AreaGram,
      m64ParameterAnnulus_spatial_differential hP hu, L, B]
  have hp : (h p, fderiv ℝ h p) = (k p, fderiv ℝ k p) := Prod.ext hvalue hderiv
  exact (hformula h hh hPhi).trans ((congrArg L hp).trans
    (hformula k hk (hvalue ▸ hPhi)).symm)

end PoincareMT

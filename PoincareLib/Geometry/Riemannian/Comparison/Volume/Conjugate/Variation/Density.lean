import PoincareLib.Geometry.Riemannian.Connection.Variation.Coordinates
import PoincareLib.Geometry.Riemannian.Connection.AlongCurve.Metric

/-!
# Local second variation of energy

The metric product rule, curvature antisymmetry, and pointwise second variation
for the retained coordinate covariant derivative. Adapted from AxelWorkspace,
`formalized-sources/riemannian/MorganTian/MorganTianLib/Geometry/SecondVariation.lean`,
revision `f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e` (Apache-2.0).
Original SHA-256: 526c282bb7d27b913f331d68887bffed1dc7db11aff1b2af1085c00e9ecd7d05.
License: `references/analysis/axel-workspace/LICENSE.Apache-2.0.txt`.
Imports and namespace use the retained connection. This is the local calculation underlying
Morgan--Tian, Section 1.3, and the nonsingularity input of Theorem 1.34, p. 19.
-/

open Set Filter
open scoped Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareMT.ConjugateVariation

open PoincareMT.ConnectionVariation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Metric compatibility of the connection coefficients -/

/-- **Math.** The connection coefficients `Γ` are **metric-compatible** with the
point-dependent bilinear form `G` when

`(∂_X G)(V, W) = G(Γ(X, V), W) + G(V, Γ(X, W))`,

i.e. `∇G = 0`.  In chart components this is
`∂_k G_{ij} = Σ_m (G_{mj} Γᵐ_{ki} + G_{im} Γᵐ_{kj})`, which is exactly do Carmo's
`partialDeriv_chartGramOnE_eq` for the Levi-Civita Christoffel symbols — so this
hypothesis is discharged by the real chart data, it is not an idealization. -/
def IsMetricCompatibleAt (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (x : E) : Prop :=
  ∀ X V W : E, fderiv ℝ G x X V W = G x (Γ x X V) W + G x V (Γ x X W)

/-- **Math.** **Metric compatibility along a map.**  For fields `V, W : P → E`
along `u : P → E`,

`∂_d (G(V, W)) = G(∇_d V, W) + G(V, ∇_d W)`.

This is the product rule for `q ↦ G(u q)(V q)(W q)`, with the derivative of the
coefficient `G ∘ u` absorbed into the two Christoffel terms by
`IsMetricCompatible`.  It is the identity that lets one integrate by parts against
the metric — the engine of both the first and the second variation. -/
theorem fderiv_metricAlong {G : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {u V W : P → E} {p : P} (hcompat : IsMetricCompatibleAt G Γ (u p))
    (hG : DifferentiableAt ℝ G (u p)) (hu : DifferentiableAt ℝ u p)
    (hV : DifferentiableAt ℝ V p) (hW : DifferentiableAt ℝ W p) (d : P) :
    fderiv ℝ (fun q => G (u q) (V q) (W q)) p d
      = G (u p) (covDerivAlong Γ u V d p) (W p) + G (u p) (V p) (covDerivAlong Γ u W d p) := by
  -- the coefficient field `G ∘ u`
  have hGu : HasFDerivAt (fun q => G (u q)) ((fderiv ℝ G (u p)).comp (fderiv ℝ u p)) p := by
    simpa [Function.comp_def] using
      HasFDerivAt.comp (x := p) (g := G) (f := u) hG.hasFDerivAt hu.hasFDerivAt
  -- two applications of the CLM product rule
  have hA := hGu.clm_apply hV.hasFDerivAt
  have hB := hA.clm_apply hW.hasFDerivAt
  rw [hB.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.flip_apply]
  rw [covDerivAlong_def, covDerivAlong_def]
  rw [hcompat (fderiv ℝ u p d) (V p) (W p)]
  simp only [map_add, ContinuousLinearMap.add_apply]
  ring

/-- The pointwise `HasFDerivAt` form of `fderiv_metricAlong`, convenient when the
identity has to be differentiated a second time. -/
theorem differentiableAt_metricAlong {G : E → E →L[ℝ] E →L[ℝ] ℝ} {u V W : P → E} {p : P}
    (hG : DifferentiableAt ℝ G (u p)) (hu : DifferentiableAt ℝ u p)
    (hV : DifferentiableAt ℝ V p) (hW : DifferentiableAt ℝ W p) :
    DifferentiableAt ℝ (fun q => G (u q) (V q) (W q)) p := by
  have hGu : HasFDerivAt (fun q => G (u q)) ((fderiv ℝ G (u p)).comp (fderiv ℝ u p)) p := by
    simpa [Function.comp_def] using
      HasFDerivAt.comp (x := p) (g := G) (f := u) hG.hasFDerivAt hu.hasFDerivAt
  exact ((hGu.clm_apply hV.hasFDerivAt).clm_apply hW.hasFDerivAt).differentiableAt

/-! ### The curvature is skew in the metric

`R_{ijkl} = −R_{ijlk}`, obtained by antisymmetrizing the second covariant
derivative of the scalar `G(V, W)`.  Metric compatibility is the only input. -/

/-- Directional second derivative of a scalar field, as a flip of the second
Fréchet derivative — the shape Schwarz symmetry is stated in. -/
theorem fderiv_fderiv_apply_dir {A : P → ℝ} {p : P} (hA : ContDiffAt ℝ 2 A p) (d : P) :
    fderiv ℝ (fun q => fderiv ℝ A q d) p = (fderiv ℝ (fderiv ℝ A) p).flip d := by
  have h21 : ((1 : ℕ∞ω) + 1 : ℕ∞ω) ≤ 2 := by norm_num
  have hD2A : HasFDerivAt (fderiv ℝ A) (fderiv ℝ (fderiv ℝ A) p) p :=
    ((hA.fderiv_right h21).differentiableAt (by norm_num)).hasFDerivAt
  have h : HasFDerivAt (fun q => fderiv ℝ A q d) ((fderiv ℝ (fderiv ℝ A) p).flip d) p := by
    simpa using hD2A.clm_apply (hasFDerivAt_const d p)
  exact h.fderiv

/-- **Math.** **The curvature is skew-symmetric in the metric**:

`G(R(X, Y) V, W) + G(V, R(X, Y) W) = 0`,

i.e. `R_{ijkl} = −R_{ijlk}`, for `X = ∂_{d₁}u`, `Y = ∂_{d₂}u` the coordinate
velocities of the family.

*Proof.*  Differentiate `G(V, W)` twice along the family.  By metric
compatibility (`fderiv_metricAlong`, used twice),

`∂_{d₁}∂_{d₂} G(V, W) = G(∇_{d₁}∇_{d₂}V, W) + G(∇_{d₂}V, ∇_{d₁}W)
    + G(∇_{d₁}V, ∇_{d₂}W) + G(V, ∇_{d₁}∇_{d₂}W).`

The left side is symmetric in `d₁, d₂` by Schwarz, and the two middle terms on the
right are visibly symmetric, so antisymmetrizing kills everything except

`0 = G(∇_{d₁}∇_{d₂}V − ∇_{d₂}∇_{d₁}V, W) + G(V, ∇_{d₁}∇_{d₂}W − ∇_{d₂}∇_{d₁}W)`,

and each bracket is a curvature term by `covDerivAlong_comm`. ∎

This is the symmetry Morgan–Tian invoke as `⟨ℛ(Y,X)Y, X⟩ = −⟨ℛ(Y,X)X, Y⟩` when
turning the second variation into the index form
(`claim:curvature-symmetries-bianchi`). -/
theorem metricAlong_christoffelCurvature_antisymm
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {u V W : P → E} {p : P}
    (hcompat : ∀ᶠ x in 𝓝 (u p), IsMetricCompatibleAt G Γ x)
    (hG : ContDiffAt ℝ 2 G (u p)) (hu : ContDiffAt ℝ 2 u p)
    (hV : ContDiffAt ℝ 2 V p) (hW : ContDiffAt ℝ 2 W p)
    (hΓ : DifferentiableAt ℝ Γ (u p)) (d₁ d₂ : P) :
    G (u p) (christoffelCurvature Γ (u p) (fderiv ℝ u p d₁) (fderiv ℝ u p d₂) (V p)) (W p)
      + G (u p) (V p)
          (christoffelCurvature Γ (u p) (fderiv ℝ u p d₁) (fderiv ℝ u p d₂) (W p)) = 0 := by
  -- `C¹` data at nearby points, needed to differentiate the compatibility identity again
  have hGev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ G (u q) := by
    have h : ∀ᶠ x in 𝓝 (u p), DifferentiableAt ℝ G x := by
      filter_upwards [hG.eventually (by simp)] with x hx
      exact hx.differentiableAt (by norm_num)
    exact hu.continuousAt.eventually h
  have hcev : ∀ᶠ q in 𝓝 p, IsMetricCompatibleAt G Γ (u q) := hu.continuousAt.eventually hcompat
  have huev : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 u q := hu.eventually (by simp)
  have hVev : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 V q := hV.eventually (by simp)
  have hWev : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 W q := hW.eventually (by simp)
  set A : P → ℝ := fun q => G (u q) (V q) (W q) with hA
  -- `A` is `C²`
  have hGcomp : ContDiffAt ℝ 2 (fun q => G (u q)) p := hG.comp p hu
  have hA2 : ContDiffAt ℝ 2 A p := (hGcomp.clm_apply hV).clm_apply hW
  -- the first covariant derivative of `A`, as a field identity near `p`
  have hfirst : ∀ d : P, (fun q => fderiv ℝ A q d) =ᶠ[𝓝 p]
      (fun q => G (u q) (covDerivAlong Γ u V d q) (W q)
        + G (u q) (V q) (covDerivAlong Γ u W d q)) := by
    intro d
    filter_upwards [hGev, huev, hVev, hWev, hcev] with q hGq huq hVq hWq hcq
    exact fderiv_metricAlong hcq hGq (huq.differentiableAt (by norm_num))
      (hVq.differentiableAt (by norm_num)) (hWq.differentiableAt (by norm_num)) d
  -- differentiability of the covariant-derivative fields at `p`
  have hcov : ∀ (X : P → E) (_ : ContDiffAt ℝ 2 X p) (d : P),
      DifferentiableAt ℝ (covDerivAlong Γ u X d) p := by
    intro X hX d
    have h1 : DifferentiableAt ℝ (fun q => fderiv ℝ X q d) p := by
      have : ContDiffAt ℝ 1 (fun q => fderiv ℝ X q d) p :=
        (hX.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
      exact this.differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (fun q => Γ (u q)) p := by
      have h : HasFDerivAt (fun q => Γ (u q)) ((fderiv ℝ Γ (u p)).comp (fderiv ℝ u p)) p := by
        simpa [Function.comp_def] using
          HasFDerivAt.comp (x := p) (g := Γ) (f := u) hΓ.hasFDerivAt
            (hu.differentiableAt (by norm_num)).hasFDerivAt
      exact h.differentiableAt
    have h3 : DifferentiableAt ℝ (fun q => fderiv ℝ u q d) p := by
      have : ContDiffAt ℝ 1 (fun q => fderiv ℝ u q d) p :=
        (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
      exact this.differentiableAt (by norm_num)
    have h4 : DifferentiableAt ℝ X p := hX.differentiableAt (by norm_num)
    have hfun : covDerivAlong Γ u X d =
        (fun q => fderiv ℝ X q d) +
          fun q => Γ (u q) (fderiv ℝ u q d) (X q) := by
      funext q
      rfl
    rw [hfun]
    exact h1.add ((h2.clm_apply h3).clm_apply h4)
  -- second derivative of `A`, expanded by compatibility twice
  have hsecond : ∀ d d' : P, fderiv ℝ (fun q => fderiv ℝ A q d) p d'
      = G (u p) (covDerivAlong Γ u (covDerivAlong Γ u V d) d' p) (W p)
        + G (u p) (covDerivAlong Γ u V d p) (covDerivAlong Γ u W d' p)
        + (G (u p) (covDerivAlong Γ u V d' p) (covDerivAlong Γ u W d p)
          + G (u p) (V p) (covDerivAlong Γ u (covDerivAlong Γ u W d) d' p)) := by
    intro d d'
    have hDV := hcov V hV d
    have hDW := hcov W hW d
    have hGp : DifferentiableAt ℝ G (u p) := hGev.self_of_nhds
    have hup : DifferentiableAt ℝ u p := hu.differentiableAt (by norm_num)
    have hVp : DifferentiableAt ℝ V p := hV.differentiableAt (by norm_num)
    have hWp : DifferentiableAt ℝ W p := hW.differentiableAt (by norm_num)
    have hsum : HasFDerivAt (fun q => G (u q) (covDerivAlong Γ u V d q) (W q)
          + G (u q) (V q) (covDerivAlong Γ u W d q))
        (fderiv ℝ (fun q => G (u q) (covDerivAlong Γ u V d q) (W q)) p
          + fderiv ℝ (fun q => G (u q) (V q) (covDerivAlong Γ u W d q)) p) p :=
      (differentiableAt_metricAlong hGp hup hDV hWp).hasFDerivAt.add
        (differentiableAt_metricAlong hGp hup hVp hDW).hasFDerivAt
    rw [Filter.EventuallyEq.fderiv_eq (hfirst d), hsum.fderiv]
    simp only [ContinuousLinearMap.add_apply]
    rw [fderiv_metricAlong hcompat.self_of_nhds hGp hup hDV hWp d',
      fderiv_metricAlong hcompat.self_of_nhds hGp hup hVp hDW d']
  -- Schwarz symmetry of the scalar second derivative
  have hswap : fderiv ℝ (fun q => fderiv ℝ A q d₂) p d₁
      = fderiv ℝ (fun q => fderiv ℝ A q d₁) p d₂ := by
    rw [fderiv_fderiv_apply_dir hA2 d₂, fderiv_fderiv_apply_dir hA2 d₁]
    simp only [ContinuousLinearMap.flip_apply]
    exact (hA2.isSymmSndFDerivAt (by simp)).eq d₁ d₂
  have h₁ := hsecond d₂ d₁
  have h₂ := hsecond d₁ d₂
  rw [h₁, h₂] at hswap
  -- the curvature commutation identities for `V` and for `W`
  have hcV := covDerivAlong_comm hu hV hΓ d₁ d₂
  have hcW := covDerivAlong_comm hu hW hΓ d₁ d₂
  have hRV : christoffelCurvature Γ (u p) (fderiv ℝ u p d₁) (fderiv ℝ u p d₂) (V p)
      = covDerivAlong Γ u (covDerivAlong Γ u V d₂) d₁ p
        - covDerivAlong Γ u (covDerivAlong Γ u V d₁) d₂ p := hcV.symm
  have hRW : christoffelCurvature Γ (u p) (fderiv ℝ u p d₁) (fderiv ℝ u p d₂) (W p)
      = covDerivAlong Γ u (covDerivAlong Γ u W d₂) d₁ p
        - covDerivAlong Γ u (covDerivAlong Γ u W d₁) d₂ p := hcW.symm
  rw [hRV, hRW]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  linarith [hswap]

/-! ### The energy density and its first variation -/

/-- **Math.** The **energy density** of the family `u` in the direction `dt`:
`½ G(∂_t u, ∂_t u)`.  Integrating it in `t` gives Morgan–Tian's energy
`E(γ) = ½∫|γ′|²`. -/
def energyDensity (G : E → E →L[ℝ] E →L[ℝ] ℝ) (u : P → E) (dt : P) : P → ℝ :=
  fun p => (1 / 2 : ℝ) * G (u p) (fderiv ℝ u p dt) (fderiv ℝ u p dt)

/-- **Math.** **The first variation of the energy density.**

`∂_s (½ G(∂_t u, ∂_t u)) = G(∇_t ∂_s u, ∂_t u)`.

Metric compatibility differentiates the metric, and torsion-freeness
(`covDerivAlong_fderiv_symm`) turns `∇_s ∂_t u` into `∇_t ∂_s u` — after which the
`t`-derivative is exposed and one may integrate by parts.  This is Morgan–Tian's
`dE/du = ∫⟨∇_X Y, X⟩`. -/
theorem fderiv_energyDensity {G : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hGsymm : ∀ x X Y, G x X Y = G x Y X) {u : P → E} {p : P}
    (hcompat : IsMetricCompatibleAt G Γ (u p))
    (hΓsymm : ∀ x X Y, Γ x X Y = Γ x Y X)
    (hG : DifferentiableAt ℝ G (u p)) (hu : ContDiffAt ℝ 2 u p) (ds dt : P) :
    fderiv ℝ (energyDensity G u dt) p ds
      = G (u p) (covDerivAlong Γ u (fun r => fderiv ℝ u r ds) dt p) (fderiv ℝ u p dt) := by
  have hup : DifferentiableAt ℝ u p := hu.differentiableAt (by norm_num)
  have hX : DifferentiableAt ℝ (fun q => fderiv ℝ u q dt) p := by
    have : ContDiffAt ℝ 1 (fun q => fderiv ℝ u q dt) p :=
      (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    exact this.differentiableAt (by norm_num)
  have hdiff : DifferentiableAt ℝ
      (fun q => G (u q) (fderiv ℝ u q dt) (fderiv ℝ u q dt)) p :=
    differentiableAt_metricAlong hG hup hX hX
  have hbase := fderiv_metricAlong hcompat hG hup hX hX ds
  -- torsion-freeness: `∇_s ∂_t u = ∇_t ∂_s u`
  have hsymm : covDerivAlong Γ u (fun r => fderiv ℝ u r dt) ds p
      = covDerivAlong Γ u (fun r => fderiv ℝ u r ds) dt p :=
    covDerivAlong_fderiv_symm hu (fun X Y => hΓsymm (u p) X Y) ds dt
  have hED : energyDensity G u dt
      = fun q => (1 / 2 : ℝ) * G (u q) (fderiv ℝ u q dt) (fderiv ℝ u q dt) := rfl
  rw [hED, fderiv_const_mul hdiff, ContinuousLinearMap.smul_apply, smul_eq_mul, hbase, hsymm]
  rw [hGsymm (u p) (fderiv ℝ u p dt) (covDerivAlong Γ u (fun r => fderiv ℝ u r ds) dt p)]
  ring

/-! ### The second variation -/

/-- **Math.** **The second variation of energy — the index form.**

Let `u : P → E` be a `C³` two-parameter family read in a chart, `X = ∂_t u`,
`Y = ∂_s u`, and suppose the `t`-line through `p` is a **geodesic at `p`**
(`∇_t ∂_t u = 0` at `p` — nothing is assumed at other points).  Then

`∂_s∂_s (½ G(X, X)) = ∂_t G(∇_s ∂_s u, X) + G(∇_t Y, ∇_t Y) − G(R(Y, X)X, Y).`

The last two terms are **exactly Morgan–Tian's index-form integrand**
`⟨∇_X Y, ∇_X Y⟩ − ⟨ℛ(Y,X)X, Y⟩` (`IndexForm.indexIntegrand`), and the first is a
total `t`-derivative — the boundary term.

*Proof.*  Differentiate the first variation `∂_s(½G(X,X)) = G(∇_t Y, X)` once more
in `s`, using metric compatibility:

`∂_s G(∇_t Y, X) = G(∇_s∇_t Y, X) + G(∇_t Y, ∇_s X)`.

Torsion-freeness turns `∇_s X` into `∇_t Y`, giving the term `G(∇_t Y, ∇_t Y)`.
Curvature commutation (`covDerivAlong_comm`) turns `∇_s∇_t Y` into
`∇_t (∇_s Y) + R(Y, X) Y`.  For the first piece, compatibility again gives
`G(∇_t (∇_s Y), X) = ∂_t G(∇_s Y, X) − G(∇_s Y, ∇_t X)`, and the geodesic
hypothesis kills the second term.  For the second piece, the curvature is skew in
the metric (`metricAlong_christoffelCurvature_antisymm`), so
`G(R(Y,X)Y, X) = −G(R(Y,X)X, Y)`. ∎

**No exponential map is used.**  The variation is an arbitrary `C³` family in a
chart; the classical construction `α(s,t) = exp_{γ(t)}(sY(t))` — which would need
joint `C²` smoothness of `exp` in basepoint *and* vector, a theorem mathlib does
not have — is not needed, because this identity is local and every point of a
manifold lies in a chart. -/
theorem secondVariation_energyDensity
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E}
    (hGsymm : ∀ x X Y, G x X Y = G x Y X) {u : P → E} {p : P} {ds dt : P}
    (hcompat : ∀ᶠ x in 𝓝 (u p), IsMetricCompatibleAt G Γ x)
    (hΓsymm : ∀ x X Y, Γ x X Y = Γ x Y X)
    (hG : ContDiffAt ℝ 2 G (u p)) (hu : ContDiffAt ℝ 3 u p)
    (hΓ : DifferentiableAt ℝ Γ (u p))
    (hgeo : covDerivAlong Γ u (fun r => fderiv ℝ u r dt) dt p = 0) :
    fderiv ℝ (fun q => fderiv ℝ (energyDensity G u dt) q ds) p ds
      = fderiv ℝ (fun q => G (u q)
            (covDerivAlong Γ u (fun r => fderiv ℝ u r ds) ds q) (fderiv ℝ u q dt)) p dt
        + G (u p) (covDerivAlong Γ u (fun r => fderiv ℝ u r ds) dt p)
            (covDerivAlong Γ u (fun r => fderiv ℝ u r ds) dt p)
        - G (u p) (christoffelCurvature Γ (u p) (fderiv ℝ u p ds) (fderiv ℝ u p dt)
            (fderiv ℝ u p dt)) (fderiv ℝ u p ds) := by
  have hu2 : ContDiffAt ℝ 2 u p := hu.of_le (by norm_num)
  have hup : DifferentiableAt ℝ u p := hu.differentiableAt (by norm_num)
  have hGp : DifferentiableAt ℝ G (u p) := hG.differentiableAt (by norm_num)
  -- the two coordinate velocity fields, and their regularity
  set X : P → E := fun r => fderiv ℝ u r dt with hXdef
  set Y : P → E := fun r => fderiv ℝ u r ds with hYdef
  have hX2 : ContDiffAt ℝ 2 X p :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hY2 : ContDiffAt ℝ 2 Y p :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hXp : DifferentiableAt ℝ X p := hX2.differentiableAt (by norm_num)
  -- differentiability of a covariant-derivative field, as in the antisymmetry proof
  have hcov : ∀ (Z : P → E) (_ : ContDiffAt ℝ 2 Z p) (d : P),
      DifferentiableAt ℝ (covDerivAlong Γ u Z d) p := by
    intro Z hZ d
    have h1 : DifferentiableAt ℝ (fun q => fderiv ℝ Z q d) p := by
      have : ContDiffAt ℝ 1 (fun q => fderiv ℝ Z q d) p :=
        (hZ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
      exact this.differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (fun q => Γ (u q)) p := by
      have h : HasFDerivAt (fun q => Γ (u q)) ((fderiv ℝ Γ (u p)).comp (fderiv ℝ u p)) p := by
        simpa [Function.comp_def] using
          HasFDerivAt.comp (x := p) (g := Γ) (f := u) hΓ.hasFDerivAt hup.hasFDerivAt
      exact h.differentiableAt
    have h3 : DifferentiableAt ℝ (fun q => fderiv ℝ u q d) p := by
      have : ContDiffAt ℝ 1 (fun q => fderiv ℝ u q d) p :=
        (hu2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
      exact this.differentiableAt (by norm_num)
    have h4 : DifferentiableAt ℝ Z p := hZ.differentiableAt (by norm_num)
    have hfun : covDerivAlong Γ u Z d =
        (fun q => fderiv ℝ Z q d) +
          fun q => Γ (u q) (fderiv ℝ u q d) (Z q) := by
      funext q
      rfl
    rw [hfun]
    exact h1.add ((h2.clm_apply h3).clm_apply h4)
  -- ### Step 1: the first variation, valid near `p`
  have hGev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ G (u q) := by
    have h : ∀ᶠ x in 𝓝 (u p), DifferentiableAt ℝ G x := by
      filter_upwards [hG.eventually (by simp)] with x hx
      exact hx.differentiableAt (by norm_num)
    exact hu.continuousAt.eventually h
  have huev : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 u q := by
    filter_upwards [hu.eventually (by simp)] with q hq
    exact hq.of_le (by norm_num)
  have hcev : ∀ᶠ q in 𝓝 p, IsMetricCompatibleAt G Γ (u q) := hu.continuousAt.eventually hcompat
  have hfirst : (fun q => fderiv ℝ (energyDensity G u dt) q ds)
      =ᶠ[𝓝 p] fun q => G (u q) (covDerivAlong Γ u Y dt q) (X q) := by
    filter_upwards [hGev, huev, hcev] with q hGq huq hcq
    exact fderiv_energyDensity hGsymm hcq hΓsymm hGq huq ds dt
  rw [Filter.EventuallyEq.fderiv_eq hfirst]
  -- ### Step 2: differentiate the first variation once more in `s`
  have hDY : DifferentiableAt ℝ (covDerivAlong Γ u Y dt) p := hcov Y hY2 dt
  rw [fderiv_metricAlong hcompat.self_of_nhds hGp hup hDY hXp ds]
  -- torsion-freeness: `∇_s X = ∇_t Y`
  have hsymm : covDerivAlong Γ u X ds p = covDerivAlong Γ u Y dt p :=
    covDerivAlong_fderiv_symm hu2 (fun A B => hΓsymm (u p) A B) ds dt
  rw [hsymm]
  -- ### curvature commutation on the field `Y`
  have hcomm := covDerivAlong_comm hu2 hY2 hΓ ds dt
  have hcommY : covDerivAlong Γ u (covDerivAlong Γ u Y dt) ds p
      = covDerivAlong Γ u (covDerivAlong Γ u Y ds) dt p
        + christoffelCurvature Γ (u p) (fderiv ℝ u p ds) (fderiv ℝ u p dt) (Y p) := by
    rw [← hcomm]; abel
  rw [hcommY, map_add, ContinuousLinearMap.add_apply]
  -- ### the total `t`-derivative: compatibility again, and the geodesic hypothesis
  have hDZ : DifferentiableAt ℝ (covDerivAlong Γ u Y ds) p := hcov Y hY2 ds
  have hbdry := fderiv_metricAlong hcompat.self_of_nhds hGp hup hDZ hXp dt
  rw [hgeo] at hbdry
  simp only [map_zero, add_zero] at hbdry
  rw [hbdry]
  -- ### the curvature is skew in the metric
  have hanti := metricAlong_christoffelCurvature_antisymm (V := Y) (W := X)
    hcompat hG hu2 hY2 hX2 hΓ ds dt
  have hYp : Y p = fderiv ℝ u p ds := rfl
  have hXp' : X p = fderiv ℝ u p dt := rfl
  rw [hYp, hXp'] at hanti
  -- `G(R(Y,X)Y, X) = −G(Y, R(Y,X)X) = −G(R(Y,X)X, Y)`
  have hswapG : G (u p) (fderiv ℝ u p ds)
      (christoffelCurvature Γ (u p) (fderiv ℝ u p ds) (fderiv ℝ u p dt) (fderiv ℝ u p dt))
      = G (u p)
        (christoffelCurvature Γ (u p) (fderiv ℝ u p ds) (fderiv ℝ u p dt) (fderiv ℝ u p dt))
        (fderiv ℝ u p ds) := hGsymm _ _ _
  rw [hswapG] at hanti
  linarith [hanti]

end PoincareMT.ConjugateVariation

end

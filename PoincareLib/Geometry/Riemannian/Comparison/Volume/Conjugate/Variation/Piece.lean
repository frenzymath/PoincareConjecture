import PoincareLib.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Density
import PoincareLib.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Energy
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Second variation on a coordinate interval

Integrating the pointwise second variation gives the index integral and the
endpoint acceleration terms. Adapted from AxelWorkspace,
`formalized-sources/riemannian/MorganTian/MorganTianLib/Geometry/PieceSecondVariation.lean`,
revision `f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e` (Apache-2.0).
Original SHA-256: 99d2bd7f072a1255268cd955d10465193875ebdeb15c21be08daeee73f4cda3f.
License: `references/analysis/axel-workspace/LICENSE.Apache-2.0.txt`.
Imports and namespaces are adapted to the retained connection and metric.
Supports Morgan--Tian, Theorem 1.34, p. 19.
-/

open Set Filter
open scoped Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareMT.ConjugateVariation

open PoincareMT.ConnectionVariation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Slicing a function on the parameter square

The two coordinate slices of a function of `(s, t)` and their derivatives.  These are
the bridges between the `deriv`-in-one-real-variable world of interval integrals and the
`fderiv`-on-`ℝ × ℝ` world of `SecondVariation`. -/

/-- **Math.** The `s`-slice of a function on the parameter square: for `f` differentiable
at `(s, t)`, `σ ↦ f (σ, t)` has derivative `∂_{(1,0)} f (s,t)` at `s`. -/
theorem hasDerivAt_slice_fst {f : ℝ × ℝ → ℝ} {s t : ℝ} (hf : DifferentiableAt ℝ f (s, t)) :
    HasDerivAt (fun σ => f (σ, t)) (fderiv ℝ f (s, t) ((1 : ℝ), (0 : ℝ))) s :=
  hf.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))

/-- **Math.** `deriv` form of `hasDerivAt_slice_fst`. -/
theorem deriv_slice_fst {f : ℝ × ℝ → ℝ} {s t : ℝ} (hf : DifferentiableAt ℝ f (s, t)) :
    deriv (fun σ => f (σ, t)) s = fderiv ℝ f (s, t) ((1 : ℝ), (0 : ℝ)) :=
  (hasDerivAt_slice_fst hf).deriv

/-- **Math.** The `t`-slice of a function on the parameter square: for `f` differentiable
at `(s, t)`, `τ ↦ f (s, τ)` has derivative `∂_{(0,1)} f (s,t)` at `t`. -/
theorem hasDerivAt_slice_snd {f : ℝ × ℝ → ℝ} {s t : ℝ} (hf : DifferentiableAt ℝ f (s, t)) :
    HasDerivAt (fun τ => f (s, τ)) (fderiv ℝ f (s, t) ((0 : ℝ), (1 : ℝ))) t :=
  hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))

/-- **Math.** `deriv` form of `hasDerivAt_slice_snd`. -/
theorem deriv_slice_snd {f : ℝ × ℝ → ℝ} {s t : ℝ} (hf : DifferentiableAt ℝ f (s, t)) :
    deriv (fun τ => f (s, τ)) t = fderiv ℝ f (s, t) ((0 : ℝ), (1 : ℝ)) :=
  (hasDerivAt_slice_snd hf).deriv

/-! ### Regularity of the chart data

The metric `G` and the connection coefficients `Γ` are **only defined where the chart is**:
for the genuine Levi-Civita data `G = chartMetricBilin g α`, `Γ = chartChristoffelBilin g α`
the Gram matrix is junk outside the chart target, so no *global* regularity or compatibility
statement about them is ever provable.  Everything below is therefore localized to an open
set `U : Set E` — the honest domain of the chart data (see
`Ch01/ChartMetricCompatible.isMetricCompatibleAt_chartMetricBilin`, whose conclusion holds
exactly on `interior (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (trivialization
base set)`).

The *family* `u`, by contrast, keeps its **global** regularity: it is an `E`-valued function
of the parameters `(s, t)`, built by the caller out of one-variable data that can be
bump-extended, so `ContDiff ℝ 3 u` is arrangeable.  The bridge between the two is a
`Set.MapsTo u s U` hypothesis: the parameters we care about land in `U`. -/

section Regularity

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **Math.** The covariant derivative along a map of `C²` data with `C¹` coefficients is
`C¹`: `∇_d V = ∂_d V + Γ_u(∂_d u, V)`.  Localized: `Γ` is only `C¹` on `U`, and the
parameters `s` are required to land in `U`. -/
theorem contDiffOn_covDerivAlong {Γ : E → E →L[ℝ] E →L[ℝ] E} {u V : P → E}
    {U : Set E} {s : Set P} (hΓ : ContDiffOn ℝ 1 Γ U) (hu : ContDiff ℝ 2 u)
    (hV : ContDiff ℝ 2 V) (hmaps : Set.MapsTo u s U) (d : P) :
    ContDiffOn ℝ 1 (covDerivAlong Γ u V d) s := by
  have h1 : ContDiff ℝ 1 (fun q : P => fderiv ℝ V q d) :=
    (hV.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h2 : ContDiffOn ℝ 1 (fun q : P => Γ (u q)) s :=
    hΓ.comp (hu.of_le (by norm_num)).contDiffOn hmaps
  have h3 : ContDiff ℝ 1 (fun q : P => fderiv ℝ u q d) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h4 : ContDiff ℝ 1 V := hV.of_le (by norm_num)
  have h : covDerivAlong Γ u V d
      = fun q : P => fderiv ℝ V q d + Γ (u q) (fderiv ℝ u q d) (V q) := rfl
  rw [h]
  exact h1.contDiffOn.add ((h2.clm_apply h3.contDiffOn).clm_apply h4.contDiffOn)

/-- **Math.** The energy density `½ G(∂_t u, ∂_t u)` of a `C³` family with a metric that is
`C²` on `U` is `C²` wherever the family lands in `U`. -/
theorem contDiffOn_energyDensity {G : E → E →L[ℝ] E →L[ℝ] ℝ} {u : P → E}
    {U : Set E} {s : Set P} (hG : ContDiffOn ℝ 2 G U) (hu : ContDiff ℝ 3 u)
    (hmaps : Set.MapsTo u s U) (dt : P) :
    ContDiffOn ℝ 2 (energyDensity G u dt) s := by
  have hX : ContDiff ℝ 2 (fun q : P => fderiv ℝ u q dt) :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hGu : ContDiffOn ℝ 2 (fun q : P => G (u q)) s :=
    hG.comp (hu.of_le (by norm_num)).contDiffOn hmaps
  have h : energyDensity G u dt
      = fun q : P => (1 / 2 : ℝ) * G (u q) (fderiv ℝ u q dt) (fderiv ℝ u q dt) := rfl
  rw [h]
  exact contDiffOn_const.mul ((hGu.clm_apply hX.contDiffOn).clm_apply hX.contDiffOn)

end Regularity

/-! ### The two ingredients of the piecewise second variation -/

/-- **Math.** The index-form integrand of Morgan–Tian, read in a chart:
`G(∇_t Y, ∇_t Y) − G(R(Y, X) X, Y)` with `X = ∂_t u`, `Y = ∂_s u`. -/
def chartIndexIntegrand (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (u : ℝ × ℝ → E) (t : ℝ) : ℝ :=
  G (u (0, t))
      (covDerivAlong Γ u (fun q => fderiv ℝ u q (1, 0)) (0, 1) (0, t))
      (covDerivAlong Γ u (fun q => fderiv ℝ u q (1, 0)) (0, 1) (0, t))
    - G (u (0, t))
        (christoffelCurvature Γ (u (0, t)) (fderiv ℝ u (0, t) (1, 0))
          (fderiv ℝ u (0, t) (0, 1)) (fderiv ℝ u (0, t) (0, 1)))
        (fderiv ℝ u (0, t) (1, 0))

/-- **Math.** The boundary term `Φ(t) = G(∇_s ∂_s u, ∂_t u)` of the second variation. -/
def secondVariationBoundary (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (u : ℝ × ℝ → E) (t : ℝ) : ℝ :=
  G (u (0, t))
    (covDerivAlong Γ u (fun q => fderiv ℝ u q (1, 0)) (1, 0) (0, t))
    (fderiv ℝ u (0, t) (0, 1))

section Piece

variable {G : E → E →L[ℝ] E →L[ℝ] ℝ} {Γ : E → E →L[ℝ] E →L[ℝ] E} {u : ℝ × ℝ → E}

/-- The boundary term of the second variation as a function on the whole parameter square;
`secondVariationBoundary` is its restriction to the line `s = 0`. -/
private def boundaryFun (G : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (u : ℝ × ℝ → E) : ℝ × ℝ → ℝ :=
  fun q => G (u q) (covDerivAlong Γ u (fun r => fderiv ℝ u r ((1 : ℝ), (0 : ℝ)))
    ((1 : ℝ), (0 : ℝ)) q) (fderiv ℝ u q ((0 : ℝ), (1 : ℝ)))

private theorem contDiffOn_boundaryFun {U : Set E} {s : Set (ℝ × ℝ)}
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U) (hu : ContDiff ℝ 3 u)
    (hmaps : Set.MapsTo u s U) : ContDiffOn ℝ 1 (boundaryFun G Γ u) s := by
  have hY2 : ContDiff ℝ 2 (fun r : ℝ × ℝ => fderiv ℝ u r ((1 : ℝ), (0 : ℝ))) :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hcov : ContDiffOn ℝ 1 (covDerivAlong Γ u
      (fun r : ℝ × ℝ => fderiv ℝ u r ((1 : ℝ), (0 : ℝ))) ((1 : ℝ), (0 : ℝ))) s :=
    contDiffOn_covDerivAlong hΓ (hu.of_le (by norm_num)) hY2 hmaps _
  have hX1 : ContDiff ℝ 1 (fun q : ℝ × ℝ => fderiv ℝ u q ((0 : ℝ), (1 : ℝ))) :=
    ((hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).of_le (by norm_num)
  have hGu : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => G (u q)) s :=
    (hG.of_le (by norm_num)).comp (hu.of_le (by norm_num)).contDiffOn hmaps
  exact (hGu.clm_apply hcov).clm_apply hX1.contDiffOn

/-- **Math.** The boundary term `Φ` of the second variation is `C¹` on any set of times whose
line `s = 0` lands in the domain `U` of the chart data. -/
theorem contDiffOn_secondVariationBoundary {U : Set E} {J : Set ℝ}
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U) (hu : ContDiff ℝ 3 u)
    (hJ : ∀ t ∈ J, u ((0 : ℝ), t) ∈ U) :
    ContDiffOn ℝ 1 (secondVariationBoundary G Γ u) J := by
  have hb : ContDiffOn ℝ 1 (boundaryFun G Γ u) (u ⁻¹' U) :=
    contDiffOn_boundaryFun hG hΓ hu (fun q hq => hq)
  have hline : ContDiff ℝ 1 (fun t : ℝ => ((0 : ℝ), t)) := contDiff_const.prodMk contDiff_id
  exact hb.comp hline.contDiffOn (fun t ht => hJ t ht)

/-- **Math.** The index-form integrand is continuous on any set of times whose line `s = 0`
lands in the domain `U` of the chart data — hence interval-integrable there. -/
theorem continuousOn_chartIndexIntegrand {U : Set E} {J : Set ℝ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U) (hu : ContDiff ℝ 3 u)
    (hJ : ∀ t ∈ J, u ((0 : ℝ), t) ∈ U) :
    ContinuousOn (chartIndexIntegrand G Γ u) J := by
  have hline : Continuous (fun t : ℝ => ((0 : ℝ), t)) := continuous_const.prodMk continuous_id
  have hmapsW : Set.MapsTo u (u ⁻¹' U) U := fun q hq => hq
  have hmapsJ : Set.MapsTo (fun t : ℝ => ((0 : ℝ), t)) J (u ⁻¹' U) := fun t ht => hJ t ht
  have hY2 : ContDiff ℝ 2 (fun r : ℝ × ℝ => fderiv ℝ u r ((1 : ℝ), (0 : ℝ))) :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hT2 : ContDiff ℝ 2 (fun r : ℝ × ℝ => fderiv ℝ u r ((0 : ℝ), (1 : ℝ))) :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hx : ContinuousOn (fun t : ℝ => u ((0 : ℝ), t)) J := (hu.continuous.comp hline).continuousOn
  have hxmaps : Set.MapsTo (fun t : ℝ => u ((0 : ℝ), t)) J U := fun t ht => hJ t ht
  have hX : ContinuousOn (fun t : ℝ => fderiv ℝ u ((0 : ℝ), t) ((1 : ℝ), (0 : ℝ))) J :=
    (hY2.continuous.comp hline).continuousOn
  have hT : ContinuousOn (fun t : ℝ => fderiv ℝ u ((0 : ℝ), t) ((0 : ℝ), (1 : ℝ))) J :=
    (hT2.continuous.comp hline).continuousOn
  have hD : ContinuousOn (fun t : ℝ => covDerivAlong Γ u
      (fun r : ℝ × ℝ => fderiv ℝ u r ((1 : ℝ), (0 : ℝ))) ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), t)) J :=
    (contDiffOn_covDerivAlong hΓ (hu.of_le (by norm_num)) hY2 hmapsW _).continuousOn.comp
      hline.continuousOn hmapsJ
  have hΓc : ContinuousOn (fun t : ℝ => Γ (u ((0 : ℝ), t))) J := hΓ.continuousOn.comp hx hxmaps
  have hdΓ : ContinuousOn (fun t : ℝ => fderiv ℝ Γ (u ((0 : ℝ), t))) J :=
    (hΓ.continuousOn_fderiv_of_isOpen hU le_rfl).comp hx hxmaps
  have hGc : ContinuousOn (fun t : ℝ => G (u ((0 : ℝ), t))) J := hG.continuousOn.comp hx hxmaps
  have hR : ContinuousOn (fun t : ℝ => christoffelCurvature Γ (u ((0 : ℝ), t))
      (fderiv ℝ u ((0 : ℝ), t) ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ u ((0 : ℝ), t) ((0 : ℝ), (1 : ℝ)))
      (fderiv ℝ u ((0 : ℝ), t) ((0 : ℝ), (1 : ℝ)))) J :=
    ((((hdΓ.clm_apply hX).clm_apply hT).clm_apply hT).sub
        (((hdΓ.clm_apply hT).clm_apply hX).clm_apply hT)
      |>.add ((hΓc.clm_apply hX).clm_apply ((hΓc.clm_apply hT).clm_apply hT)))
      |>.sub ((hΓc.clm_apply hT).clm_apply ((hΓc.clm_apply hX).clm_apply hT))
  exact ((hGc.clm_apply hD).clm_apply hD).sub ((hGc.clm_apply hR).clm_apply hX)

/-- **Math.** The pointwise second `s`-derivative of the energy density on the line `s = 0`,
split into a total `t`-derivative of the boundary term and the index-form integrand.

This is `secondVariation_energyDensity` rewritten in terms of one-variable derivatives of
the slices, so that it can be integrated in `t`. -/
theorem deriv_deriv_slice_energyDensity {t : ℝ} {U : Set E} (hU : IsOpen U)
    (hGsymm : ∀ x X Y, G x X Y = G x Y X)
    (hΓsymm : ∀ x X Y, Γ x X Y = Γ x Y X)
    (hcompat : ∀ x ∈ U, IsMetricCompatibleAt G Γ x)
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U) (hu : ContDiff ℝ 3 u)
    (hmem : u ((0 : ℝ), t) ∈ U)
    (hgeo : covDerivAlong Γ u (fun q => fderiv ℝ u q (0, 1)) (0, 1) (0, t) = 0) :
    deriv (fun σ : ℝ => deriv (fun ρ : ℝ => energyDensity G u ((0 : ℝ), (1 : ℝ)) (ρ, t)) σ) 0
      = deriv (secondVariationBoundary G Γ u) t + chartIndexIntegrand G Γ u t := by
  -- the open set of parameters that land in the domain `U` of the chart data
  have hWopen : IsOpen (u ⁻¹' U) := hU.preimage hu.continuous
  have hmapsW : Set.MapsTo u (u ⁻¹' U) U := fun q hq => hq
  have hW0 : ((0 : ℝ), t) ∈ u ⁻¹' U := hmem
  have hWnhds : u ⁻¹' U ∈ 𝓝 ((0 : ℝ), t) := hWopen.mem_nhds hW0
  have hUnhds : U ∈ 𝓝 (u ((0 : ℝ), t)) := hU.mem_nhds hmem
  have hf2 : ContDiffOn ℝ 2 (energyDensity G u ((0 : ℝ), (1 : ℝ))) (u ⁻¹' U) :=
    contDiffOn_energyDensity hG hu hmapsW _
  -- the inner `s`-derivative, as a function of `σ`, *near* `σ = 0`
  have hsliceOpen : IsOpen {σ : ℝ | (σ, t) ∈ u ⁻¹' U} :=
    hWopen.preimage (continuous_id.prodMk continuous_const)
  have hinner :
      (fun σ : ℝ => deriv (fun ρ : ℝ => energyDensity G u ((0 : ℝ), (1 : ℝ)) (ρ, t)) σ)
        =ᶠ[𝓝 (0 : ℝ)] fun σ : ℝ =>
          fderiv ℝ (energyDensity G u ((0 : ℝ), (1 : ℝ))) (σ, t) ((1 : ℝ), (0 : ℝ)) := by
    filter_upwards [hsliceOpen.mem_nhds (show (0 : ℝ) ∈ {σ : ℝ | (σ, t) ∈ u ⁻¹' U} from hW0)]
      with σ hσ
    exact deriv_slice_fst
      ((hf2.contDiffAt (hWopen.mem_nhds hσ)).differentiableAt (by norm_num))
  -- the outer `s`-derivative
  have hg1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ =>
      fderiv ℝ (energyDensity G u ((0 : ℝ), (1 : ℝ))) q ((1 : ℝ), (0 : ℝ))) (u ⁻¹' U) :=
    (hf2.fderiv_of_isOpen hWopen (m := 1) (by norm_num)).clm_apply contDiffOn_const
  have houter : HasDerivAt
      (fun σ : ℝ => fderiv ℝ (energyDensity G u ((0 : ℝ), (1 : ℝ))) (σ, t) ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ (fun q : ℝ × ℝ =>
          fderiv ℝ (energyDensity G u ((0 : ℝ), (1 : ℝ))) q ((1 : ℝ), (0 : ℝ)))
        ((0 : ℝ), t) ((1 : ℝ), (0 : ℝ))) 0 :=
    hasDerivAt_slice_fst (f := fun q : ℝ × ℝ =>
      fderiv ℝ (energyDensity G u ((0 : ℝ), (1 : ℝ))) q ((1 : ℝ), (0 : ℝ)))
      ((hg1.contDiffAt hWnhds).differentiableAt (by norm_num))
  rw [hinner.deriv_eq, houter.deriv]
  -- the engine: `U` is open, so compatibility at `u p` holds on a whole neighbourhood
  have hsv := secondVariation_energyDensity (G := G) (Γ := Γ) (u := u) (p := ((0 : ℝ), t))
    (ds := ((1 : ℝ), (0 : ℝ))) (dt := ((0 : ℝ), (1 : ℝ)))
    hGsymm (by filter_upwards [hUnhds] with x hx using hcompat x hx) hΓsymm
    (hG.contDiffAt hUnhds) hu.contDiffAt
    ((hΓ.contDiffAt hUnhds).differentiableAt (by norm_num)) hgeo
  rw [hsv]
  -- the boundary term, as a `t`-derivative along the line `s = 0`
  have hbdry : deriv (secondVariationBoundary G Γ u) t
      = fderiv ℝ (fun q : ℝ × ℝ => G (u q)
          (covDerivAlong Γ u (fun r => fderiv ℝ u r ((1 : ℝ), (0 : ℝ)))
            ((1 : ℝ), (0 : ℝ)) q) (fderiv ℝ u q ((0 : ℝ), (1 : ℝ))))
          ((0 : ℝ), t) ((0 : ℝ), (1 : ℝ)) :=
    (hasDerivAt_slice_snd (f := boundaryFun G Γ u)
      (((contDiffOn_boundaryFun hG hΓ hu hmapsW).contDiffAt hWnhds).differentiableAt (by norm_num))).deriv
  rw [hbdry, chartIndexIntegrand]
  ring

/-- **Math.** **The second variation of the energy of one piece, with its boundary term.**

For a `C³` chart family `u` whose `t`-lines are geodesic on `[τ₀, τ₁]` at `s = 0`,

`d²/ds² E_piece(0) = (Φ(τ₁) − Φ(τ₀)) + ∫_{τ₀}^{τ₁} (G(∇_t Y, ∇_t Y) − G(R(Y,X)X, Y)) dt`,

with `Φ = secondVariationBoundary` the boundary term `G(∇_s ∂_s u, ∂_t u)`.

*Proof.*  Differentiate under the integral sign twice
(`deriv_deriv_intervalIntegral_of_contDiffOn_box`); identify the integrand with the
pointwise second variation (`secondVariation_energyDensity`, via
`deriv_deriv_slice_energyDensity`); and integrate the total `t`-derivative by the
fundamental theorem of calculus. ∎ -/
theorem deriv_deriv_pieceEnergy_eq_boundary_add_integral {τ₀ τ₁ r : ℝ} {U : Set E}
    (hτ : τ₀ ≤ τ₁) (hr : 0 < r) (hU : IsOpen U)
    (hGsymm : ∀ x X Y, G x X Y = G x Y X)
    (hΓsymm : ∀ x X Y, Γ x X Y = Γ x Y X)
    (hcompat : ∀ x ∈ U, IsMetricCompatibleAt G Γ x)
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U)
    (hu : ContDiff ℝ 3 u)
    (humem : ∀ p ∈ Set.Ioo (-r) r ×ˢ Set.Ioo (τ₀ - r) (τ₁ + r), u p ∈ U)
    (hgeo : ∀ t ∈ Set.Icc τ₀ τ₁,
      covDerivAlong Γ u (fun q => fderiv ℝ u q (0, 1)) (0, 1) (0, t) = 0) :
    deriv (deriv (fun s => ∫ t in τ₀..τ₁, energyDensity G u (0, 1) (s, t))) 0
      = (secondVariationBoundary G Γ u τ₁ - secondVariationBoundary G Γ u τ₀)
        + ∫ t in τ₀..τ₁, chartIndexIntegrand G Γ u t := by
  -- the enlarged open time interval, on which the line `s = 0` still lands in `U`
  set J : Set ℝ := Set.Ioo (τ₀ - r) (τ₁ + r) with hJdef
  have hJmem : ∀ t ∈ J, u ((0 : ℝ), t) ∈ U := fun t ht =>
    humem ((0 : ℝ), t) ⟨⟨by linarith, by linarith⟩, ht⟩
  have hsub : Set.uIcc τ₀ τ₁ ⊆ J := by
    rw [Set.uIcc_of_le hτ]
    exact fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- STEP B: differentiate under the integral sign, twice
  have hf2 : ContDiffOn ℝ 2 (energyDensity G u ((0 : ℝ), (1 : ℝ)))
      (Set.Ioo ((0 : ℝ) - r) ((0 : ℝ) + r) ×ˢ Set.Ioo (τ₀ - r) (τ₁ + r)) := by
    refine contDiffOn_energyDensity hG hu (fun p hp => humem p ⟨?_, hp.2⟩) _
    have := hp.1
    simpa using this
  have hbox : deriv (deriv
        (fun s : ℝ => ∫ t in τ₀..τ₁, energyDensity G u ((0 : ℝ), (1 : ℝ)) (s, t))) 0
      = ∫ t in τ₀..τ₁, deriv
          (fun σ : ℝ => deriv (fun ρ : ℝ => energyDensity G u ((0 : ℝ), (1 : ℝ)) (ρ, t)) σ) 0 :=
    deriv_deriv_intervalIntegral_of_contDiffOn_box hτ hr hf2
  rw [hbox]
  -- STEP C: identify the integrand
  have hpt : ∀ t ∈ Set.uIcc τ₀ τ₁,
      deriv (fun σ : ℝ =>
          deriv (fun ρ : ℝ => energyDensity G u ((0 : ℝ), (1 : ℝ)) (ρ, t)) σ) 0
        = deriv (secondVariationBoundary G Γ u) t + chartIndexIntegrand G Γ u t := by
    intro t ht
    have htJ : t ∈ J := hsub ht
    rw [Set.uIcc_of_le hτ] at ht
    exact deriv_deriv_slice_energyDensity hU hGsymm hΓsymm hcompat hG hΓ hu (hJmem t htJ)
      (hgeo t ht)
  rw [intervalIntegral.integral_congr hpt]
  -- STEP E: split the integral
  have hΦ1 : ContDiffOn ℝ 1 (secondVariationBoundary G Γ u) J :=
    contDiffOn_secondVariationBoundary hG hΓ hu hJmem
  have hcΦ : ContinuousOn (deriv (secondVariationBoundary G Γ u)) J :=
    hΦ1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hcI : ContinuousOn (chartIndexIntegrand G Γ u) J :=
    continuousOn_chartIndexIntegrand hU hG hΓ hu hJmem
  rw [intervalIntegral.integral_add ((hcΦ.mono hsub).intervalIntegrable)
    ((hcI.mono hsub).intervalIntegrable)]
  -- STEP D: the fundamental theorem of calculus on the boundary term.  `J` is open and
  -- contains `[τ₀, τ₁]`, so the boundary function is genuinely (two-sidedly) differentiable
  -- at every point of the closed interval.
  have hftc : (∫ t in τ₀..τ₁, deriv (secondVariationBoundary G Γ u) t)
      = secondVariationBoundary G Γ u τ₁ - secondVariationBoundary G Γ u τ₀ :=
    intervalIntegral.integral_deriv_eq_sub' _ rfl
      (fun x hx =>
        (hΦ1.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt (by norm_num))
      (hcΦ.mono hsub)
  rw [hftc]

/-- **Math.** **The second variation of the energy of one piece of a broken variation.**

If, in addition, the two **junction curves** `s ↦ u(s, τ₀)` and `s ↦ u(s, τ₁)` are
*geodesics* at `s = 0` — which is exactly `∇_s ∂_s u = 0` there, the chart geodesic ODE
`ĉ''(0) + Γ(ĉ(0))(ĉ'(0), ĉ'(0)) = 0` — then the boundary term of this piece vanishes at
**both** ends, and

`d²/ds² E_piece(0) = ∫_{τ₀}^{τ₁} (G(∇_t Y, ∇_t Y) − G(R(Y,X)X, Y)) dt`,

the index form of the piece.  Nothing has to be telescoped across pieces: each piece kills
its own boundary term, inside its own chart.  Summing over the pieces of a broken
variation therefore gives `E''(0) = I(Y, Y)` directly. -/
theorem deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand {τ₀ τ₁ r : ℝ} {U : Set E}
    (hτ : τ₀ ≤ τ₁) (hr : 0 < r) (hU : IsOpen U)
    (hGsymm : ∀ x X Y, G x X Y = G x Y X)
    (hΓsymm : ∀ x X Y, Γ x X Y = Γ x Y X)
    (hcompat : ∀ x ∈ U, IsMetricCompatibleAt G Γ x)
    (hG : ContDiffOn ℝ 2 G U) (hΓ : ContDiffOn ℝ 1 Γ U)
    (hu : ContDiff ℝ 3 u)
    (humem : ∀ p ∈ Set.Ioo (-r) r ×ˢ Set.Ioo (τ₀ - r) (τ₁ + r), u p ∈ U)
    (hgeo : ∀ t ∈ Set.Icc τ₀ τ₁,
      covDerivAlong Γ u (fun q => fderiv ℝ u q (0, 1)) (0, 1) (0, t) = 0)
    (hj₀ : covDerivAlong Γ u (fun q => fderiv ℝ u q (1, 0)) (1, 0) (0, τ₀) = 0)
    (hj₁ : covDerivAlong Γ u (fun q => fderiv ℝ u q (1, 0)) (1, 0) (0, τ₁) = 0) :
    deriv (deriv (fun s => ∫ t in τ₀..τ₁, energyDensity G u (0, 1) (s, t))) 0
      = ∫ t in τ₀..τ₁, chartIndexIntegrand G Γ u t := by
  have h₀ : secondVariationBoundary G Γ u τ₀ = 0 := by
    show G (u ((0 : ℝ), τ₀))
      (covDerivAlong Γ u (fun q => fderiv ℝ u q ((1 : ℝ), (0 : ℝ)))
        ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), τ₀)) (fderiv ℝ u ((0 : ℝ), τ₀) ((0 : ℝ), (1 : ℝ))) = 0
    rw [hj₀]
    simp
  have h₁ : secondVariationBoundary G Γ u τ₁ = 0 := by
    show G (u ((0 : ℝ), τ₁))
      (covDerivAlong Γ u (fun q => fderiv ℝ u q ((1 : ℝ), (0 : ℝ)))
        ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), τ₁)) (fderiv ℝ u ((0 : ℝ), τ₁) ((0 : ℝ), (1 : ℝ))) = 0
    rw [hj₁]
    simp
  rw [deriv_deriv_pieceEnergy_eq_boundary_add_integral hτ hr hU hGsymm hΓsymm hcompat hG hΓ hu
    humem hgeo, h₀, h₁]
  ring

end Piece

end PoincareMT.ConjugateVariation

end

import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalDifferenceSource
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorCoherentJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter Metric
open scoped SchwartzMap LineDeriv Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ} {ι : Type*}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem tendsto_principalDifferenceSource
    (A : ι → Fin n → Fin n → 𝓢(V, ℝ)) (B : Fin n → Fin n → 𝓢(V, ℝ))
    (p : List (Fin n) → L2) {l : Filter ι}
    (hA : ∀ i j, Tendsto (fun t => schwartzMultiplier (A t i j - B i j)) l (𝓝 0))
    (hdA : ∀ i j, Tendsto (fun t =>
      schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A t i j - B i j))) l (𝓝 0)) :
    Tendsto (fun t => principalDifferenceSource (A t) B p) l (𝓝 0) := by
  have hterm (i j : Fin n) : Tendsto (fun t =>
      schwartzMultiplier (A t i j - B i j) (p [j, i]) +
        schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A t i j - B i j)) (p [i]))
      l (𝓝 0) := by
    have h1 := ((ContinuousLinearMap.apply ℝ L2 (p [j, i])).continuous.tendsto 0).comp
      (hA i j)
    have h2 := ((ContinuousLinearMap.apply ℝ L2 (p [i])).continuous.tendsto 0).comp
      (hdA i j)
    simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply, zero_apply, zero_add]
      using h1.add h2
  simpa only [principalDifferenceSource, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun i _ =>
      tendsto_finsetSum Finset.univ (fun j _ => hterm i j))

theorem tendsto_weak_secondJet_of_divergence
    (A : ι → Fin n → Fin n → 𝓢(V, ℝ)) (B : Fin n → Fin n → 𝓢(V, ℝ))
    (q : ι → List (Fin n) → L2) (p : List (Fin n) → L2)
    (G : ι → L2) (H : L2) {l : Filter ι}
    (hq : ∀ t, IsWeakSchwartzJet (q t) 2) (hp : IsWeakSchwartzJet p 2)
    {K : Set V} (hK : IsCompact K)
    (hqK : ∀ t, ∀ᵐ x ∂volume, x ∉ K → q t [] x = 0)
    (hpK : ∀ᵐ x ∂volume, x ∉ K → p [] x = 0)
    {r ell D : ℝ} (hr : 0 < r) (hell : 0 < ell) (hD : 0 ≤ D)
    (hEll : ∀ t, ∀ x ∈ cthickening (3 * r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A t i j x * ξ i * ξ j)
    (hAD : ∀ t i j x, ‖fderiv ℝ (A t i j) x‖ ≤ D)
    (hqe : ∀ t, DivergenceEquation (A t) (fun i => q t [i]) (G t)
      (cthickening (3 * r) K))
    (hpe : DivergenceEquation B (fun i => p [i]) H (cthickening (3 * r) K))
    (hG : Tendsto G l (𝓝 H))
    (hfirst : ∀ i, Tendsto (fun t => q t [i]) l (𝓝 (p [i])))
    (hA : ∀ i j, Tendsto (fun t => schwartzMultiplier (A t i j - B i j)) l (𝓝 0))
    (hdA : ∀ i j, Tendsto (fun t =>
      schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A t i j - B i j))) l (𝓝 0))
    (i j : Fin n) : Tendsto (fun t => q t [j, i]) l (𝓝 (p [j, i])) := by
  have hsource : Tendsto (fun t => G t - H + principalDifferenceSource (A t) B p)
      l (𝓝 0) := by
    simpa only [sub_self, zero_add] using
      (hG.sub (tendsto_const_nhds (x := H))).add
        (tendsto_principalDifferenceSource A B p hA hdA)
  have hfirstNorm : Tendsto (fun t => ∑ a : Fin n, ‖q t [a] - p [a]‖) l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun a _ => tendsto_iff_norm_sub_tendsto_zero.mp (hfirst a))
  have hbound (t : ι) : ‖q t [j, i] - p [j, i]‖ ≤
      (‖G t - H + principalDifferenceSource (A t) B p‖ +
        (n : ℝ) * D * (∑ a, ‖q t [a] - p [a]‖)) / ell := by
    have hsupport : ∀ᵐ x ∂volume, x ∉ K → (q t [] - p []) x = 0 := by
      filter_upwards [hqK t, hpK, Lp.coeFn_sub (q t []) (p [])] with x hqx hpx hsub
      intro hx
      rw [hsub, Pi.sub_apply, hqx hx, hpx hx, sub_self]
    exact norm_weakJet_second_le (fun w => q t w - p w) (weakSchwartzJet_sub (hq t) hp)
      hK hsupport (A t) hr hell hD (hEll t) (hAD t) [] (by simp)
      (G t - H + principalDifferenceSource (A t) B p)
      (divergence_equation_sub (A t) B (q t) p hp (hqe t) hpe) i j
  have hlim : Tendsto (fun t =>
      (‖G t - H + principalDifferenceSource (A t) B p‖ +
        (n : ℝ) * D * (∑ a, ‖q t [a] - p [a]‖)) / ell) l (𝓝 0) := by
    simpa only [norm_zero, mul_zero, zero_add, zero_div] using
      (hsource.norm.add (tendsto_const_nhds.mul hfirstNorm)).div_const ell
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hlim)

end PoincareConjecture.M35.Uniqueness.Heat

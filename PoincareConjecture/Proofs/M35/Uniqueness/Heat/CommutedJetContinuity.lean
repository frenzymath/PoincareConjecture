import PoincareConjecture.Proofs.M35.Uniqueness.Heat.EllipticJetContinuity

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

theorem tendsto_weak_commuted_secondJet_of_divergence
    (A : ι → Fin n → Fin n → 𝓢(V, ℝ)) (B : Fin n → Fin n → 𝓢(V, ℝ))
    (q : ι → List (Fin n) → L2) (p : List (Fin n) → L2)
    (G : ι → L2) (H : L2) {l : Filter ι} {s : ℕ}
    (hq : ∀ t, IsWeakSchwartzJet (q t) (s + 2)) (hp : IsWeakSchwartzJet p (s + 2))
    {K : Set V} (hK : IsCompact K)
    (hqK : ∀ t, ∀ᵐ x ∂volume, x ∉ K → q t [] x = 0)
    (hpK : ∀ᵐ x ∂volume, x ∉ K → p [] x = 0)
    {r ell D : ℝ} (hr : 0 < r) (hell : 0 < ell) (hD : 0 ≤ D)
    (hEll : ∀ t, ∀ x ∈ cthickening (3 * r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A t i j x * ξ i * ξ j)
    (hAD : ∀ t i j x, ‖fderiv ℝ (A t i j) x‖ ≤ D)
    (w : List (Fin n)) (hw : w.length ≤ s)
    (hqe : ∀ t, DivergenceEquation (A t) (fun i => q t (i :: w)) (G t)
      (cthickening (3 * r) K))
    (hpe : DivergenceEquation B (fun i => p (i :: w)) H (cthickening (3 * r) K))
    (hG : Tendsto G l (𝓝 H))
    (hfirst : ∀ i, Tendsto (fun t => q t (i :: w)) l (𝓝 (p (i :: w))))
    (hA : ∀ i j, Tendsto (fun t => schwartzMultiplier (A t i j - B i j)) l (𝓝 0))
    (hdA : ∀ i j, Tendsto (fun t =>
      schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A t i j - B i j))) l (𝓝 0))
    (i j : Fin n) : Tendsto (fun t => q t (j :: i :: w)) l (𝓝 (p (j :: i :: w))) := by
  let pp := fun v => p (v ++ w)
  have hpp : IsWeakSchwartzJet pp 2 := by
    intro v hv k
    exact hp (v ++ w) (by simp only [List.length_append]; omega) k
  let source := fun t => G t - H + principalDifferenceSource (A t) B pp
  have hsource : Tendsto source l (𝓝 0) := by
    simpa only [sub_self, zero_add] using
      (hG.sub (tendsto_const_nhds (x := H))).add
        (tendsto_principalDifferenceSource A B pp hA hdA)
  have hfirstNorm : Tendsto (fun t => ∑ k : Fin n, ‖q t (k :: w) - p (k :: w)‖)
      l (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun k _ => tendsto_iff_norm_sub_tendsto_zero.mp (hfirst k))
  have hbound (t : ι) : ‖q t (j :: i :: w) - p (j :: i :: w)‖ ≤
      (‖source t‖ + (n : ℝ) * D * (∑ k, ‖q t (k :: w) - p (k :: w)‖)) / ell := by
    have hsupport : ∀ᵐ x ∂volume, x ∉ K → (q t [] - p []) x = 0 := by
      filter_upwards [hqK t, hpK, Lp.coeFn_sub (q t []) (p [])] with x hqx hpx hsub
      intro hx
      rw [hsub, Pi.sub_apply, hqx hx, hpx hx, sub_self]
    have he := divergence_equation_sub (A t) B (fun v => q t (v ++ w)) pp hpp
      (hqe t) hpe
    exact norm_weakJet_second_le (fun v => q t v - p v)
      (weakSchwartzJet_sub (hq t) hp) hK hsupport (A t) hr hell hD (hEll t) (hAD t)
      w hw (source t) he i j
  have hlim : Tendsto (fun t =>
      (‖source t‖ + (n : ℝ) * D * (∑ k, ‖q t (k :: w) - p (k :: w)‖)) / ell)
      l (𝓝 0) := by
    simpa only [norm_zero, mul_zero, zero_add, zero_div] using
      (hsource.norm.add (tendsto_const_nhds.mul hfirstNorm)).div_const ell
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound hlim)

end PoincareConjecture.M35.Uniqueness.Heat

import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.FiniteCalabi
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.Cutoff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}

theorem exists_distance_cutoff_lower_support_of_flat_finite
    (F : RicciFlow (m + 1) M J)
    {t r Λ scale δ d₀ A B C : ℝ} (ht : t ∈ interior J) (hm : 0 < m)
    (hcomplete : MetricComplete (F.metric t))
    (hRic : ∀ y : M, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ (F.connection t).ricci y v v)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (p x : M)
    (hx : x ∈ (F.metric t).ball p r) (hpx : p ≠ x)
    (hfinite : (F.metric t).edist p x ≠ ⊤)
    (hupper : ∀ y ∈ (F.metric t).ball p r, ∀ v : TangentSpace (𝓡 (m + 1)) y,
      (F.connection t).ricci y v v ≤ Λ * (F.metric t).inner y v v)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ) (hδ : 0 < δ)
    (hflat : ∀ z, z ≤ 1 → χ z = 1) (hd₀ : 0 ≤ d₀)
    (hA : ∀ z, deriv χ z ^ 2 ≤ A * χ z)
    (hB : ∀ z, -B ≤ deriv (deriv χ) z) (hC : ∀ z, -C ≤ deriv χ z)
    (hpos : 0 < χ ((((F.metric t).edist p x).toReal - d₀) / δ)) :
    ∃ (U : Set M) (φ : ℝ → M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ (φ t) U ∧
      φ t x = χ ((((F.metric t).edist p x).toReal - d₀) / δ) ∧
      (∀ s : ℝ, ∀ y ∈ U, φ s y ≤ χ ((((F.metric s).edist p y).toReal - d₀) / δ)) ∧
      DifferentiableAt ℝ (fun s => φ s x) t ∧
      deriv (fun s => φ s x) t - (F.connection t).laplacian (φ t) x +
        2 * (F.metric t).inner x ((F.connection t).gradient (φ t) x)
          ((F.connection t).gradient (φ t) x) / φ t x ≤
        C * (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Λ / scale) / δ +
          (B + 2 * A + 2 * (m : ℝ) * C) / δ ^ 2 := by
  obtain ⟨U, ρ, hU, hxU, hρ, heq, hle, hg, hl, htime, htbound⟩ :=
    F.exists_distance_spacetime_upper_support_of_finite ht hm hcomplete hRic hΛ hscale
      p x hx hpx hupper
  have hd : 0 < ((F.metric t).edist p x).toReal := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 (m + 1)) M
    exact ENNReal.toReal_pos (edist_pos.mpr hpx).ne' hfinite
  let φ : ℝ → M → ℝ := fun s y => χ ((ρ s y - d₀) / δ)
  have hφtime : DifferentiableAt ℝ (fun s => φ s x) t :=
    (hχ.differentiable (by simp) _).comp t ((htime.sub_const d₀).div_const δ)
  refine ⟨U, φ, hU, hxU,
    hχ.contMDiff.comp_contMDiffOn ((hρ.sub contMDiffOn_const).div_const δ),
    by simp only [φ, heq], ?_, hφtime, ?_⟩
  · intro s y hy
    exact hanti (div_le_div_of_nonneg_right (sub_le_sub_right (hle s y hy) d₀) hδ.le)
  · exact (F.connection t).cutoff_heat_le_of_flat_upper_support hU hxU hρ htime
      hχ hanti hflat hδ hd₀ (by positivity) hA hB hC
      (by simpa only [heq] using hd) hg (by simpa only [heq] using hl) htbound
      (by simpa only [heq] using hpos)

end PoincareConjecture.RicciFlow

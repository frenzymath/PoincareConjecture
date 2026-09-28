import PoincareConjecture.Proofs.M76.Mathlib.VariableBandEndpointIncidence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLevelChartTransport

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem FinitePiecewiseAffineOn.exists_geometric_band_level_charts
    {B : Set E} {lower upper : E → ℝ} {T : Set F} {f : E × ℝ → F}
    (hlu : ∀ x ∈ B, lower x ≤ upper x)
    (hf : FinitePiecewiseAffineOn f
      {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)})
    (H : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} ≃ₜ T)
    (hH : ∀ p, (H p : F) = f p) (A : F →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (H p) = (p : E × ℝ).2)
    {g : F → ℝ} (hg : FinitePiecewiseAffineOn g T) (v : F) (hv : A.linear v = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ D : F ≃ₜ F,
      FinitePiecewiseAffineOn (D : F → F) T →
      (∀ y ∈ T, D y = y + (ε * g y) • v) → ∀ c : ℝ,
      ∃ G : {x : E | x ∈ B ∧ c ∈
          Icc (lower x + ε * g (f (x, lower x)))
            (upper x + ε * g (f (x, upper x)))} ≃ₜ
          ((D '' T) ∩ {y | A y = c} : Set F),
        G.IsFinitePL ∧
        ∀ x : {x : E | x ∈ B ∧ c ∈
            Icc (lower x + ε * g (f (x, lower x)))
              (upper x + ε * g (f (x, upper x)))},
          ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)},
            (p : E × ℝ).1 = (x : E) ∧ (G x : F) = D (H p) ∧
            (lower x + ε * g (f (x, lower x)) = c ↔ (p : E × ℝ).2 = lower x) ∧
            (upper x + ε * g (f (x, upper x)) = c ↔ (p : E × ℝ).2 = upper x) := by
  let S : Set (E × ℝ) :=
    {p | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}
  have hmap : MapsTo f S T := by
    intro p hp
    rw [← hH ⟨p, hp⟩]
    exact (H ⟨p, hp⟩).property
  have hgf : FinitePiecewiseAffineOn (g ∘ f) S := hg.comp hf hmap
  obtain ⟨δ, hδ, hcharts⟩ := hgf.exists_variable_band_level_endpoint_charts hlu
  refine ⟨δ, hδ, fun ε hε D hD hDval c => ?_⟩
  obtain ⟨L, hL, hbase, hlower, hupper⟩ := hcharts ε hε c
  let R := H.trans (D.image T)
  have hR : R.IsFinitePL :=
    (show H.IsFinitePL from ⟨f, hf, hH⟩).trans ⟨D, hD, fun _ => rfl⟩
  have hRheight (p : S) : A (R p) = (p : E × ℝ).2 + ε * (g ∘ f) p := by
    change A (D (H p)) = _
    rw [hDval (H p) (H p).property, add_comm (H p : F)]
    change A ((ε * g (H p)) • v +ᵥ (H p : F)) = _
    rw [A.map_vadd, map_smul, hv, hheight p]
    change ε * g (H p) * 1 + (p : E × ℝ).2 =
      (p : E × ℝ).2 + ε * g (f p)
    rw [hH p, mul_one, add_comm]
  obtain ⟨G, hG, hGval⟩ := hR.transport_level_chart hRheight L hL
  refine ⟨G, hG, fun x => ?_⟩
  let p : S := ⟨L x, (L x).property.1⟩
  exact ⟨p, hbase x, hGval x, hlower x, hupper x⟩

end Geometry

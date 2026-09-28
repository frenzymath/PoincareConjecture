import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.Cutoff
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarCutoff







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.RicciFlow

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}




theorem exists_lower_time_support_distance_cutoff_scalarCurvature
    (hTheory : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    {a t r Λ scale δ d₀ A B C Q : ℝ} (ht : t ∈ interior J) (hm : 0 < m)
    (hcomplete : MetricComplete (F.metric t))
    (hRic : ∀ y : M, ∀ w : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ (F.connection t).ricci y w w)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (p x : M)
    (hx : x ∈ (F.metric t).ball p r) (hpx : p ≠ x)
    (hupper : ∀ y ∈ (F.metric t).ball p r, ∀ w : TangentSpace (𝓡 (m + 1)) y,
      (F.connection t).ricci y w w ≤ Λ * (F.metric t).inner y w w)
    (hRicpast : ∀ s ∈ Icc a t, ∀ w : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ (F.connection s).ricci x w w)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ)
    (hχnonneg : ∀ z, 0 ≤ χ z) (hδ : 0 < δ)
    (hflat : ∀ z, z ≤ 1 → χ z = 1) (hd₀ : 0 ≤ d₀)
    (hA₀ : 0 ≤ A) (hB₀ : 0 ≤ B) (hC₀ : 0 ≤ C)
    (hA : ∀ z, deriv χ z ^ 2 ≤ A * χ z)
    (hB : ∀ z, -B ≤ deriv (deriv χ) z) (hC : ∀ z, -C ≤ deriv χ z)
    (hQ : (F.connection t).scalarCurvature x ≤ Q)
    (hpos : 0 < χ ((((F.metric t).edist p x).toReal - d₀) / δ) *
      (F.connection t).scalarCurvature x)
    (hmax : IsLocalMax (fun y =>
      χ ((((F.metric t).edist p y).toReal - d₀) / δ) *
        (F.connection t).scalarCurvature y) x) :
    ∃ (v : ℝ → ℝ) (d : ℝ),
      v t = χ ((((F.metric t).edist p x).toReal - d₀) / δ) *
        (F.connection t).scalarCurvature x ∧
      (∀ᶠ s in 𝓝[Icc a t] t,
        v s ≤ χ ((((F.metric s).edist p x).toReal - d₀) / δ) *
          (F.connection s).scalarCurvature x) ∧
      HasDerivAt v d t ∧
      d ≤ 2 * Q * (χ ((((F.metric t).edist p x).toReal - d₀) / δ) *
        (F.connection t).scalarCurvature x) +
        Q * (C * (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Λ / scale) / δ +
          (B + 2 * A + 2 * (m : ℝ) * C) / δ ^ 2) := by
  have hcutoffpos : 0 < χ ((((F.metric t).edist p x).toReal - d₀) / δ) :=
    lt_of_le_of_ne (hχnonneg _) (by
      intro hz
      rw [← hz, zero_mul] at hpos
      exact (lt_irrefl 0) hpos)
  obtain ⟨U, φ, hU, hxU, hφ, heq, hle, hφtime, hheat⟩ :=
    F.exists_distance_cutoff_lower_support_of_flat ht hm hcomplete hRic hΛ hscale p x
      hx hpx hupper hχ hanti hδ hflat hd₀ hA hB hC hcutoffpos
  have hRnow (y : M) : 0 ≤ (F.connection t).scalarCurvature y :=
    Finset.sum_nonneg (fun _ _ => hRic y _)
  have hRpast (s : ℝ) (hs : s ∈ Icc a t) : 0 ≤ (F.connection s).scalarCurvature x :=
    Finset.sum_nonneg (fun _ _ => hRicpast s hs _)
  have hlocal : IsLocalMax
      (fun y => φ t y * (F.connection t).scalarCurvature y) x := by
    filter_upwards [hU.mem_nhds hxU, hmax] with y hy hmy
    calc
      φ t y * (F.connection t).scalarCurvature y ≤
          χ ((((F.metric t).edist p y).toReal - d₀) / δ) *
            (F.connection t).scalarCurvature y :=
        mul_le_mul_of_nonneg_right (hle t y hy) (hRnow y)
      _ ≤ χ ((((F.metric t).edist p x).toReal - d₀) / δ) *
          (F.connection t).scalarCurvature x := hmy
      _ = φ t x * (F.connection t).scalarCurvature x := by rw [heq]
  have hRtime := (hTheory.scalar_evolution (m + 1) M J F t (interior_subset ht) x).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  let v : ℝ → ℝ := fun s => φ s x * (F.connection s).scalarCurvature x
  have hv : DifferentiableAt ℝ v t := hφtime.mul hRtime.differentiableAt
  refine ⟨v, deriv v t, by simp only [v, heq], ?_, hv.hasDerivAt, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_le_mul_of_nonneg_right (hle s x hxU) (hRpast s hs)
  · have hb := F.deriv_cutoff_mul_scalarCurvature_le_linear_at_max_on_open
      hTheory ht x φ hU hxU hφ hφtime (by simpa only [heq] using hcutoffpos)
      (hRic x) hlocal hQ (by positivity) hheat
    simpa only [v, heq] using hb



theorem exists_lower_time_support_distance_cutoff_scalarCurvature_all_points
    (hTheory : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    {a t r Λ scale δ d₀ A B C Q : ℝ} (ht : t ∈ interior J) (hm : 0 < m)
    (hcomplete : MetricComplete (F.metric t))
    (hRic : ∀ y : M, ∀ w : TangentSpace (𝓡 (m + 1)) y,
      0 ≤ (F.connection t).ricci y w w)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (p x : M)
    (hx : x ∈ (F.metric t).ball p r)
    (hupper : ∀ y ∈ (F.metric t).ball p r, ∀ w : TangentSpace (𝓡 (m + 1)) y,
      (F.connection t).ricci y w w ≤ Λ * (F.metric t).inner y w w)
    (hRicpast : ∀ s ∈ Icc a t, ∀ w : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ (F.connection s).ricci x w w)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hanti : Antitone χ)
    (hχnonneg : ∀ z, 0 ≤ χ z) (hδ : 0 < δ)
    (hflat : ∀ z, z ≤ 1 → χ z = 1) (hd₀ : 0 ≤ d₀)
    (hA₀ : 0 ≤ A) (hB₀ : 0 ≤ B) (hC₀ : 0 ≤ C)
    (hA : ∀ z, deriv χ z ^ 2 ≤ A * χ z)
    (hB : ∀ z, -B ≤ deriv (deriv χ) z) (hC : ∀ z, -C ≤ deriv χ z)
    (hQ : (F.connection t).scalarCurvature x ≤ Q)
    (hpos : 0 < χ ((((F.metric t).edist p x).toReal - d₀) / δ) *
      (F.connection t).scalarCurvature x)
    (hmax : IsLocalMax (fun y =>
      χ ((((F.metric t).edist p y).toReal - d₀) / δ) *
        (F.connection t).scalarCurvature y) x) :
    ∃ (v : ℝ → ℝ) (d : ℝ),
      v t = χ ((((F.metric t).edist p x).toReal - d₀) / δ) *
        (F.connection t).scalarCurvature x ∧
      (∀ᶠ s in 𝓝[Icc a t] t,
        v s ≤ χ ((((F.metric s).edist p x).toReal - d₀) / δ) *
          (F.connection s).scalarCurvature x) ∧
      HasDerivAt v d t ∧
      d ≤ 2 * Q * (χ ((((F.metric t).edist p x).toReal - d₀) / δ) *
        (F.connection t).scalarCurvature x) +
        Q * (C * (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Λ / scale) / δ +
          (B + 2 * A + 2 * (m : ℝ) * C) / δ ^ 2) := by
  by_cases hpx : p = x
  · subst x
    have hself (s : ℝ) : ((F.metric s).edist p p).toReal = 0 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
        ⟨(F.metric s).toRiemannianMetric⟩
      change (Manifold.riemannianEDist (𝓡 (m + 1)) p p).toReal = 0
      simp only [Manifold.riemannianEDist_self, ENNReal.toReal_zero]
    have hcenter (s : ℝ) : χ ((((F.metric s).edist p p).toReal - d₀) / δ) = 1 := by
      apply hflat
      rw [hself]
      exact (div_le_one hδ).mpr (by linarith)
    have hnear : ∀ᶠ y in 𝓝 p, ((F.metric t).edist p y).toReal < δ :=
      ((F.metric t).continuous_toReal_edist p).continuousAt.eventually
        (eventually_lt_nhds (by simpa only [hself] using hδ))
    have hlocal : IsLocalMax (F.connection t).scalarCurvature p := by
      apply hmax.congr
      filter_upwards [hnear] with y hy
      rw [hflat _ ((div_le_one hδ).mpr (by linarith)), one_mul]
    have hRnonneg : 0 ≤ (F.connection t).scalarCurvature p :=
      Finset.sum_nonneg (fun _ _ => hRic p _)
    have hQnonneg : 0 ≤ Q := hRnonneg.trans hQ
    have hRtime := (hTheory.scalar_evolution (m + 1) M J F t (interior_subset ht) p).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)
    have hlap := (F.connection t).laplacian_nonpos_of_isLocalMax
      (hTheory.tensor_calculus (m + 1) M (F.metric t) (F.connection t)).contMDiff_scalarCurvature
      hlocal
    have hderiv := F.deriv_scalarCurvature_le_laplacian_add_sq_of_ricci_nonneg
      hTheory ht p (hRic p)
    have hreaction := mul_le_mul_of_nonneg_right hQ hRnonneg
    refine ⟨fun s => (F.connection s).scalarCurvature p,
      deriv (fun s => (F.connection s).scalarCurvature p) t,
      by rw [hcenter, one_mul], ?_, hRtime.differentiableAt.hasDerivAt, ?_⟩
    · filter_upwards [] with s
      rw [hcenter, one_mul]
    · rw [hcenter, one_mul]
      have hheat : 0 ≤ Q *
          (C * (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * Λ / scale) / δ +
            (B + 2 * A + 2 * (m : ℝ) * C) / δ ^ 2) := by positivity
      nlinarith only [hderiv, hlap, hreaction, hheat]
  · exact F.exists_lower_time_support_distance_cutoff_scalarCurvature
      hTheory ht hm hcomplete hRic hΛ hscale p x hx hpx hupper hRicpast
      hχ hanti hχnonneg hδ hflat hd₀ hA₀ hB₀ hC₀ hA hB hC hQ hpos hmax

end PoincareConjecture.RicciFlow

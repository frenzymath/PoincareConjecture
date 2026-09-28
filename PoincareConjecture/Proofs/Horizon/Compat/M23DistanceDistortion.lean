import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.DistanceDistortion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
  {J : Set ℝ}

theorem toReal_edist_le_add_of_ricci_upper_on_balls_intrinsic
    (F : RicciFlow (m + 1) M J) (hm : 0 < m)
    {a b Λ scale : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ (F.connection t).ricci x v v)
    (hΛ : 0 ≤ Λ) (hscale : 0 < scale) (p x : M)
    (hlocal : ∀ t ∈ Icc a b, ∃ r : ℝ, x ∈ (F.metric t).ball p r ∧
      ∀ y ∈ (F.metric t).ball p r, ∀ v : TangentSpace (𝓡 (m + 1)) y,
        (F.connection t).ricci y v v ≤ Λ * (F.metric t).inner y v v) :
    ((F.metric a).edist p x).toReal ≤ ((F.metric b).edist p x).toReal +
      (4 * (((m + 1 : ℕ) : ℝ)) * scale + 8 * Λ / scale) * (b - a) := by
  by_cases hpx : p = x
  · subst x
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self, ENNReal.toReal_zero, zero_add]
    positivity
  have hjoint := F.continuousOn_toReal_edist_of_ricci_nonneg_intrinsic hJ
    (hcomplete b ⟨hab, le_rfl⟩) hRic p
  have hcont : ContinuousOn (fun t => ((F.metric t).edist p x).toReal) (Icc a b) :=
    hjoint.comp (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, mem_univ x⟩)
  apply Poincare.AncientVolume.backward_image_le_add_of_upper_supports hab hcont
  intro t ht
  obtain ⟨r, hx, hupper⟩ := hlocal t (Ioc_subset_Icc_self ht)
  obtain ⟨U, rho, _hU, hxU, _hsmooth, heq, habove, _hgrad, _hlap, hd, hder⟩ :=
    F.exists_distance_spacetime_upper_support (hJ (Ioc_subset_Icc_self ht)) hm
      (hcomplete t (Ioc_subset_Icc_self ht)) (hRic t (Ioc_subset_Icc_self ht))
      hΛ hscale p x hx hpx hupper
  exact ⟨fun s => rho s x, heq, fun s => habove s x hxU, hd, hder⟩

end PoincareConjecture.RicciFlow

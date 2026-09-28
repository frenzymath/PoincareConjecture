import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Coordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M30

theorem exists_smooth_metricFamily_of_coefficients
    {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n)))
    {J : Set ℝ} (t₀ : ℝ) (ht₀ : t₀ ∈ J)
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (J ×ˢ (U : Set (EuclideanSpace ℝ (Fin n)))))
    (hsymm : ∀ t ∈ J, ∀ x ∈ U, ∀ v w, B (t, x) v w = B (t, x) w v)
    (hlower : ∀ t ∈ J, ∀ x ∈ U, ∃ c : ℝ, 0 < c ∧
      ∀ v, c * ‖v‖ ^ 2 ≤ B (t, x) v v) :
    ∃ g : ℝ → RiemannianMetric n U, RiemannianMetric.IsSmoothFamilyOn g J ∧
      ∀ t ∈ J, ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
        (g t).inner x v w = B (t, x) v w := by
  classical
  have hex (t : J) : ∃ g : RiemannianMetric n U,
      ∀ (x : U) (v w : TangentSpace (𝓡 n) x), g.inner x v w = B (t, x) v w := by
    apply RiemannianMetric.exists_of_coordinate_limit U
      (fun _ x => B (t, x)) (fun x => B (t, x))
      (hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x hx => ⟨t.property, hx⟩))
    · exact fun _ x hx => hsymm t t.property x hx
    · exact fun _ _ _ _ => tendsto_const_nhds
    · intro x hx
      obtain ⟨c, hc, hbound⟩ := hlower t t.property x hx
      exact ⟨c, hc, Eventually.of_forall fun _ => hbound⟩
  choose gSlice hSlice using hex
  let g : ℝ → RiemannianMetric n U := fun t =>
    if ht : t ∈ J then gSlice ⟨t, ht⟩ else gSlice ⟨t₀, ht₀⟩
  have hcoeff (t : ℝ) (ht : t ∈ J) (x : U) (v w : TangentSpace (𝓡 n) x) :
      (g t).inner x v w = B (t, x) v w := by
    simpa only [g, dif_pos ht] using hSlice ⟨t, ht⟩ x v w
  refine ⟨g, ?_, hcoeff⟩
  apply RiemannianMetric.isSmoothFamilyOn_of_constant_chart
    (fun x y => by simp [Opens.chartAt_eq]) g (fun p => B (p.1, p.2)) ?_ hcoeff
  have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) ∞
      (fun p : ℝ × U => (p.1, (p.2 : EuclideanSpace ℝ (Fin n)))) :=
    contMDiff_fst.prodMk_space (contMDiff_subtype_val.comp contMDiff_snd)
  exact hB.contMDiffOn.comp hmap.contMDiffOn (fun p hp => ⟨hp.1, p.2.property⟩)

end PoincareConjecture.M30

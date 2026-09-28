import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.SpatialEvolution
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinMetricCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.M28

theorem norm_pullbackCoefficients_le_of_quadratic_upper
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (e : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n)) {b : ℝ} (hb : 0 ≤ b)
    (hupper : ∀ v, g.pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) :
    ‖g.pullbackCoefficients e x‖ ≤ b := by
  apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
  · intro u v
    exact g.symm _ _ _
  · intro v
    have hnonneg : 0 ≤ g.pullbackCoefficients e x v v := by
      let w := mfderiv (𝓡 n) (𝓡 n) e x v
      change 0 ≤ g.inner (e x) w w
      by_cases hw : w = 0
      · simp [hw]
      · exact (g.pos _ _ hw).le
    rw [abs_of_nonneg hnonneg]
    exact hupper v

theorem differentiableAt_spatialJet_of_mem_interior
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {t : ℝ} (ht : t ∈ interior J) (m : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    DifferentiableAt ℝ
      (fun s => iteratedFDeriv ℝ m ((F.metric s).pullbackCoefficients e) x) t := by
  have hB := F.smooth.contDiffOn_spacetime_pullbackCoefficients_within hU he
  have hjet := SpacetimeBounds.contDiffOn_spatialJet
    (hB.mono (show interior J ×ˢ U ⊆ J ×ˢ U from
      fun _ hz => ⟨interior_subset hz.1, hz.2⟩)) isOpen_interior hU m
  exact ((hjet.contDiffAt ((isOpen_interior.prod hU).mem_nhds ⟨ht, hx⟩)).comp t
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

set_option synthInstance.maxHeartbeats 100000 in

theorem exists_affine_spatialJet_evolution_bound_interior
    (n q : ℕ) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {M : Type*} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        {J : Set ℝ} (F : RicciFlow n M J),
        ∀ {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
        (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
        ∀ {t : ℝ}, t ∈ interior J → ∀ {x : EuclideanSpace ℝ (Fin n)}, x ∈ U →
        (∀ v, a * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients e x v v) →
        (∀ v, (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ s ≤ q + 1, (F.connection t).curvatureDerivativeNorm s (e x) ≤ K s) →
        (∀ j, 1 ≤ j → j ≤ q →
          ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ A ^ j) →
        ‖deriv (fun s => iteratedFDeriv ℝ (q + 1)
          ((F.metric s).pullbackCoefficients e) x) t‖ ≤
          C * (1 + ‖iteratedFDeriv ℝ (q + 1)
            ((F.metric t).pullbackCoefficients e) x‖) := by
  obtain ⟨C, hC, hbound⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
    n q K hK ha hb A hA
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ J F U hU e he hi t ht x hx hlower hupper hcurv hjets
  obtain ⟨l, r, htlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (mem_interior_iff_mem_nhds.mp ht)
  obtain ⟨s, hls, hst⟩ := exists_between htlr.1
  have hnontriv : (Ioo l r).Nontrivial :=
    ⟨s, ⟨hls, hst.trans htlr.2⟩, t, htlr, ne_of_lt hst⟩
  let F' := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F hsub
    ordConnected_Ioo hnontriv
  exact hbound F' isOpen_Ioo hU he hi htlr hx hlower hupper hcurv hjets

end PoincareConjecture.M28

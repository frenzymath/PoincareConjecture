import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.JetSlices
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.ChartFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Pointed
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.FlowEquation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.OpenDomain
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CanonicalDomain

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000

open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RiemannianMetric

private theorem pullbackCoefficients_openChart
    {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n)))
    (g : RiemannianMetric n U) (p x : U) :
    g.pullbackCoefficients (extChartAt (𝓡 n) p).symm (x : EuclideanSpace ℝ (Fin n)) =
      g.inner x := by
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x)
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hd
  have hc : extChartAt (𝓡 n) p = extChartAt (𝓡 n) x := by
    simp [extChartAt, Opens.chartAt_eq]
  rw [hc]
  ext v w
  change g.inner ((extChartAt (𝓡 n) x).symm x)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm x v)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm x w) = g.inner x v w
  have hx : (extChartAt (𝓡 n) x).symm (x : EuclideanSpace ℝ (Fin n)) = x :=
    (extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)
  change mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm
    (x : EuclideanSpace ℝ (Fin n)) = ContinuousLinearMap.id ℝ _ at hd
  rw [hd, hx]
  rfl

private theorem iteratedFDeriv_openChart_eq
    {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n)))
    (g : RiemannianMetric n U)
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hcoeff : ∀ (x : U) v w, g.inner x v w = B x v w)
    (x : U) (v w : EuclideanSpace ℝ (Fin n)) (r : ℕ) :
    iteratedFDeriv ℝ r
      (fun y => g.pullbackCoefficients (extChartAt (𝓡 n) x).symm y v w)
      (extChartAt (𝓡 n) x x) = iteratedFDeriv ℝ r (fun y => B y v w) x := by
  have heq : (fun y => g.pullbackCoefficients (extChartAt (𝓡 n) x).symm y v w)
      =ᶠ[𝓝 (x : EuclideanSpace ℝ (Fin n))] (fun y => B y v w) := by
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    rw [pullbackCoefficients_openChart U g x ⟨y, hy⟩]
    exact hcoeff ⟨y, hy⟩ v w
  exact (heq.iteratedFDeriv ℝ r).eq_of_nhds

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RicciFlow

private theorem scalar_slices_of_bilinear_jets
    {n : ℕ} {x₀ : EuclideanSpace ℝ (Fin n)} {ρ : ℝ} (hρ : 0 < ρ)
    (Bseq : ℕ → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hseq : ∀ k, ContDiffOn ℝ ∞ (Bseq k) (Iic 0 ×ˢ closedBall x₀ ρ))
    (hB : ContDiffOn ℝ ∞ B (Iic 0 ×ˢ closedBall x₀ ρ))
    {t : ℝ} (ht : t ≤ 0) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball x₀ ρ)
    (hjet : ∀ r, Tendsto (fun k => iteratedFDerivWithin ℝ r (Bseq k)
      (Iic 0 ×ˢ closedBall x₀ ρ) (t, x)) atTop
      (𝓝 (iteratedFDerivWithin ℝ r B (Iic 0 ×ˢ closedBall x₀ ρ) (t, x))))
    (v w : EuclideanSpace ℝ (Fin n)) :
    (∀ r, Tendsto (fun k => iteratedFDeriv ℝ r (fun y => Bseq k (t, y) v w) x) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun y => B (t, y) v w) x))) ∧
    Tendsto (fun k => derivWithin (fun s => Bseq k (s, x) v w) (Iic 0) t) atTop
      (𝓝 (derivWithin (fun s => B (s, x) v w) (Iic 0) t)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ w).comp
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v)
  have huBall : UniqueDiffOn ℝ (closedBall x₀ ρ) := by
    apply uniqueDiffOn_convex (convex_closedBall x₀ ρ)
    rw [interior_closedBall x₀ hρ.ne']
    exact ⟨x₀, by simpa using hρ⟩
  have hu := (uniqueDiffOn_Iic 0).prod huBall
  have hp : (t, x) ∈ Iic 0 ×ˢ closedBall x₀ ρ := ⟨ht, ball_subset_closedBall hx⟩
  have hs (C : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
      (hC : ContDiffOn ℝ ∞ C (Iic 0 ×ˢ closedBall x₀ ρ)) :
      ContDiffOn ℝ ∞ (fun z => C z v w) (Iic 0 ×ˢ closedBall x₀ ρ) :=
    (hC.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have heq (C : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
      (hC : ContDiffOn ℝ ∞ C (Iic 0 ×ˢ closedBall x₀ ρ)) (r : ℕ) :
      iteratedFDerivWithin ℝ r (fun z => C z v w) (Iic 0 ×ˢ closedBall x₀ ρ) (t, x) =
        L.compContinuousMultilinearMap
          (iteratedFDerivWithin ℝ r C (Iic 0 ×ˢ closedBall x₀ ρ) (t, x)) := by
    exact L.iteratedFDerivWithin_comp_left (hC (t, x) hp) hu hp
      (WithTop.coe_le_coe.mpr (le_top : (r : ℕ∞) ≤ ⊤))
  have hj (r : ℕ) : Tendsto (fun k => iteratedFDerivWithin ℝ r
      (fun z => Bseq k z v w) (Iic 0 ×ˢ closedBall x₀ ρ) (t, x)) atTop
      (𝓝 (iteratedFDerivWithin ℝ r (fun z => B z v w)
        (Iic 0 ×ˢ closedBall x₀ ρ) (t, x))) := by
    rw [heq B hB r]
    have hpost := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin r => ℝ × E) (E →L[ℝ] E →L[ℝ] ℝ) ℝ L).continuous.tendsto _).comp
        (hjet r)
    exact hpost.congr (fun k => (heq (Bseq k) (hseq k) r).symm)
  exact ⟨fun r => PoincareConjecture.AncientCompactness.tendsto_spatial_slice_jet_of_centered_halfCylinder
    hρ _ _ (fun k => hs _ (hseq k)) (hs _ hB) ht hx r (hj r),
    PoincareConjecture.AncientCompactness.tendsto_derivWithin_time_slice_of_centered_halfCylinder hρ _ _
      (fun k => hs _ (hseq k)) (hs _ hB) ht (ball_subset_closedBall hx) (hj 1)⟩

theorem exists_of_ancient_centered_halfCylinder_coefficients
    {n : ℕ} {x₀ : EuclideanSpace ℝ (Fin n)} {ρ : ℝ} (hρ : 0 < ρ)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ ball x₀ ρ)
    (Fseq : ℕ → RicciFlow n U (Iic 0))
    (Bseq : ℕ → ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hseq : ∀ k, ContDiffOn ℝ ∞ (Bseq k) (Iic 0 ×ˢ closedBall x₀ ρ))
    (hB : ContDiffOn ℝ ∞ B (Iic 0 ×ˢ closedBall x₀ ρ))
    (hcoeff : ∀ k t, t ≤ 0 → ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      ((Fseq k).metric t).inner x v w = Bseq k (t, x) v w)
    (hsymm : ∀ t ≤ 0, ∀ x ∈ U, ∀ v w, B (t, x) v w = B (t, x) w v)
    (hlower : ∀ t ≤ 0, ∀ x ∈ U, ∃ c : ℝ, 0 < c ∧
      ∀ v, c * ‖v‖ ^ 2 ≤ B (t, x) v v)
    (hjet : ∀ r K, IsCompact K → K ⊆ Iic 0 ×ˢ closedBall x₀ ρ →
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ r (Bseq k) (Iic 0 ×ˢ closedBall x₀ ρ))
        (iteratedFDerivWithin ℝ r B (Iic 0 ×ˢ closedBall x₀ ρ)) atTop K) :
    ∃ F : RicciFlow n U (Iic 0), ∀ t ≤ 0, ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      (F.metric t).inner x v w = B (t, x) v w := by
  obtain ⟨g, hg, hgcoeff⟩ := RiemannianMetric.exists_smoothFamily_of_ancient_coefficients
    U B (hB.mono (prod_mono subset_rfl (hU.trans ball_subset_closedBall))) hsymm hlower
  let D : ∀ t, LeviCivitaData (g t) := fun t => (g t).openEuclideanLeviCivitaData U
  have hj (t : ℝ) (ht : t ≤ 0) (x : U) (v w : EuclideanSpace ℝ (Fin n)) := by
    apply scalar_slices_of_bilinear_jets hρ Bseq B hseq hB ht (hU x.property) ?_ v w
    intro r
    exact (hjet r {(t, (x : EuclideanSpace ℝ (Fin n)))} isCompact_singleton
      (singleton_subset_iff.mpr ⟨ht, ball_subset_closedBall (hU x.property)⟩)).tendsto_at
        (mem_singleton _)
  have heq := equation_of_coordinate_jets_within Fseq g D (uniqueDiffOn_Iic 0) hg
  have hequation : ∀ t ∈ Iic (0 : ℝ), ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * (D t).ricci x v w) (Iic 0) t := by
    apply heq
    · intro t ht x r _ a c
      simpa only [RiemannianMetric.iteratedFDeriv_openChart_eq U (g t)
          (fun y => B (t, y)) (hgcoeff t ht),
        RiemannianMetric.iteratedFDeriv_openChart_eq U ((Fseq _).metric t)
          (fun y => Bseq _ (t, y)) (hcoeff _ t ht)] using
        (hj t ht x (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ c)).1 r
    · intro t ht x v w
      have hlim : derivWithin (fun s => (g s).inner x v w) (Iic 0) t =
          derivWithin (fun s => B (s, x) v w) (Iic 0) t :=
        derivWithin_congr (fun s hs => hgcoeff s hs x v w) (hgcoeff t ht x v w)
      have hsrc (k : ℕ) : derivWithin (fun s => ((Fseq k).metric s).inner x v w) (Iic 0) t =
          derivWithin (fun s => Bseq k (s, x) v w) (Iic 0) t :=
        derivWithin_congr (fun s hs => hcoeff k s hs x v w) (hcoeff k t ht x v w)
      simpa only [hlim, hsrc] using (hj t ht x v w).2
  exact ⟨{
    metric := g
    connection := D
    interval := (Fseq 0).interval
    nontrivial := (Fseq 0).nontrivial
    smooth := hg
    equation := hequation }, hgcoeff⟩

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

theorem exists_ancient_limit_of_eventual_partial_chart_coefficients
    {n : ℕ} (C : ℕ → FlowCarrier.{u} n)
    {x₀ : EuclideanSpace ℝ (Fin n)} {ρ : ℝ} (hρ : 0 < ρ)
    (Fseq : ∀ k, RicciFlow n (C k).carrier (Iic 0))
    (Φ : ∀ k, PartialDiffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (C k).carrier ∞)
    (hsource : ∀ᶠ k : ℕ in atTop, closedBall x₀ ρ ⊆ (Φ k).source)
    (U : Opens (EuclideanSpace ℝ (Fin n)))
    (hU : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆ ball x₀ ρ)
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Iic 0 ×ˢ closedBall x₀ ρ))
    (hsymm : ∀ t ≤ 0, ∀ x ∈ U, ∀ v w, B (t, x) v w = B (t, x) w v)
    (hlower : ∀ t ≤ 0, ∀ x ∈ U, ∃ c : ℝ, 0 < c ∧
      ∀ v, c * ‖v‖ ^ 2 ≤ B (t, x) v v)
    (hjet : ∀ r K, IsCompact K → K ⊆ Iic 0 ×ˢ closedBall x₀ ρ →
      TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ r
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((Fseq k).metric z.1).pullbackCoefficients (Φ k) z.2)
          (Iic 0 ×ˢ closedBall x₀ ρ))
        (iteratedFDerivWithin ℝ r B (Iic 0 ×ˢ closedBall x₀ ρ)) atTop K) :
    ∃ F : RicciFlow n U (Iic 0), ∀ t ≤ 0, ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      (F.metric t).inner x v w = B (t, x) v w := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsource
  have hUΦ (k : ℕ) : (U : Set (EuclideanSpace ℝ (Fin n))) ⊆
      (Φ (max k N)).source :=
    (hU.trans ball_subset_closedBall).trans (hN _ (le_max_right k N))
  let Fchart (k : ℕ) :=
    (Fseq (max k N)).pullbackToPartialChart (Φ (max k N)) U (hUΦ k)
  apply exists_of_ancient_centered_halfCylinder_coefficients hρ U hU Fchart
    (fun k z => ((Fseq (max k N)).metric z.1).pullbackCoefficients
      (Φ (max k N)) z.2) B ?_ hB ?_ hsymm hlower ?_
  · intro k
    exact ((Fseq (max k N)).contDiffOn_pullbackCoefficients_within
      (Φ (max k N)).open_source (Φ (max k N)).contMDiffOn_toFun).mono
        (prod_mono subset_rfl (hN _ (le_max_right k N)))
  · intro k t _ x v w
    exact pullbackToPartialChart_inner (Fseq (max k N)) (Φ (max k N)) U (hUΦ k) t x v w
  · intro r K hK hKΩ
    apply (hjet r K hK hKΩ).congr
    filter_upwards [eventually_ge_atTop N] with k hk z _
    rw [max_eq_left hk]

end PoincareConjecture.RicciFlow

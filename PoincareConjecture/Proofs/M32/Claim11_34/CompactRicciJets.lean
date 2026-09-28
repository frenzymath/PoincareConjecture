import PoincareConjecture.Proofs.M32.Mathlib.CompactUniformComposition
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter
















set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v w

namespace PoincareConjecture.M32

open SpacetimeBounds SpacetimeBounds.Bootstrap

local notation "E" n:max => EuclideanSpace ℝ (Fin n)




theorem tendstoUniformlyOn_bilinear_metricJet_of_scalar_entries
    {n r : ℕ} {I : Type*} {l : Filter I} {K : Set (E n)}
    {B : I → E n → MetricCoefficient n} {C : E n → MetricCoefficient n}
    (hB : ∀ᶠ i in l, ∀ x ∈ K, ContDiffAt ℝ ∞ (B i) x)
    (hC : ∀ x ∈ K, ContDiffAt ℝ ∞ C x)
    (hentry : ∀ a b : Fin n, TendstoUniformlyOn
      (fun i x => iteratedFDeriv ℝ r (fun y => B i y
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) x)
      (fun x => iteratedFDeriv ℝ r (fun y => C y
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) x) l K) :
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ r (B i)) (iteratedFDeriv ℝ r C) l K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon hepsilon
  let delta := epsilon / ((n : ℝ) * n + 1)
  have hdelta : 0 < delta := div_pos hepsilon (by positivity)
  have hall : ∀ᶠ i in l, ∀ a b : Fin n, ∀ x ∈ K,
      dist (iteratedFDeriv ℝ r (fun y => C y
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) x)
        (iteratedFDeriv ℝ r (fun y => B i y
          (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) x)
          < delta :=
    eventually_all.mpr fun a => eventually_all.mpr fun b =>
      Metric.tendstoUniformlyOn_iff.mp (hentry a b) delta hdelta
  filter_upwards [hB, hall] with i hi hentries x hx
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  rw [dist_eq_norm, ← iteratedFDeriv_sub_apply ((hC x hx).of_le hr) ((hi x hx).of_le hr)]
  apply lt_of_le_of_lt (norm_iteratedFDeriv_bilinear_le_of_components
    (EuclideanSpace.basisFun (Fin n) ℝ) ((hC x hx).sub (hi x hx)) r (C := delta) ?_) ?_
  · intro a b
    have hCa : ContDiffAt ℝ ∞ (fun y => C y
        (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)) x :=
      ((hC x hx).clm_apply contDiffAt_const).clm_apply contDiffAt_const
    have hBa : ContDiffAt ℝ ∞ (fun y => B i y
        (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)) x :=
      ((hi x hx).clm_apply contDiffAt_const).clm_apply contDiffAt_const
    change ‖iteratedFDeriv ℝ r ((fun y => C y
      (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) -
        (fun y => B i y (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b))) x‖ ≤ delta
    rw [iteratedFDeriv_sub_apply (hCa.of_le hr) (hBa.of_le hr)]
    simpa only [dist_eq_norm] using (hentries a b x hx).le
  · have hden : ((n : ℝ) * n + 1) * delta = epsilon := by
      dsimp only [delta]
      exact mul_div_cancel₀ epsilon (ne_of_gt (by positivity : 0 < (n : ℝ) * n + 1))
    nlinarith




theorem tendstoUniformlyOn_metricTwoJet_of_bilinear_jets
    {n : ℕ} {I : Type*} {l : Filter I} {K : Set (E n)}
    {B : I → E n → MetricCoefficient n} {C : E n → MetricCoefficient n}
    (hjets : ∀ r : ℕ, r ≤ 2 → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ r (B i)) (iteratedFDeriv ℝ r C) l K) :
    TendstoUniformlyOn (fun i => metricTwoJet (B i)) (metricTwoJet C) l K := by
  have hfinite : TendstoUniformlyOn
      (fun i x => spatialJet 2 (fun p : ℝ × E n => B i p.2) (0, x))
      (fun x => spatialJet 2 (fun p : ℝ × E n => C p.2) (0, x)) l K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro epsilon hepsilon
    have hall := eventually_all.mpr fun r : Fin 3 =>
      Metric.tendstoUniformlyOn_iff.mp (hjets r (by omega)) epsilon hepsilon
    filter_upwards [hall] with i hi x hx
    exact (dist_pi_lt_iff hepsilon).mpr fun r => hi r x hx
  have h := (twoJetProjection n).uniformContinuous.comp_tendstoUniformlyOn hfinite
  simpa only [Function.comp_def, twoJetProjection_spatialJet] using h

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem tendstoUniformlyOn_ricci_of_scalar_pullback_jets
    {n : ℕ} {I : Type w} {l : Filter I}
    {M : I → Type u} {X : Type v}
    [∀ i, TopologicalSpace (M i)] [TopologicalSpace X]
    [∀ i, ChartedSpace (E n) (M i)] [ChartedSpace (E n) X]
    [∀ i, IsManifold (𝓡 n) ∞ (M i)] [IsManifold (𝓡 n) ∞ X]
    (gk : ∀ i, RiemannianMetric n (M i)) (Dk : ∀ i, LeviCivitaData (gk i))
    (phi : ∀ i, E n → M i) (g : RiemannianMetric n X) (D : LeviCivitaData g)
    (psi : E n → X) {K U : Set (E n)} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hpsi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ psi U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) psi y).IsInvertible)
    (hphi : ∀ᶠ i in l, ∃ V : Set (E n), IsOpen V ∧ K ⊆ V ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ (phi i) V ∧
      ∀ y ∈ V, (mfderiv (𝓡 n) (𝓡 n) (phi i) y).IsInvertible)
    (hjets : ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin n, TendstoUniformlyOn
      (fun i x => iteratedFDeriv ℝ r (fun y => (gk i).pullbackCoefficients (phi i) y
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) x)
      (fun x => iteratedFDeriv ℝ r (fun y => g.pullbackCoefficients psi y
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) x) l K)
    (u v : E n) :
    TendstoUniformlyOn
      (fun i x => (Dk i).ricci (phi i x)
        (mfderiv (𝓡 n) (𝓡 n) (phi i) x u) (mfderiv (𝓡 n) (𝓡 n) (phi i) x v))
      (fun x => D.ricci (psi x)
        (mfderiv (𝓡 n) (𝓡 n) psi x u) (mfderiv (𝓡 n) (𝓡 n) psi x v)) l K := by
  let B := fun i => (gk i).pullbackCoefficients (phi i)
  let C := g.pullbackCoefficients psi
  have hB : ∀ᶠ i in l, ∀ x ∈ K, ContDiffAt ℝ ∞ (B i) x := by
    filter_upwards [hphi] with i hi x hx
    obtain ⟨V, hV, hKV, hs, _⟩ := hi
    exact (gk i).contDiffAt_pullbackCoefficients (hs.contMDiffAt (hV.mem_nhds (hKV hx)))
  have hC (x : E n) (hx : x ∈ K) : ContDiffAt ℝ ∞ C x :=
    g.contDiffAt_pullbackCoefficients (hpsi.contMDiffAt (hU.mem_nhds (hKU hx)))
  have htwo : TendstoUniformlyOn (fun i => metricTwoJet (B i)) (metricTwoJet C) l K :=
    tendstoUniformlyOn_metricTwoJet_of_bilinear_jets fun r hr =>
      tendstoUniformlyOn_bilinear_metricJet_of_scalar_entries hB hC (hjets r hr)
  have hcont : ContinuousOn (metricTwoJet C) K := by
    intro x hx
    have hfirst := (hC x hx).fderiv_right (m := ∞) (by simp)
    have hsecond := hfirst.fderiv_right (m := ∞) (by simp)
    exact ((hC x hx).continuousAt.prodMk
      (hfirst.continuousAt.prodMk hsecond.continuousAt)).continuousWithinAt
  have hricci : TendstoUniformlyOn
      (fun i x => jetRicci (metricTwoJet (B i) x) u v)
      (fun x => jetRicci (metricTwoJet C x) u v) l K := by
    apply tendstoUniformlyOn_comp_of_isCompact_image
      (g := fun J => jetRicci J u v) (hK.image_of_continuousOn hcont) ?_ htwo
    rintro J ⟨x, hx, rfl⟩
    exact (contDiffAt_jetRicci
      (g.isInvertible_pullbackCoefficients (hinv x (hKU hx)).injective) u v).continuousAt
  have hlim := hricci.congr_right (g := fun x => D.ricci (psi x)
      (mfderiv (𝓡 n) (𝓡 n) psi x u) (mfderiv (𝓡 n) (𝓡 n) psi x v))
    (fun x hx => jetRicci_metricTwoJet_pullback D hU hpsi hinv (hKU hx) u v)
  apply hlim.congr
  filter_upwards [hphi] with i hi x hx
  obtain ⟨V, hV, hKV, hs, hi⟩ := hi
  exact jetRicci_metricTwoJet_pullback (Dk i) hV hs hi (hKV hx) u v

end PoincareConjecture.M32

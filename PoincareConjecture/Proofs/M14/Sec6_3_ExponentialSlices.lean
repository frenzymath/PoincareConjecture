import PoincareConjecture.Proofs.M14.Sec6_3_ActionSmooth

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem exponentialFamily_domain_slice_isOpen (E : M14ExponentialFamily G T x) (s : ℝ) :
    IsOpen {Z | (Z, s) ∈ E.domain} := by
  rw [isOpen_iff_mem_nhds]
  intro Z hZ
  obtain ⟨U, hU, hZU, hsub⟩ := E.domain_relative_open (Z, s) hZ
  have hcont : Continuous (fun W : G.Horizontal x => (W, s)) :=
    continuous_id.prodMk continuous_const
  apply mem_of_superset ((hU.preimage hcont).mem_nhds hZU)
  intro W hW
  exact hsub ⟨hW, (E.domain_admissible hZ).1, (E.domain_admissible hZ).2⟩

theorem exponentialFamily_gamma_slice_contMDiffAt (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hs : (Z, s) ∈ E.domain) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    ContMDiffAt (𝓘(ℝ, G.Horizontal x)) (spacetimeModel n) ∞ (fun W => E.gamma W s) Z := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have h : ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (spacetimeModel n) ∞
      (fun W => E.gamma W s) {W | (W, s) ∈ E.domain} :=
    E.family_smooth.comp (contMDiff_id.prodMk (contMDiff_const (c := s))).contMDiffOn
      (fun _ hW => hW)
  exact (h Z hs).contMDiffAt ((exponentialFamily_domain_slice_isOpen E s).mem_nhds hs)

theorem exponentialFamily_smooth_prefix
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    ∃ U : Set (G.Horizontal x), IsOpen U ∧ Z ∈ U ∧ U ×ˢ Icc 0 s ⊆ E.domain ∧
      M14HorizontalFamilySmooth G E.gamma (U ×ˢ Icc 0 s) := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have hsurv : (Z, s) ∈ initialValueDomain G T x := exponentialFamily_domain_eq E ▸ hs
  obtain ⟨U, hU, hZU, htube, _⟩ :=
    initialValueCurve_smooth_prefix hM04 hM12 E.base_time hpos hsurv
  rw [← exponentialFamily_domain_eq E] at htube
  exact ⟨U, hU, hZU, htube, E.family_smooth.mono htube⟩

theorem exponentialFamily_action_slice_contMDiffAt
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    ContMDiffAt (𝓘(ℝ, G.Horizontal x)) (𝓘(ℝ, ℝ)) ∞ (fun W => E.action W s) Z := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have h : ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (𝓘(ℝ, ℝ)) ∞
      (fun W => E.action W s) {W | (W, s) ∈ E.domain} :=
    (exponentialFamily_action_smooth hM04 hM12 E).comp
      (contMDiff_id.prodMk (contMDiff_const (c := s))).contMDiffOn (fun _ hW => ⟨hW, hpos⟩)
  exact (h Z hs).contMDiffAt ((exponentialFamily_domain_slice_isOpen E s).mem_nhds hs)

end PoincareConjecture.M14

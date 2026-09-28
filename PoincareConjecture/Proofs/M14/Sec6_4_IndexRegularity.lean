import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoordinates
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCover
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiPair
import PoincareConjecture.Proofs.M14.Sec6_2_ClosedFieldExtension











set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}




theorem gaugeHorizontalCovariantDerivative_contMDiffOn (b : G.gaugeCover.index)
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (T : ℝ) (x₀ : G.gaugeCover.spatial b) {J : Set ℝ} (hJ : UniqueDiffOn ℝ J)
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b} {γ : ℝ → G.Point}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β J)
    (hrec : ∀ s ∈ J, (G.gaugeCover.cylinder b).toSpacetime (β s) = γ s)
    (hclock : ∀ s ∈ J, (β s).1.val = T - s ^ 2)
    {Y : ∀ s, G.Horizontal (γ s)} (E : M14PullbackExtension G γ J Y) :
    ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ s)
        (M14HorizontalCovariantDerivative G γ J Y E s)) J := by
  have hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ γ J :=
    ((G.gaugeCover.cylinder b).smooth.comp_contMDiffOn hβ).congr
      (fun s hs => (hrec s hs).symm)
  obtain ⟨f, hf, hY⟩ := exists_smooth_horizontalGauge_coordinates b hβ hrec Y
    (pullbackExtension_field_contMDiffOn E hγ)
  let q := fun s => (β s).2.val
  have hq : ContDiffOn ℝ ∞ q J := gaugeLift_spatialCurve_contDiffOn b hβ
  have htime (s : ℝ) (hs : s ∈ J) : T - s ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock s hs]
    exact (β s).1.property
  have hmap : MapsTo (fun s => (s, q s)) J (J ×ˢ (extChartAt (𝓡 n) x₀).target) := by
    intro s hs
    refine ⟨hs, ?_⟩
    have hsrc : (β s).2 ∈ (extChartAt (𝓡 n) x₀).source := by
      rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
      exact mem_univ _
    have he : extChartAt (𝓡 n) x₀ (β s).2 = (β s).2.val := by
      rw [extChartAt_coe]
      rfl
    simpa only [he] using (extChartAt (𝓡 n) x₀).map_source hsrc
  let d := fun s => derivWithin f J s +
    M08.closedChartConnection W.flow T x₀ J (s, q s) (derivWithin q J s) (f s)
  have hd : ContDiffOn ℝ ∞ d J :=
    (hf.derivWithin hJ (m := ∞) (by simp)).add
      ((((M08.closedChartConnection_contDiffOn W.flow T x₀ hJ htime).comp
        (contDiffOn_id.prodMk hq) hmap).clm_apply
          (hq.derivWithin hJ (m := ∞) (by simp))).clm_apply hf)
  apply (horizontalFieldOfGauge_contMDiffOn b hβ hrec hd).congr
  intro s hs
  exact Bundle.TotalSpace.ext rfl
    ((horizontalCovariantDerivative_lifted_gauge b hCoordinates W T x₀
      hβ hrec hclock E f hY hs (hJ s hs)).trans
        (horizontalFieldOfGauge_heq b hrec d hs).symm)

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)




theorem horizontalCovariantDerivative_contMDiffOn
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    {Y : ∀ s, G.Horizontal (R.curve s)}
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y) :
    ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s)
        (M14HorizontalCovariantDerivative G R.curve
          (M14SqrtParameterInterval τ₁ τ₂) Y E s)) (M14SqrtParameterInterval τ₁ τ₂) := by
  intro s hs
  obtain ⟨b, N, β, hN, hsN, hβ, hrec, hclock⟩ := exists_squareRoot_gauge_neighborhood R hs
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  obtain ⟨l, r, hal, hlr, hrb, hls, hsr, hsubN, hnear⟩ :=
    M08.exists_enlarged_closed_interval hab hs.1 le_rfl hs.2 hN
      (by simpa only [Icc_self, singleton_subset_iff] using hsN)
  have hsub : Icc l r ⊆ M14SqrtParameterInterval τ₁ τ₂ := Icc_subset_Icc hal hrb
  have hsub' : Icc l r ⊆ M14SqrtParameterInterval τ₁ τ₂ ∩ N :=
    fun _ hv => ⟨hsub hv, hsubN hv⟩
  obtain ⟨W⟩ := ordinaryGaugeWitness_nonempty b hCoordinates
  have hlocal := gaugeHorizontalCovariantDerivative_contMDiffOn b hCoordinates W T (β s).2
    (uniqueDiffOn_Icc hlr) (hβ.mono hsub') (fun v hv => hrec v (hsub' hv))
    (fun v hv => hclock v (hsub' hv)) (pullbackExtensionRestrict E hsub)
  have hglobal : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve v)
        (M14HorizontalCovariantDerivative G R.curve
          (M14SqrtParameterInterval τ₁ τ₂) Y E v)) (Icc l r) := by
    apply hlocal.congr
    intro v hv
    congr 1
    exact horizontalCovariantDerivative_restrict_subset E hsub (uniqueDiffOn_Icc hlr v hv)
      ((R.smooth.mono R.interval_subset v (hsub hv)).mdifferentiableWithinAt (by simp))
  exact (hglobal s ⟨hls, hsr⟩).mono_of_mem_nhdsWithin (hnear s ⟨le_rfl, le_rfl⟩)




theorem exists_horizontalCovariantDerivative_extension
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    {Y : ∀ s, G.Horizontal (R.curve s)}
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y) :
    Nonempty (M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂)
      (fun s => M14HorizontalCovariantDerivative G R.curve
        (M14SqrtParameterInterval τ₁ τ₂) Y E s)) :=
  exists_pullbackExtension_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
    (horizontalCovariantDerivative_contMDiffOn R hCoordinates E)

end PoincareConjecture.M14

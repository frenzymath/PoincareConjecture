import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Pullback
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Pullback









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

open Set Filter Poincare.Gluing Manifold IsManifold
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {Q : Type*} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q] [IsManifold (𝓡 n) ∞ Q]

omit [IsManifold (𝓡 n) ∞ Q] in
private theorem restricted_chart
    (e : OpenPartialHomeomorph Q (EuclideanSpace ℝ (Fin n)))
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (V : TopologicalSpace.Opens Q) (p : V)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hp : (p : Q) ∈ e.source) (hpΩ : e p ∈ Ω) :
    ∃ c : OpenPartialHomeomorph V (EuclideanSpace ℝ (Fin n)),
      p ∈ c.source ∧ c.target ⊆ e.target ∩ Ω ∧
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target ∧
      EqOn (Subtype.val ∘ c.symm) e.symm c.target := by
  let d := (e.symm.restrOpen Ω hΩ).symm
  let c := d.subtypeRestr ⟨p⟩
  have hct : c.target ⊆ e.target ∩ Ω := d.subtypeRestr_target_subset ⟨p⟩
  have hce : EqOn (Subtype.val ∘ c.symm) e.symm c.target := by
    intro x hx
    exact d.subtypeRestr_symm_apply ⟨p⟩ hx
  have hcs : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c c.source := by
    intro x hx
    have hx' : (x : Q) ∈ e.source := hx.2.1
    exact ((he.contMDiffAt (e.open_source.mem_nhds hx')).comp x
      (contMDiff_subtype_val.contMDiffAt)).contMDiffWithinAt
  have hci : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff V c.symm c.target x).mp
    exact ((hei.mono (fun x hx => (hct hx).1)).congr hce) x hx
  let dc : PartialDiffeomorph (𝓡 n) (𝓡 n) V (EuclideanSpace ℝ (Fin n)) ∞ :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := hcs
      contMDiffOn_invFun := hci }
  refine ⟨c, ?_, hct, ?_, hce⟩
  · rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact ⟨hp, hpΩ⟩
  · intro x
    exact ⟨dc.symm, x.property, fun _ _ => rfl⟩

private theorem coefficients_eqOn_of_eqOn
    (g : RiemannianMetric n Q)
    {a b : EuclideanSpace ℝ (Fin n) → Q}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hab : EqOn a b Ω) :
    EqOn (g.pullbackCoefficients a) (g.pullbackCoefficients b) Ω := by
  intro x hx
  have heq : a =ᶠ[𝓝 x] b := hab.eventuallyEq_of_mem (hΩ.mem_nhds hx)
  simp only [pullbackCoefficients, heq.mfderiv_eq]
  ext v w
  exact congrArg (fun q : Q => g.inner q
    (mfderiv (𝓡 n) (𝓡 n) b x v) (mfderiv (𝓡 n) (𝓡 n) b x w)) (hab hx)

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.ChartDistance

variable {n : ℕ} {ι : Type*}
  (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
  [∀ i, Nonempty (Piece U i)] (O : OverlapSystem (fun i => Piece U i))




theorem exists_neighborhood_metrics_of_local_source_jets :
    letI := quotientChartedSpace U hU O
    ∀ [IsManifold (𝓡 n) ∞ (Quotient O.setoid)]
      {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
      [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
      [∀ k, IsManifold (𝓡 n) ∞ (M k)]
      (gs : ∀ k, RiemannianMetric n (M k))
      (g : RiemannianMetric n (Quotient O.setoid))
      (h : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_hcoeff : ∀ i, EqOn (g.pullbackCoefficients
        (chartParametrization U hU (O.include i))) (h i).euclideanCoefficients (U i))
      (V : TopologicalSpace.Opens (Quotient O.setoid)) (A : ∀ k, Quotient O.setoid → M k)
      (_hA : ∀ᶠ k in atTop, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (A k) V)
      (_hjets : ∀ z ∈ V, ∃ i, ∃ W : Set (Piece U i), IsOpen W ∧
        z ∈ O.include i '' W ∧ O.include i '' W ⊆ V ∧
        ∀ m C, IsCompact C → C ⊆ Subtype.val '' W →
          TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ m ((gs k).pullbackCoefficients
              (chartParametrization U hU (A k ∘ O.include i))))
            (iteratedFDeriv ℝ m (h i).euclideanCoefficients) atTop C),
    let gV := g.pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) V)
    ∃ G : ℕ → RiemannianMetric n V,
      (∀ᶠ k in atTop,
        ContMDiff (𝓡 n) (𝓡 n) ∞ (fun y : V => A k y) ∧
        ∀ (x : V) (v w : TangentSpace (𝓡 n) x),
          (G k).inner x v w = (gs k).inner (A k x)
            (mfderiv (𝓡 n) (𝓡 n) (fun y : V => A k y) x v)
            (mfderiv (𝓡 n) (𝓡 n) (fun y : V => A k y) x w)) ∧
      ∀ p : V, ∃ c : OpenPartialHomeomorph V (EuclideanSpace ℝ (Fin n)),
        p ∈ c.source ∧ IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ c.symm c.target ∧
        ∀ m C, IsCompact C → C ⊆ c.target →
          TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ m ((G k).pullbackCoefficients c.symm))
            (iteratedFDeriv ℝ m (gV.pullbackCoefficients c.symm)) atTop C := by
  let := quotientChartedSpace U hU O
  intro _ M _ _ _ gs g h hcoeff V A hA hjets
  dsimp only
  let gV := g.pullbackOfLocalDiffeomorph Subtype.val
    (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) V)
  obtain ⟨G, hG⟩ := RiemannianMetric.exists_source_pullback_metrics gs g V A hA
  refine ⟨G, hG, ?_⟩
  intro p
  obtain ⟨i, W, hW, hpW, _, hj⟩ := hjets p p.property
  let e := quotientChart U hU O i
  have heAtlas : e ∈ maximalAtlas (𝓡 n) ∞ (Quotient O.setoid) :=
    subset_maximalAtlas ⟨i, rfl⟩
  have hp : (p : Quotient O.setoid) ∈ e.source := by
    rw [quotientChart_source]
    exact image_mono (subset_univ W) hpW
  have hpΩ : e p ∈ Subtype.val '' W := by
    obtain ⟨x, hx, hxp⟩ := hpW
    refine ⟨x, hx, ?_⟩
    rw [← hxp, quotientChart_apply]
  have hΩ : IsOpen (Subtype.val '' W) :=
    (hU i).isOpenEmbedding_subtypeVal.isOpenMap _ hW
  obtain ⟨c, hpc, hct, hcd, hce⟩ := RiemannianMetric.restricted_chart e
    (contMDiffOn_of_mem_maximalAtlas heAtlas)
    (contMDiffOn_symm_of_mem_maximalAtlas heAtlas) V p _ hΩ hp hpΩ
  refine ⟨c, hpc, hcd, ?_⟩
  have hcs : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target := hcd.contMDiffOn
  have hparam : chartParametrization U hU (O.include i) = e.symm := rfl
  have hsource : ∀ᶠ k in atTop, EqOn ((G k).pullbackCoefficients c.symm)
      ((gs k).pullbackCoefficients
        (chartParametrization U hU (A k ∘ O.include i))) c.target := by
    filter_upwards [hG] with k hk
    intro x hx
    rw [RiemannianMetric.pullbackCoefficients_eq_of_source_metric
      (gs k) (G k) (fun y : V => A k y) hk.1 hk.2 c.symm
        (hcs.contMDiffAt (c.open_target.mem_nhds hx))]
    apply RiemannianMetric.coefficients_eqOn_of_eqOn (gs k) c.open_target _ hx
    intro y hy
    exact congrArg (A k) (hce hy)
  have hlimit : EqOn (gV.pullbackCoefficients c.symm)
      (h i).euclideanCoefficients c.target := by
    intro x hx
    rw [RiemannianMetric.pullbackCoefficients_eq_of_source_metric g gV Subtype.val
      contMDiff_subtype_val (fun _ _ _ => rfl) c.symm
        (hcs.contMDiffAt (c.open_target.mem_nhds hx))]
    rw [RiemannianMetric.coefficients_eqOn_of_eqOn g c.open_target hce hx]
    exact hcoeff i (quotientChart_target U hU O i ▸ (hct hx).1)
  intro m C hC hCt
  apply ((hj m C hC (fun x hx => (hct (hCt hx)).2)).congr ?_).congr_right
  · exact (Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen
      c.open_target hlimit m).symm.mono hCt
  · filter_upwards [hsource] with k hk
    exact (Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen
      c.open_target hk m).symm.mono hCt

end PoincareConjecture.ChartDistance

namespace Poincare.AncientVolume.ScalarRatio

open PoincareConjecture

variable {X : Type*} [MetricSpace X] {p : X} (hc : RayComparison p) {n : ℕ}
  (hne : Nonempty (AsymptoticConePositive p hc))
  (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
    ∃ (d : UnitSliceRadialChartData hc n) (x : d.Level), (d.levelHomeomorph x).1 = z)
  {ι : Type*} (U : ι → Set (EuclideanSpace ℝ (Fin (n + 1))))
  (hU : ∀ i, IsOpen (U i)) [∀ i, Nonempty (Piece U i)]
  (O : OverlapSystem (fun i => Piece U i))
  (g : ι → RiemannianMetric (n + 1) (EuclideanSpace ℝ (Fin (n + 1))))
  (f : Quotient O.setoid → AsymptoticConePositive p hc)
  (hf : Topology.IsOpenEmbedding f)
  (hdist : ∀ i (x y : Piece U i), dist (f (O.include i x)) (f (O.include i y)) =
    ((g i).edist x y).toReal)





theorem exists_neighborhood_metrics_of_positive_cone_source_jets :
    letI := quotientChartedSpace U hU O
    letI := RiemannianMetric.quotient_isManifold_of_isometric_realization U hU O g f hdist
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
      [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) (M k)]
      [∀ k, IsManifold (𝓡 (n + 1)) ∞ (M k)]
      (gs : ∀ k, RiemannianMetric (n + 1) (M k))
      (V : TopologicalSpace.Opens (Quotient O.setoid)) (A : ∀ k, Quotient O.setoid → M k)
      (_hA : ∀ᶠ k in atTop,
        IsLocalDiffeomorphOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (A k) V)
      (_hjets : ∀ z ∈ V, ∃ i, ∃ W : Set (Piece U i), IsOpen W ∧
        z ∈ O.include i '' W ∧ O.include i '' W ⊆ V ∧
        ∀ m C, IsCompact C → C ⊆ Subtype.val '' W →
          TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ m ((gs k).pullbackCoefficients
              (ChartDistance.chartParametrization U hU (A k ∘ O.include i))))
            (iteratedFDeriv ℝ m (g i).euclideanCoefficients) atTop C),
    let gQ := positiveConeRealizationMetric hc hne hcover U hU O g f hf hdist
    let gV := gQ.pullbackOfLocalDiffeomorph Subtype.val
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 (n + 1)) V)
    ∃ G : ℕ → RiemannianMetric (n + 1) V,
      (∀ᶠ k in atTop,
        ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (fun y : V => A k y) ∧
        ∀ (x : V) (v w : TangentSpace (𝓡 (n + 1)) x),
          (G k).inner x v w = (gs k).inner (A k x)
            (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (fun y : V => A k y) x v)
            (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) (fun y : V => A k y) x w)) ∧
      ∀ p : V, ∃ c : OpenPartialHomeomorph V (EuclideanSpace ℝ (Fin (n + 1))),
        p ∈ c.source ∧
        IsLocalDiffeomorphOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ c.symm c.target ∧
        (∀ m C, IsCompact C → C ⊆ c.target →
          TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ m ((G k).pullbackCoefficients c.symm))
            (iteratedFDeriv ℝ m (gV.pullbackCoefficients c.symm)) atTop C) ∧
        (∀ C, IsCompact C → C ⊆ c.target →
          TendstoUniformlyOn (fun k => (G k).pullbackCoefficients c.symm)
            (gV.pullbackCoefficients c.symm) atTop C) ∧
        (∀ C, IsCompact C → C ⊆ c.target →
          TendstoUniformlyOn (fun k => fderiv ℝ ((G k).pullbackCoefficients c.symm))
            (fderiv ℝ (gV.pullbackCoefficients c.symm)) atTop C) := by
  let := quotientChartedSpace U hU O
  let := RiemannianMetric.quotient_isManifold_of_isometric_realization U hU O g f hdist
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro M _ _ _ gs V A hA hjets
  dsimp only
  obtain ⟨G, hG, hcharts⟩ :=
    ChartDistance.exists_neighborhood_metrics_of_local_source_jets U hU O gs
      (positiveConeRealizationMetric hc hne hcover U hU O g f hf hdist) g
      (positiveConeRealizationMetric_pullbackCoefficients hc hne hcover U hU O g f hf hdist)
      V A hA hjets
  refine ⟨G, hG, ?_⟩
  intro p
  obtain ⟨c, hpc, hcd, hj⟩ := hcharts p
  refine ⟨c, hpc, hcd, hj, ?_, ?_⟩
  · intro C hC hCt
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin (n + 1)))).comp_tendstoUniformlyOn
        (hj 0 C hC hCt)
  · intro C hC hCt
    have hfirst := Poincare.Analysis.Calculus.tendstoUniformlyOn_fderiv_jets
      0 (hj 1 C hC hCt)
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin (n + 1)))).comp_tendstoUniformlyOn hfirst

end Poincare.AncientVolume.ScalarRatio

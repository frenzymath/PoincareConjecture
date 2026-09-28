import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Positive.Manifold
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Gluing.Smooth













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter Poincare.Gluing Poincare.AncientVolume.ScalarRatio Manifold IsManifold
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {ι : Type*}
  (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
  [∀ i, Nonempty (Piece U i)] (O : OverlapSystem (fun i => Piece U i))
  (g : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
  {B : Type*} [MetricSpace B] (f : Quotient O.setoid → B)
  (hdist : ∀ i (x y : Piece U i), dist (f (O.include i x)) (f (O.include i y)) =
    ((g i).edist x y).toReal)

include hdist

private theorem realization_quotientChart_symm_dist (i : ι)
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (quotientChart U hU O i).target)
    (hy : y ∈ (quotientChart U hU O i).target) :
    dist (f ((quotientChart U hU O i).symm x)) (f ((quotientChart U hU O i).symm y)) =
      ((g i).edist x y).toReal := by
  have hxU : x ∈ U i := quotientChart_target U hU O i ▸ hx
  have hyU : y ∈ U i := quotientChart_target U hU O i ▸ hy
  rw [quotientChart_symm_apply U hU O i hxU, quotientChart_symm_apply U hU O i hyU]
  exact hdist i ⟨x, hxU⟩ ⟨y, hyU⟩



theorem quotient_isManifold_of_isometric_realization :
    letI := quotientChartedSpace U hU O
    IsManifold (𝓡 n) ∞ (Quotient O.setoid) := by
  let := quotientChartedSpace U hU O
  apply isManifold_of_contDiffOn (𝓡 n) ∞ (Quotient O.setoid)
  intro C C' hC hC'
  obtain ⟨i, rfl⟩ := hC
  obtain ⟨j, rfl⟩ := hC'
  let ci := quotientChart U hU O i
  let cj := quotientChart U hU O j
  have hedist : ∀ x ∈ (ci.symm.trans cj).source, ∀ y ∈ (ci.symm.trans cj).source,
      (g j).edist ((ci.symm.trans cj) x) ((ci.symm.trans cj) y) = (g i).edist x y := by
    intro x hx y hy
    change x ∈ ci.target ∧ ci.symm x ∈ cj.source at hx
    change y ∈ ci.target ∧ ci.symm y ∈ cj.source at hy
    apply (ENNReal.toReal_eq_toReal_iff' ((g j).edist_ne_top _ _) ((g i).edist_ne_top _ _)).mp
    change ((g j).edist (cj (ci.symm x)) (cj (ci.symm y))).toReal = _
    rw [← realization_quotientChart_symm_dist U hU O g f hdist j
      (cj.map_source hx.2) (cj.map_source hy.2)]
    rw [cj.left_inv hx.2, cj.left_inv hy.2]
    exact realization_quotientChart_symm_dist U hU O g f hdist i hx.1 hy.1
  simpa only [mfld_simps] using
    (g i).contDiffOn_of_edist_eq (g j) (ci.symm.trans cj).open_source hedist

end PoincareConjecture.RiemannianMetric

namespace Poincare.AncientVolume.ScalarRatio

open PoincareConjecture

variable {X : Type*} [MetricSpace X] {p : X} (hc : RayComparison p) {n : ℕ}
  (hne : Nonempty (AsymptoticConePositive p hc))
  (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
    ∃ (d : UnitSliceRadialChartData hc n) (x : d.Level), (d.levelHomeomorph x).1 = z)





theorem isLocalDiffeomorph_positiveCone_realization
    {ι : Type*} (U : ι → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hU : ∀ i, IsOpen (U i)) [∀ i, Nonempty (Piece U i)]
    (O : OverlapSystem (fun i => Piece U i))
    (g : ι → RiemannianMetric (n + 1) (EuclideanSpace ℝ (Fin (n + 1))))
    (f : Quotient O.setoid → AsymptoticConePositive p hc)
    (hf : Topology.IsOpenEmbedding f)
    (hdist : ∀ i (x y : Piece U i), dist (f (O.include i x)) (f (O.include i y)) =
      ((g i).edist x y).toReal) :
    letI := quotientChartedSpace U hU O
    letI := positiveConeChartedSpace hc n hne hcover
    IsManifold (𝓡 (n + 1)) ∞ (Quotient O.setoid) ∧
      IsLocalDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ f := by
  let := quotientChartedSpace U hU O
  let := positiveConeChartedSpace hc n hne hcover
  let hQ := RiemannianMetric.quotient_isManifold_of_isometric_realization U hU O g f hdist
  let := hQ
  let := positiveCone_isManifold hc n hne hcover
  refine ⟨hQ, ?_⟩
  intro q
  let : Nonempty (Quotient O.setoid) := ⟨q⟩
  let F := hf.toOpenPartialHomeomorph
  obtain ⟨i, x, rfl⟩ : ∃ (i : ι) (x : Piece U i), O.include i x = q := by
    induction q using Quotient.inductionOn with
    | h a => exact ⟨a.1, a.2, rfl⟩
  let ci := quotientChart U hU O i
  have hxci : O.include i x ∈ ci.source := by
    rw [quotientChart_source]
    exact ⟨x, mem_univ _, rfl⟩
  obtain ⟨d, hxd⟩ := positiveCone_radialAtlas_covers hc n hne hcover (f (O.include i x))
  let cd := d.positiveChart hne
  let A := ci.symm.trans F
  let T := A.trans cd
  have hA : ∀ a ∈ A.source, ∀ b ∈ A.source,
      dist (A a) (A b) = ((g i).edist a b).toReal := by
    intro a ha b hb
    exact RiemannianMetric.realization_quotientChart_symm_dist U hU O g f hdist i ha.1 hb.1
  have hT := (g i).smooth_isometric_charts_of_edist_eq d.metric T
    ((g i).edist_eq_on_isometric_chart_transition d.metric A cd.symm hA
      (fun a ha b hb => d.positiveChart_symm_distance hne ha hb))
  have hciAtlas : ci ∈ maximalAtlas (𝓡 (n + 1)) ∞ (Quotient O.setoid) :=
    subset_maximalAtlas ⟨i, rfl⟩
  have hcdAtlas : cd ∈ maximalAtlas (𝓡 (n + 1)) ∞ (AsymptoticConePositive p hc) :=
    subset_maximalAtlas ⟨d, rfl⟩
  let Ci : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
      (Quotient O.setoid) (EuclideanSpace ℝ (Fin (n + 1))) ∞ := {
    toPartialEquiv := ci.toPartialEquiv
    open_source := ci.open_source
    open_target := ci.open_target
    contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hciAtlas
    contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hciAtlas }
  let Ct : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) ∞ := {
    toPartialEquiv := T.toPartialEquiv
    open_source := T.open_source
    open_target := T.open_target
    contMDiffOn_toFun := hT.1
    contMDiffOn_invFun := hT.2.1 }
  let Cd : PartialDiffeomorph (𝓡 (n + 1)) (𝓡 (n + 1))
      (AsymptoticConePositive p hc) (EuclideanSpace ℝ (Fin (n + 1))) ∞ := {
    toPartialEquiv := cd.toPartialEquiv
    open_source := cd.open_source
    open_target := cd.open_target
    contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hcdAtlas
    contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hcdAtlas }
  have hxT : ci (O.include i x) ∈ T.source := by
    refine ⟨⟨ci.map_source hxci, ?_⟩, ?_⟩
    · exact mem_univ _
    · change f (ci.symm (ci (O.include i x))) ∈ cd.source
      rw [ci.left_inv hxci]
      exact hxd
  refine ⟨(Ci.trans Ct).trans Cd.symm, ⟨⟨hxci, hxT⟩, ?_⟩, ?_⟩
  · exact cd.map_source hxT.2
  intro y hy
  have hyci : y ∈ ci.source := hy.1.1
  have hyd : f (ci.symm (ci y)) ∈ cd.source := hy.1.2.2
  change f y = cd.symm (cd (f (ci.symm (ci y))))
  rw [cd.left_inv hyd, ci.left_inv hyci]

end Poincare.AncientVolume.ScalarRatio

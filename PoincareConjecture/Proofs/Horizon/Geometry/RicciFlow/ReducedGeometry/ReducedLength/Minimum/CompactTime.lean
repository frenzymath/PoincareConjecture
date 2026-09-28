import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.Infimum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Norm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_reducedLength_self_le_on_interval (K : AncientKappaSolution 2 M)
    (p : M) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ tau : ℝ, 0 < tau → tau ≤ B →
      reducedLength K.flow 0 p p tau ≤ C * tau / 2 := by
  have hR : ContinuousOn (fun s => (K.flow.connection (-s)).scalarCurvature p)
      (Icc 0 B) :=
    (K.flow.continuousOn_scalarCurvature_ancient_surface p).comp
      continuous_neg.continuousOn (fun _ hs => neg_nonpos.mpr hs.1)
  obtain ⟨A, hA⟩ := isCompact_Icc.bddAbove_image hR
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro tau htau htauB
  apply K.reducedLength_self_le_of_scalar_le p htau (le_max_right A 0)
  intro s hs
  exact (hA (mem_image_of_mem _ ⟨hs.1, hs.2.trans htauB⟩)).trans (le_max_left A 0)

theorem exists_uniform_reducedLength_comparator (K : AncientKappaSolution 2 M)
    (p : M) (B : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ tau : ℝ, 0 < tau → tau ≤ B →
      reducedLength K.flow 0 p p tau ≤ L := by
  obtain ⟨C, hC, hbound⟩ := K.exists_reducedLength_self_le_on_interval p B
  refine ⟨C * max B 0 / 2, by positivity, ?_⟩
  intro tau htau htauB
  apply (hbound tau htau htauB).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (htauB.trans (le_max_left _ _)) hC) (by norm_num)

theorem exists_compact_reducedLength_sublevels (K : AncientKappaSolution 2 M)
    (p : M) (B A : ℝ) :
    ∃ S : Set M, IsCompact S ∧ ∀ tau : ℝ, 0 < tau → tau ≤ B →
      {q | reducedLength K.flow 0 p q tau ≤ A} ⊆ S := by
  let R := Real.sqrt (4 * max B 0 * max A 0)
  refine ⟨{q | (K.flow.metric 0).edist p q ≤ ENNReal.ofReal R},
    (K.flow.metric 0).isCompact_closedBall_of_metricComplete (K.complete 0 le_rfl) p R, ?_⟩
  intro tau htau htauB q hq
  have hq' : reducedLength K.flow 0 p q tau ≤ max A 0 :=
    hq.trans (le_max_left _ _)
  change (K.flow.metric 0).edist p q ≤ ENNReal.ofReal R
  apply le_trans (K.reducedLength_sublevel_subset_closedBall p htau (max A 0) hq')
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (htauB.trans (le_max_left _ _)) (by norm_num))
    (le_max_right _ _)

theorem isCompact_closure_spacetime_reducedLength_sublevel (K : AncientKappaSolution 2 M)
    (p : M) (B A : ℝ) :
    IsCompact (closure {z : M × ℝ |
      0 < z.2 ∧ z.2 ≤ B ∧ reducedLength K.flow 0 p z.1 z.2 ≤ A}) := by
  obtain ⟨S, hS, hsub⟩ := K.exists_compact_reducedLength_sublevels p B A
  have hcompact := hS.prod (isCompact_Icc (a := (0 : ℝ)) (b := B))
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hcompact.isClosed
  rintro ⟨q, tau⟩ ⟨htau, htauB, hq⟩
  exact ⟨hsub tau htau htauB hq, htau.le, htauB⟩

theorem continuousOn_scalarCurvature_spacetime_Icc (K : AncientKappaSolution 2 M)
    {B : ℝ} (hB : 0 < B) :
    ContinuousOn (fun z : ℝ × M => (K.flow.connection z.1).scalarCurvature z.2)
      (Icc (-B) 0 ×ˢ univ) := by
  have hab : -B < 0 := neg_lt_zero.mpr hB
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow K.flow
    (show Icc (-B) 0 ⊆ Iic 0 from fun _ ht => ht.2) ordConnected_Icc
    ⟨-B, ⟨le_rfl, hab.le⟩, 0, ⟨hab.le, le_rfl⟩, hab.ne⟩
  exact (F.contMDiffOn_scalarCurvature_surface_Icc hab).continuousOn

set_option backward.isDefEq.respectTransparency true in

theorem exists_curvature_bound_on_compact (K : AncientKappaSolution 2 M)
    {S : Set M} (hS : IsCompact S) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (-B) 0, ∀ q ∈ S,
      |(K.flow.connection t).curvatureTensorNorm q| ≤ C := by
  have hR : ContinuousOn (fun z : ℝ × M => |(K.flow.connection z.1).scalarCurvature z.2|)
      (Icc (-B) 0 ×ˢ S) :=
    (K.continuousOn_scalarCurvature_spacetime_Icc hB).abs.mono
      (prod_mono Subset.rfl (subset_univ S))
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hS).bddAbove_image hR
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht q hq
  have hnorm : |(K.flow.connection t).curvatureTensorNorm q| =
      |(K.flow.connection t).scalarCurvature q| :=
    (congrArg abs ((K.flow.connection t).curvatureTensorNorm_eq_abs_scalarCurvature q)).trans
      (abs_abs _)
  have hscalar : |(K.flow.connection t).scalarCurvature q| ≤ C :=
    hC ⟨(t, q), ⟨ht, hq⟩, rfl⟩
  exact hnorm.le.trans (hscalar.trans (le_max_left C 0))

theorem regularizedPotential_continuousOn (K : AncientKappaSolution 2 M)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (S : Set M) :
    ContinuousOn (fun z : ℝ × M =>
      2 * z.1 ^ 2 * (K.flow.connection (0 - z.1 ^ 2)).scalarCurvature z.2)
      (Icc a b ×ˢ S) := by
  have hB : 0 < b ^ 2 + 1 := by positivity
  have hparam : Continuous (fun z : ℝ × M => (0 - z.1 ^ 2, z.2)) :=
    (continuous_const.sub (continuous_fst.pow 2)).prodMk continuous_snd
  have hscalar := (K.continuousOn_scalarCurvature_spacetime_Icc hB).comp
    hparam.continuousOn (show MapsTo (fun z : ℝ × M => (0 - z.1 ^ 2, z.2))
      (Icc a b ×ˢ S) (Icc (-(b ^ 2 + 1)) 0 ×ˢ univ) from by
        intro z hz
        have hsq := (sq_le_sq₀ (ha.trans hz.1.1) (ha.trans hab)).mpr hz.1.2
        exact ⟨⟨by linarith, by nlinarith [sq_nonneg z.1]⟩, mem_univ _⟩)
  exact (continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul hscalar

end PoincareConjecture.AncientKappaSolution

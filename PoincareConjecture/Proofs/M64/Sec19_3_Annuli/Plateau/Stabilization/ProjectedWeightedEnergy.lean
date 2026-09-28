import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.RetainedCircle
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeightedAnnulusEnergyIdentity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusReduction












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem auxiliaryCircle_projected_gram_diagonal_le
    (P : M62.CircleProductData F circumference) (time : ℝ)
    (f : LoopPlane → P.charts.Point) (z : LoopPlane)
    (hf : MDifferentiableAt (𝓡 2) (𝓡 (n + 1)) f z) (i : Fin 2) :
    m60AreaGram (F.metric time) (fun p => (f p).1) z i i ≤
      m60AreaGram (P.flow.metric time) f z i i := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞
      (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hcomp : mfderiv (𝓡 2) (𝓡 n) (fun p => (f p).1) z
      (EuclideanSpace.basisFun (Fin 2) ℝ i) =
      (P.charts.split (f z) (mfderiv (𝓡 2) (𝓡 (n + 1)) f z
        (EuclideanSpace.basisFun (Fin 2) ℝ i))).1 := by
    rw [P.charts.split_space]
    exact mfderiv_comp_apply (f := f) (g := (Prod.fst : P.charts.Point → M)) z
      (hfst.mdifferentiableAt (by simp)) hf (EuclideanSpace.basisFun (Fin 2) ℝ i)
  dsimp only [m60AreaGram]
  erw [hcomp]
  rw [P.metric_eq]
  exact le_add_of_nonneg_right
    ((P.circle.metricOnPoints.toRiemannianMetric.toCore (f z).2).re_inner_nonneg _)



theorem auxiliaryCircle_projected_weightedEnergy [T2Space M] [CompactSpace M]
    (P : M62.CircleProductData F circumference) (time : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric time) c0 c1)
    {r : ℝ} (hr : 0 < r) :
    ∃ D : M64Annulus (F.metric time) (fun x => (c0 x).1) (fun x => (c1 x).1),
      D.map = (fun p => (A.map p).1) ∧
        m64ClassicalWeightedGramEnergy (F.metric time) D r ≤
          m64ClassicalWeightedGramEnergy (P.flow.metric time) A r := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  obtain ⟨-, D, hmap, -, -, -⟩ := m64ProjectedAnnulus_of_annulus P time c0 c1 A
  refine ⟨D, hmap, ?_⟩
  apply integral_mono_ae (D.weightedGramEnergy_integrable r) (A.weightedGramEnergy_integrable r)
  filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet,
    ae_restrict_of_ae A.ae_manifold_differentiable] with z hz hdiff
  rw [hmap]
  have h0 := auxiliaryCircle_projected_gram_diagonal_le P time A.map z (hdiff hz) 0
  have h1 := auxiliaryCircle_projected_gram_diagonal_le P time A.map z (hdiff hz) 1
  exact div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left h0 hr.le)
      (mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hr).le)) (by norm_num)

end PoincareConjecture.M64

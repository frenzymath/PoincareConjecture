import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.ProjectionComplete
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



def auxiliaryCircleSection (P : M62.CircleProductData F circumference)
    (q : P.circle.Point) : M → P.charts.Point := fun x => (x, q)



theorem auxiliaryCircle_section_contMDiff
    (P : M62.CircleProductData F circumference) (q : P.circle.Point) :
    ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (auxiliaryCircleSection P q) := by
  let := P.charts.chartedSpace
  exact P.charts.from_product_smooth.comp (contMDiff_id.prodMk contMDiff_const)



theorem auxiliaryCircle_section_mfderiv_split
    (P : M62.CircleProductData F circumference) (q : P.circle.Point)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    P.charts.split (x, q)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (auxiliaryCircleSection P q) x v) =
        (v, 0) := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  have hi := (auxiliaryCircle_section_contMDiff P q).mdifferentiable (by simp)
  have hf : MDifferentiable (𝓡 (n + 1)) (𝓡 n) (Prod.fst : P.charts.Point → M) :=
    (contMDiff_fst.comp P.charts.to_product_smooth).mdifferentiable (by simp)
  have hs : MDifferentiable (𝓡 (n + 1)) (𝓡 1)
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    (contMDiff_snd.comp P.charts.to_product_smooth).mdifferentiable (by simp)
  apply Prod.ext
  · rw [P.charts.split_space]
    have h := mfderiv_comp_apply (f := auxiliaryCircleSection P q)
      (g := (Prod.fst : P.charts.Point → M)) x (hf (x, q)) (hi x) v
    have hid : (Prod.fst : P.charts.Point → M) ∘ auxiliaryCircleSection P q = id := rfl
    rw [hid, mfderiv_id] at h
    exact h.symm
  · rw [P.charts.split_circle]
    have h := mfderiv_comp_apply (f := auxiliaryCircleSection P q)
      (g := (Prod.snd : P.charts.Point → P.circle.Point)) x (hs (x, q)) (hi x) v
    have hc : (Prod.snd : P.charts.Point → P.circle.Point) ∘
        auxiliaryCircleSection P q = fun _ => q := rfl
    rw [hc, mfderiv_const] at h
    exact h.symm



theorem auxiliaryCircle_section_metric
    (P : M62.CircleProductData F circumference) (t : ℝ) (q : P.circle.Point)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    (P.flow.metric t).inner (x, q)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (auxiliaryCircleSection P q) x v)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (auxiliaryCircleSection P q) x w) =
        (F.metric t).inner x v w := by
  rw [P.metric_eq, auxiliaryCircle_section_mfderiv_split,
    auxiliaryCircle_section_mfderiv_split]
  simp



theorem auxiliaryCircle_section_edist
    (P : M62.CircleProductData F circumference) (t : ℝ) (q : P.circle.Point)
    (x y : M) :
    (P.flow.metric t).edist (x, q) (y, q) = (F.metric t).edist x y := by
  apply le_antisymm
  · have hnorm (z : M) (v : TangentSpace (𝓡 n) z) :
        (P.flow.metric t).tangentNorm (z, q)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (auxiliaryCircleSection P q) z v) ≤
            1 * (F.metric t).tangentNorm z v := by
      unfold RiemannianMetric.tangentNorm
      rw [auxiliaryCircle_section_metric, one_mul]
    have h := RiemannianMetric.edist_le_mul_of_tangentNorm_mfderiv_le
      (F.metric t) (P.flow.metric t) ((auxiliaryCircle_section_contMDiff P q).of_le (by simp))
      (by norm_num : (0 : ℝ) < 1) hnorm x y
    simpa only [auxiliaryCircleSection, ENNReal.ofReal_one, one_mul] using h
  · simpa using m64Projection_edist_le P t (x, q) (y, q)



theorem auxiliaryCircle_section_areaGram
    (P : M62.CircleProductData F circumference) (t : ℝ) (q : P.circle.Point)
    {f : LoopPlane → M} {z : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z) :
    m60AreaGram (P.flow.metric t) (auxiliaryCircleSection P q ∘ f) z =
      m60AreaGram (F.metric t) f z := by
  have hcomp (i : Fin 2) := mfderiv_comp_apply (f := f)
    (g := auxiliaryCircleSection P q) z
    ((auxiliaryCircle_section_contMDiff P q).mdifferentiableAt (by simp)) hf
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  ext i j
  dsimp only [m60AreaGram]
  erw [hcomp i, hcomp j]
  exact auxiliaryCircle_section_metric P t q _ _ _



theorem auxiliaryCircle_lift_annulus
    (P : M62.CircleProductData F circumference) (t : ℝ) (q : P.circle.Point)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric t) c0 c1) :
    ∃ B : M64Annulus (P.flow.metric t) (fun x => (c0 x, q)) (fun x => (c1 x, q)),
      B.map = (fun z => (A.map z, q)) ∧ B.area = A.area := by
  have hi := auxiliaryCircle_section_contMDiff P q
  have hdiff : ∀ᵐ z ∂volume, z ∈ m64AnnulusDomain →
      MDifferentiableAt (𝓡 2) (𝓡 (n + 1)) (auxiliaryCircleSection P q ∘ A.map) z := by
    filter_upwards [A.ae_manifold_differentiable] with z hz
    intro hmem
    exact (hi.mdifferentiableAt (by simp)).comp z (hz hmem)
  have hdensity : m60AreaDensity (P.flow.metric t) (auxiliaryCircleSection P q ∘ A.map)
      =ᵐ[volume.restrict m64AnnulusDomain] m60AreaDensity (F.metric t) A.map := by
    filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet,
      ae_restrict_of_ae A.ae_manifold_differentiable] with z hz hdiff
    unfold m60AreaDensity
    rw [auxiliaryCircle_section_areaGram P t q (hdiff hz)]
  let B : M64Annulus (P.flow.metric t) (fun x => (c0 x, q)) (fun x => (c1 x, q)) := {
    map := fun z => (A.map z, q)
    continuous_on_domain := hi.continuous.comp_continuousOn A.continuous_on_domain
    periodic := fun x s => by simp only [A.periodic]
    lower_boundary := fun x => by simp only [A.lower_boundary]
    upper_boundary := fun x => by simp only [A.upper_boundary]
    lipschitz_constant := A.lipschitz_constant
    lipschitz_nonnegative := A.lipschitz_nonnegative
    lipschitz_on_domain := fun x y => by
      rw [auxiliaryCircle_section_edist]
      exact A.lipschitz_on_domain x y
    ae_manifold_differentiable := hdiff
    area_integrable := A.area_integrable.congr hdensity.symm }
  exact ⟨B, rfl, integral_congr_ae hdensity⟩

end PoincareConjecture.M64

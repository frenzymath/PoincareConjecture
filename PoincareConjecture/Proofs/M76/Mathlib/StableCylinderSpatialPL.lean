import PoincareConjecture.Proofs.M76.Mathlib.PLChartMaps
import PoincareConjecture.Proofs.M76.Mathlib.StableCylinderSpatialProduct

set_option autoImplicit false

open Set Geometry

namespace StableCylinder

theorem plInCharts_spatial_product
    {E F X Y ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] [TopologicalSpace Y]
    {Q : ι → OpenPartialHomeomorph E X} {R : κ → OpenPartialHomeomorph F Y}
    (hQ : PLInCharts Q Q id univ) (hR : PLInCharts R R id univ)
    (hQc : ∀ x, ∃ i, x ∈ (Q i).target) (hRc : ∀ y, ∃ j, y ∈ (R j).target)
    (p : ℝ) [Fact (0 < p)] {delta : ℝ} (hd1 : delta ≤ 1) (hdp : delta < p / 2)
    (f : X × ℝ → Y × ℝ) (g : X → Y) (U : Set X)
    (hf : PLInCharts (prodCharts Q (realCharts ℝ)) (prodCharts R (realCharts ℝ))
      f (univ ×ˢ Ioo (-1) 1)) (hg : PLInCharts Q R g U)
    (G : X × AddCircle p → Y × AddCircle p)
    (hGo : EqOn G (fun z => (g z.1, z.2)) (U ×ˢ univ))
    (hGn : ∀ x : X, ∀ s ∈ Ioo (-delta) delta,
      G (x, (s : AddCircle p)) = ((f (x, s)).1, ((f (x, s)).2 : AddCircle p))) :
    PLInCharts (prodCharts Q (AddCircle.quotientCharts p))
      (prodCharts R (AddCircle.quotientCharts p)) G
      ((U ×ˢ univ) ∪ (univ ×ˢ (((↑) : ℝ → AddCircle p) '' Ioo (-delta) delta))) := by
  let q := AddCircle.shortArcQuotient p delta
  have hqS : q.source = Ioo (-delta) delta := AddCircle.shortArcQuotient_source p hdp
  have hqT : q.target = ((↑) : ℝ → AddCircle p) '' Ioo (-delta) delta :=
    AddCircle.shortArcQuotient_target p hdp
  have hold := (hg.prodMap (AddCircle.plInCharts_id p)).congr hGo.symm
  have hpre := hQ.prodMap (AddCircle.plInCharts_shortArc_inverse p delta)
  have hfirst := hf.comp_mapsTo hpre
    (prodCharts_cover Q (realCharts ℝ) hQc (realCharts_cover ℝ)) (by
      intro z hz
      have hs : q.symm z.2 ∈ Ioo (-delta) delta := hqS ▸ q.map_target hz.2
      refine ⟨mem_univ _, ?_⟩
      change q.symm z.2 ∈ Ioo (-1) 1
      constructor <;> linarith [hs.1, hs.2])
  have hpost := (hR.prodMap (AddCircle.plInCharts_coe p)).mono isOpen_univ
    (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have hnew := hpost.comp_mapsTo hfirst
    (prodCharts_cover R (realCharts ℝ) hRc (realCharts_cover ℝ)) (fun _ _ => mem_univ _)
  have hnewG : PLInCharts (prodCharts Q (AddCircle.quotientCharts p))
      (prodCharts R (AddCircle.quotientCharts p)) G (univ ×ˢ q.target) := by
    apply hnew.congr
    intro z hz
    have hs : q.symm z.2 ∈ Ioo (-delta) delta := hqS ▸ q.map_target hz.2
    have he := hGn z.1 (q.symm z.2) hs
    have hrep : ((q.symm z.2 : ℝ) : AddCircle p) = z.2 := q.right_inv hz.2
    rw [hrep] at he
    exact he.symm
  rw [← hqT]
  exact hold.union hnewG

end StableCylinder

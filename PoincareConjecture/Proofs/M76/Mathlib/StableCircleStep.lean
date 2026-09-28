import PoincareConjecture.Proofs.M76.Mathlib.StableCylinderPLConjugation
import PoincareConjecture.Proofs.M76.Mathlib.StableCylinderSpatialPL
import PoincareConjecture.Proofs.M76.Mathlib.StablePLProductCompletion
import PoincareConjecture.Proofs.M76.Mathlib.CompactCylinderHeight

set_option autoImplicit false

open Set Geometry

namespace StableCylinder

theorem exists_stable_circle_step
    {E F X Y ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    {Q : ι → OpenPartialHomeomorph E X} {R : κ → OpenPartialHomeomorph F Y}
    (hQ : PLInCharts Q Q id univ) (hR : PLInCharts R R id univ)
    (hQc : ∀ x, ∃ i, x ∈ (Q i).target) (hRc : ∀ y, ∃ j, y ∈ (R j).target)
    (p : ℝ) [Fact (0 < p)] (hp : 4 < p)
    {delta : ℝ} (hd : 0 < delta) (hd1 : delta < 1)
    (f : X × ℝ → Y × ℝ) (g : X → Y) (U : Set X) (hU : IsOpen U)
    (hf : IsLocalHomeomorphOn f (univ ×ˢ Ioo (-1) 1))
    (hfimage : MapsTo f (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1))
    (hg : IsLocalHomeomorphOn g U)
    (hprod : EqOn f (fun z => (g z.1, z.2)) (U ×ˢ Ioo (-1) 1))
    (hfPL : PLInCharts (prodCharts Q (realCharts ℝ)) (prodCharts R (realCharts ℝ))
      f (univ ×ˢ Ioo (-1) 1)) (hgPL : PLInCharts Q R g U)
    (K : Set (X × AddCircle p)) (w : X × AddCircle p → ℝ)
    (hc : Continuous w) (hw : ∀ z, w z ∈ Icc 0 1)
    (hout : ∀ z, z ∉ (U ×ˢ univ) ∪
      (univ ×ˢ (((↑) : ℝ → AddCircle p) '' Ioo (-delta) delta)) → w z = 0)
    (hcore : ∀ z ∈ K, w z = 1)
    (hwPL : ∀ i, LocallyPiecewiseAffineOn
      (w ∘ prodCharts Q (AddCircle.quotientCharts p) i)
      (prodCharts Q (AddCircle.quotientCharts p) i).source) :
    let W := (U ×ˢ univ) ∪
      (univ ×ˢ (((↑) : ℝ → AddCircle p) '' Ioo (-delta) delta))
    let A := prodCharts Q (AddCircle.quotientCharts p)
    let B := prodCharts R (AddCircle.quotientCharts p)
    ∃ (F : (X × AddCircle p) × ℝ → (Y × AddCircle p) × ℝ)
      (G : X × AddCircle p → Y × AddCircle p),
      IsLocalHomeomorphOn F (univ ×ˢ Ioo (-1) 1) ∧
      MapsTo F (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) ∧
      PLInCharts (prodCharts A (realCharts ℝ)) (prodCharts B (realCharts ℝ))
        F (univ ×ˢ Ioo (-1) 1) ∧
      IsLocalHomeomorphOn G W ∧ PLInCharts A B G W ∧
      EqOn F (fun z => (G z.1, z.2)) (K ×ˢ Ioo (-1) 1) ∧
      EqOn G (fun z => (g z.1, z.2)) (U ×ˢ univ) ∧
      (∀ x : X, ∀ s ∈ Ioo (-delta) delta,
        G (x, (s : AddCircle p)) = ((f (x, s)).1, ((f (x, s)).2 : AddCircle p))) ∧
      (∀ z ∈ univ ×ˢ Ioo (-1) 1,
        ∃ t ∈ Ioo (-1) 1, (F z).1.1 = (f (z.1.1, t)).1) ∧
      ∀ z ∈ W, ∃ t ∈ Ioo (-1) 1, (G z).1 = (f (z.1, t)).1 := by
  have hdp : delta < p / 2 := by linarith
  have hheight : ∀ z ∈ univ ×ˢ Ioo (-1) 1, |(f z).2| < 1 :=
    fun _ hz => abs_lt.mpr (hfimage hz).2
  obtain ⟨a, hda, ha1, ha⟩ := exists_uniform_height_bound
    (fun z => (f z).2) hf.continuousOn.snd hheight hd hd1
  obtain ⟨L, hrot, hinv, _, hL, hLi, hLPL⟩ :=
    AddCircle.exists_supported_cylinder_quarterTurn_of_lt p hp
      (r := a) (R := (a + 1) / 2) (hd.trans hda) (by linarith) (by linarith)
  have ha' : ∀ x : X, ∀ s : ℝ, |s| ≤ delta → |(f (x, s)).2| ≤ a :=
    fun x s hs => (ha (x, s) ⟨mem_univ _, abs_le.mp hs⟩).le
  obtain ⟨G, hG, hGo, hGn, hGprod, hGprov⟩ :=
    exists_spatial_product p hd hd1.le hdp hda.le L hL hrot hinv f g U hU hf hg hprod ha'
  have hGPL := plInCharts_spatial_product hQ hR hQc hRc p hd1.le hdp
    f g U hfPL hgPL G hGo hGn
  obtain ⟨hh, hhimage, hhprov⟩ := conjugation_isLocalHomeomorphOn L hL hLi f hf hfimage
  obtain ⟨hforwardPL, hinversePL⟩ := AddCircle.plInCharts_cylinder_homeomorph p L hLPL
  have hhPL := plInCharts_conjugation hQ hR (AddCircle.plInCharts_id p)
    hQc hRc (AddCircle.quotientCharts_cover p) L hL hforwardPL hinversePL f hfPL
  let W := (U ×ˢ univ) ∪
    (univ ×ˢ (((↑) : ℝ → AddCircle p) '' Ioo (-delta) delta))
  let A := prodCharts Q (AddCircle.quotientCharts p)
  let B := prodCharts R (AddCircle.quotientCharts p)
  have hAid : PLInCharts A A id univ :=
    (hQ.prodMap (AddCircle.plInCharts_id p)).mono isOpen_univ
      (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have hthin : univ ×ˢ Ioo (-delta) delta ⊆
      (univ : Set (X × AddCircle p)) ×ˢ Ioo (-1) 1 := by
    intro z hz
    exact ⟨mem_univ _, ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  obtain ⟨F, hF, hFimage, hFcore, hFPL, hFprov⟩ :=
    PLFiberCompression.exists_stable_PL_product_completion A B hAid
      (prodCharts_cover Q (AddCircle.quotientCharts p) hQc (AddCircle.quotientCharts_cover p))
      W K hGPL.isOpen delta hd hd1.le (conjugation L f) G
      (hh.mono hthin) hG (fun _ hz => hhimage (hthin hz)) hGprod
      (hhPL.mono (isOpen_univ.prod isOpen_Ioo) hthin) hGPL
      w hc hw hout hcore hwPL
  refine ⟨F, G, hF, hFimage, hFPL, hG, hGPL, hFcore, hGo, hGn, ?_, hGprov⟩
  intro z hz
  rcases hFprov z hz with ⟨t, ht, he⟩ | ⟨hxW, he⟩
  · obtain ⟨s, hs, hsp⟩ := hhprov (z.1, t) (hthin ⟨mem_univ _, ht⟩)
    exact ⟨s, hs, (congrArg Prod.fst he).trans hsp⟩
  · obtain ⟨s, hs, hsp⟩ := hGprov z.1 hxW
    exact ⟨s, hs, (congrArg Prod.fst he).trans hsp⟩

end StableCylinder

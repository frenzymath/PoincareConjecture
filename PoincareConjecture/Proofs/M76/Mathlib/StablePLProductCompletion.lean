import PoincareConjecture.Proofs.M76.Mathlib.PLChartFiberCompression
import PoincareConjecture.Proofs.M76.Mathlib.StableProductCompletion











set_option autoImplicit false

open Set Geometry

namespace PLFiberCompression






theorem exists_stable_PL_product_completion
    {E F X Y ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] [TopologicalSpace Y]
    (Q : ι → OpenPartialHomeomorph E X) (R : κ → OpenPartialHomeomorph F Y)
    (hQ : PLInCharts Q Q id univ) (hcover : ∀ x, ∃ i, x ∈ (Q i).target)
    (U K : Set X) (hU : IsOpen U) (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (h : X × ℝ → Y × ℝ) (g : X → Y)
    (hh : IsLocalHomeomorphOn h (univ ×ˢ Ioo (-delta) delta))
    (hg : IsLocalHomeomorphOn g U)
    (hheight : MapsTo h (univ ×ˢ Ioo (-delta) delta) (univ ×ˢ Ioo (-1) 1))
    (hprod : EqOn h (fun z => (g z.1, z.2)) (U ×ˢ Ioo (-delta) delta))
    (hhPL : PLInCharts (prodCharts Q (realCharts ℝ)) (prodCharts R (realCharts ℝ))
      h (univ ×ˢ Ioo (-delta) delta))
    (hgPL : PLInCharts Q R g U)
    (w : X → ℝ) (hc : Continuous w) (hw : ∀ x, w x ∈ Icc 0 1)
    (hout : ∀ x, x ∉ U → w x = 0) (hcore : ∀ x ∈ K, w x = 1)
    (hwPL : ∀ i, LocallyPiecewiseAffineOn (w ∘ Q i) (Q i).source) :
    ∃ F : X × ℝ → Y × ℝ,
      IsLocalHomeomorphOn F (univ ×ˢ Ioo (-1) 1) ∧
      MapsTo F (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) ∧
      EqOn F (fun z => (g z.1, z.2)) (K ×ˢ Ioo (-1) 1) ∧
      PLInCharts (prodCharts Q (realCharts ℝ)) (prodCharts R (realCharts ℝ))
        F (univ ×ˢ Ioo (-1) 1) ∧
      ∀ z ∈ univ ×ˢ Ioo (-1) 1,
        (∃ t ∈ Ioo (-delta) delta, (F z).1 = (h (z.1, t)).1) ∨
          (z.1 ∈ U ∧ (F z).1 = g z.1) := by
  obtain ⟨F, B, hF, himage, hcoreF, hformula, hBh, hBg, hCmap⟩ :=
    exists_stable_product_completion_with_formula U K hU delta hd hd1
      h g hh hg hheight hprod w hc hw hout hcore
  let C := homeomorph delta hd w (fun x => (hw x).1) hc
  let A := prodCharts Q (realCharts ℝ)
  let D := prodCharts R (realCharts ℝ)
  have hBthin : PLInCharts A D B (univ ×ˢ Ioo (-delta) delta) := hhPL.congr hBh.symm
  have hid := plInCharts_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ
  have hBprod : PLInCharts A D B (U ×ˢ Ioo (-1) 1) :=
    ((hgPL.prodMap hid).mono (hU.prod isOpen_Ioo)
      (fun _ hz => ⟨hz.1, mem_univ _⟩)).congr hBg.symm
  have hBPL := hBthin.union hBprod
  have hCPL : PLInCharts A A C (univ ×ˢ Ioo (-1) 1) :=
    (plInCharts_homeomorph Q hQ delta hd w (fun x => (hw x).1) hc hwPL).mono
      (isOpen_univ.prod isOpen_Ioo) (subset_univ _)
  have hFPL : PLInCharts A D F (univ ×ˢ Ioo (-1) 1) := by
    rw [hformula]
    exact hBPL.comp_mapsTo hCPL (prodCharts_cover Q (realCharts ℝ)
      hcover (realCharts_cover ℝ)) hCmap
  refine ⟨F, hF, himage, hcoreF, hFPL, ?_⟩
  intro z hz
  rcases hCmap hz with ht | hp
  · refine Or.inl ⟨(C z).2, ht.2, ?_⟩
    rw [hformula]
    exact congrArg Prod.fst (hBh ht)
  · refine Or.inr ⟨hp.1, ?_⟩
    rw [hformula]
    exact congrArg Prod.fst (hBg hp)

end PLFiberCompression

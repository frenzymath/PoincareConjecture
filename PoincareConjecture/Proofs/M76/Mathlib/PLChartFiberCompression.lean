import PoincareConjecture.Proofs.M76.Mathlib.PLChartMaps
import PoincareConjecture.Proofs.M76.Mathlib.PLFiberCompression

set_option autoImplicit false

open Set Geometry

namespace PLFiberCompression

theorem plInCharts_homeomorph
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (Q : ι → OpenPartialHomeomorph E X)
    (hQ : PLInCharts Q Q id univ)
    (delta : ℝ) (hd : 0 < delta) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hc : Continuous w)
    (hPL : ∀ i, LocallyPiecewiseAffineOn (w ∘ Q i) (Q i).source) :
    PLInCharts (prodCharts Q (realCharts ℝ)) (prodCharts Q (realCharts ℝ))
      (homeomorph delta hd w hw hc) univ := by
  let C := homeomorph delta hd w hw hc
  let A := prodCharts Q (realCharts ℝ)
  refine ⟨isOpen_univ, C.continuous.continuousOn, ?_⟩
  intro i j
  let D := chartMapDomain (A i) (A j) C univ
  have hD : IsOpen D := isOpen_chartMapDomain (A i) (A j) C univ isOpen_univ
    C.continuous.continuousOn
  let fst := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  let snd := (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap
  have hf : LocallyPiecewiseAffineOn fst univ := locallyPiecewiseAffineOn_affine fst isOpen_univ
  have hbase := ((hQ.coordinates i.1 j.1).comp hf).mono hD
    (fun z hz => ⟨mem_univ _, ⟨⟨hz.1.1.1, mem_univ _⟩, hz.2.1⟩⟩)
  have hwidth := ((hPL i.1).comp hf).mono hD
    (fun z hz => ⟨mem_univ _, hz.1.1.1⟩)
  have hheight : LocallyPiecewiseAffineOn snd D := locallyPiecewiseAffineOn_affine snd hD
  exact hbase.prod_mk (locallyPiecewiseAffineOn_value delta hwidth hheight)

end PLFiberCompression

import PoincareConjecture.Proofs.M08.PullbackRegularity
import PoincareConjecture.Proofs.M08.IndexContinuity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem supportedChartField_contMDiffOn {C U : Set ℝ}
    (hU : IsOpen U) (hCU : C ⊆ U) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (x : M) (η : ℝ → EuclideanSpace ℝ (Fin n)) (hη : ContDiff ℝ ∞ η)
    (hsrc : ∀ s ∈ C, s ∈ tsupport η →
      α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
        (chartFrame x (η s) (α s))) C := by
  intro s hs
  by_cases hsupport : s ∈ tsupport η
  · let N := U ∩ α ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
    have hN : IsOpen N := hα.continuousOn.isOpen_inter_preimage hU
      (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
    have hsN : s ∈ N := ⟨hCU hs, hsrc s hs hsupport⟩
    have hfield := closedChartField_contMDiffOn x α η
      (hα.mono (show C ∩ N ⊆ U from inter_subset_right.trans inter_subset_left))
      hη.contDiffOn (show MapsTo α (C ∩ N)
        (chartAt (EuclideanSpace ℝ (Fin n)) x).source from fun _ hr ↦ hr.2.2)
    exact (contMDiffWithinAt_inter (hN.mem_nhds hsN)).mp (hfield s ⟨hs, hsN⟩)
  · let N := (tsupport η)ᶜ
    have hN : IsOpen N := (isClosed_tsupport η).isOpen_compl
    have hzero : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
        (fun r ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α r)
          (0 : TangentSpace (𝓡 n) (α r))) (C ∩ N) :=
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡 n))).comp_contMDiffOn
        (hα.mono (inter_subset_left.trans hCU))
    have hfield : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
        (fun r ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α r)
          (chartFrame x (η r) (α r))) (C ∩ N) := by
      apply hzero.congr
      intro r hr
      simp only [image_eq_zero_of_notMem_tsupport hr.2, chartFrame, map_zero]
    exact (contMDiffWithinAt_inter (hN.mem_nhds hsupport)).mp (hfield s ⟨hs, hsupport⟩)

theorem exists_supportedChartTest_at {C U : Set ℝ}
    (hU : IsOpen U) (hCU : C ⊆ U) (α : ℝ → M)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    {s : ℝ} (hs : s ∈ C) (W : TangentSpace (𝓡 n) (α s)) :
    ∃ x : M, ∃ η : ℝ → EuclideanSpace ℝ (Fin n), ContDiff ℝ ∞ η ∧
      (∀ r ∈ C, r ∈ tsupport η →
        α r ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) ∧
      chartFrame x (η s) (α s) = W := by
  let x := α s
  let N := U ∩ α ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  have hN : IsOpen N := hα.continuousOn.isOpen_inter_preimage hU
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  have hsN : s ∈ N := ⟨hCU hs, mem_chart_source _ _⟩
  obtain ⟨ζ, hζs, _, hζ, _, hζone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hN.mem_nhds hsN)
  let w := (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
    (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) W)).2
  refine ⟨x, fun r ↦ ζ r • w, hζ.smul contDiff_const, ?_, ?_⟩
  · intro r hr hsupport
    exact (hζs (tsupport_smul_subset_left ζ (fun _ ↦ w) hsupport)).2
  · change chartFrame x (ζ s • w) (α s) = W
    rw [hζone, one_smul]
    exact chartFrame_coordinates_at (mem_chart_source _ _) W

theorem jacobiPairResidual_smul_right {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ J) (α : ℝ → M)
    {s : ℝ} (hs : s ∈ Icc a b)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (Y P DP W : TangentSpace (𝓡 n) (α s)) (c : ℝ) :
    jacobiPairResidual F T α (Icc a b) s Y P DP (c • W) =
      c * jacobiPairResidual F T α (Icc a b) s Y P DP W := by
  let x := α s
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let coord := fun V : TangentSpace (𝓡 n) (α s) ↦
    (e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) V)).2
  have hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := mem_chart_source _ _
  have hframe (V : TangentSpace (𝓡 n) (α s)) : chartFrame x (coord V) (α s) = V :=
    chartFrame_coordinates_at hx V
  have hleft := jacobiPairResidual_chart F hM04 T hab htime x α hs hx hα
    (coord Y) (coord P) (coord DP) (c • coord W)
  have hright := jacobiPairResidual_chart F hM04 T hab htime x α hs hx hα
    (coord Y) (coord P) (coord DP) (coord W)
  simp only [show chartFrame x (c • coord W) (α s) = c • W by
    rw [chartFrame, map_smul]; exact congrArg (c • ·) (hframe W), hframe] at hleft
  simp only [hframe] at hright
  rw [hleft, hright]
  simp only [map_smul, smul_eq_mul]
  ring

theorem jacobiPairResidual_zero_right {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ r ∈ Icc a b, T - r ^ 2 ∈ J) (α : ℝ → M)
    {s : ℝ} (hs : s ∈ Icc a b)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (Y P DP : TangentSpace (𝓡 n) (α s)) :
    jacobiPairResidual F T α (Icc a b) s Y P DP 0 = 0 := by
  simpa only [zero_smul, zero_mul] using
    jacobiPairResidual_smul_right F hM04 T hab htime α hs hα Y P DP 0 0

end PoincareConjecture.M08

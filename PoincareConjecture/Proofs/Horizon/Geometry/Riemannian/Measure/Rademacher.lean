import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.Lipschitz

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem ae_mDifferentiableAt_of_locally_lipschitz
    (g : RiemannianMetric n M) {f : M → ℝ}
    (hlocal : ∀ a : M, ∃ O : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ (chartAt (EuclideanSpace ℝ (Fin n)) a) a ∈ O ∧
      O ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C
        (f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) a).symm) O) :
    ∀ᵐ x ∂g.volumeMeasure, MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x := by
  classical
  choose O hO haO hOs C hC using hlocal
  let U : M → Set M := fun a =>
    (chartAt (EuclideanSpace ℝ (Fin n)) a).source ∩
      (chartAt (EuclideanSpace ℝ (Fin n)) a) ⁻¹' O a
  have hU (a) : IsOpen (U a) :=
    (chartAt (EuclideanSpace ℝ (Fin n)) a).continuousOn.isOpen_inter_preimage
      (chartAt (EuclideanSpace ℝ (Fin n)) a).open_source (hO a)
  have hcover : (univ : Set M) ⊆ ⋃ a, U a := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_chart_source _ x, haO x⟩
  have hae (a : M) : ∀ᵐ y ∂g.volumeMeasure,
      y ∈ U a → MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f y := by
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) a).symm
    have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
    have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
    have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
    have hcoord : ∀ᵐ z ∂volume.restrict e.source,
        e z ∈ U a → MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e z) := by
      filter_upwards [ae_restrict_of_ae
        (Poincare.Analysis.WeakDerivative.ae_differentiableAt_of_lipschitzOn volume (hO a) (hC a)),
        ae_restrict_mem e.open_source.measurableSet] with z hz hzs hza
      have hzO : z ∈ O a := by
        have hh := hza.2
        change e.symm (e z) ∈ O a at hh
        rwa [e.left_inv hzs] at hh
      have hf' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (f ∘ e) (e.symm (e z)) := by
        rw [e.left_inv hzs]
        exact (hz hzO).hasFDerivAt.hasMFDerivAt.mdifferentiableAt
      apply (hf'.comp (e z) (hD.symm.mdifferentiableAt (e.map_source hzs))).congr_of_eventuallyEq
      filter_upwards [e.open_target.mem_nhds (e.map_source hzs)] with y hy
      simp only [Function.comp_apply, e.right_inv hy]
    have h := (ae_restrict_iff' e.open_target.measurableSet).mp
      (g.ae_restrict_of_ae_pullback e he hei
        (P := fun y => y ∈ U a → MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f y) hcoord)
    filter_upwards [h] with y hy hyU
    exact hy hyU.1 hyU
  obtain ⟨s, hs, hsc⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let : Countable s := hs.to_subtype
  have hall : ∀ᵐ x ∂g.volumeMeasure, ∀ i : s,
      x ∈ U i → MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x :=
    ae_all_iff.mpr (fun i => hae i)
  filter_upwards [hall] with x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hsc (mem_univ x))
  exact hx ⟨i, hi⟩ hxi

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem locally_lipschitz_coordinates_comp
    {f : M → ℝ} {F : ℝ → ℝ} (hF : LocallyLipschitz F)
    (hlocal : ∀ a : M, ∃ O : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ (chartAt (EuclideanSpace ℝ (Fin n)) a) a ∈ O ∧
      O ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C
        (f ∘ (chartAt (EuclideanSpace ℝ (Fin n)) a).symm) O) :
    ∀ a : M, ∃ O : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ (chartAt (EuclideanSpace ℝ (Fin n)) a) a ∈ O ∧
      O ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      ∃ C : ℝ≥0, LipschitzOnWith C
        ((F ∘ f) ∘ (chartAt (EuclideanSpace ℝ (Fin n)) a).symm) O := by
  intro a
  obtain ⟨O, hO, ha, hOs, C, hC⟩ := hlocal a
  let e := chartAt (EuclideanSpace ℝ (Fin n)) a
  obtain ⟨D, T, hT, hDT⟩ := hF (f (e.symm (e a)))
  have hn : (f ∘ e.symm) ⁻¹' T ∈ 𝓝 (e a) :=
    (hC.continuousOn.continuousAt (hO.mem_nhds ha)).tendsto hT
  obtain ⟨W, hW, hWo, haW⟩ := mem_nhds_iff.mp (inter_mem (hO.mem_nhds ha) hn)
  exact ⟨W, hWo, haW, (fun x hx => hOs (hW hx).1), D * C,
    hDT.comp (hC.mono (fun x hx => (hW hx).1)) (fun x hx => (hW hx).2)⟩

end PoincareConjecture

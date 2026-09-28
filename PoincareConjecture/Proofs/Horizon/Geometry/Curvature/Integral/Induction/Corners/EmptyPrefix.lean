import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.UniversalProperty
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.CompactImage










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology
namespace PoincareConjecture.RiemannianMetric

theorem openFiber_zero_volume_preimage_of_isCompact
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {f : M → Fin 0 → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, Fin 0 → ℝ) ∞ f)
    (U : Opens M)
    (hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 n) 𝓘(ℝ, Fin 0 → ℝ) f x))
    (c : Fin 0 → ℝ) {S : Set M} (hS : IsCompact S) (hSU : S ⊆ U) :
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n + 0) :=
      ⟨by simp⟩
    let := openFiberChartedSpace (m := n) hf U hreg c
    let := isManifold_openFiber (m := n) hf U hreg c
    (g.openRegularFiberMetric (m := n) (k := 0) hf U hreg c).volumeMeasure
      {z | openFiberIncl f U c z ∈ S} = g.volumeMeasure S := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n + 0) := ⟨by simp⟩
  let := openFiberChartedSpace (m := n) hf U hreg c
  let := isManifold_openFiber (m := n) hf U hreg c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric (m := n) (k := 0) hf U hreg c
  change gL.volumeMeasure (incl ⁻¹' S) = g.volumeMeasure S
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨x₀, hx₀⟩ := hne
  let z₀ : openFiber f U c := ⟨⟨x₀, hSU hx₀⟩, Subsingleton.elim _ _⟩
  let lift : M → openFiber f U c := fun x =>
    if hx : x ∈ U then ⟨⟨x, hx⟩, Subsingleton.elim _ _⟩ else z₀
  have hlift (x : M) (hx : x ∈ U) : incl (lift x) = x := by
    simp [lift, hx, incl, openFiberIncl]
  have hincl : ContMDiff (𝓡 n) (𝓡 n) ∞ incl :=
    contMDiff_openFiberIncl (m := n) hf U hreg c
  have hliftsmooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ lift U := by
    apply (contMDiffOn_into_openFiber_iff (m := n) hf c U hreg lift U.isOpen).mpr
    exact contMDiffOn_id.congr (fun x hx => hlift x hx)
  have himage : lift '' S = incl ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_preimage, hlift x (hSU hx)] using hx
    · intro hz
      refine ⟨incl z, hz, ?_⟩
      apply (isEmbedding_openFiberIncl f U c).injective
      exact hlift (incl z) (hSU hz)
  have hcompact : IsCompact (incl ⁻¹' S) := by
    rw [← himage]
    exact hS.image_of_continuousOn (hliftsmooth.continuousOn.mono hSU)
  have hinclimage : incl '' (incl ⁻¹' S) = S := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro x hx
    exact ⟨lift x, by simpa only [mem_preimage, hlift x (hSU hx)], hlift x (hSU hx)⟩
  have hnorm (z : openFiber f U c) (v : TangentSpace (𝓡 n) z) :
      gL.tangentNorm z v = g.tangentNorm (incl z) (mfderiv (𝓡 n) (𝓡 n) incl z v) :=
    g.openRegularFiberMetric_tangentNorm (m := n) (k := 0) hf U hreg c z v
  have hnormlift (x : M) (hx : x ∈ U) (v : TangentSpace (𝓡 n) x) :
      gL.tangentNorm (lift x) (mfderiv (𝓡 n) (𝓡 n) lift x v) = g.tangentNorm x v := by
    rw [hnorm]
    have hevent : incl ∘ lift =ᶠ[𝓝 x] id :=
      Filter.mem_of_superset (U.isOpen.mem_nhds hx) (fun y hy => hlift y hy)
    have hder := mfderiv_comp x (hincl.mdifferentiable (by simp) (lift x))
      ((hliftsmooth.contMDiffAt (U.isOpen.mem_nhds hx)).mdifferentiableAt (by simp))
    have hid : mfderiv (𝓡 n) (𝓡 n) (incl ∘ lift) x = ContinuousLinearMap.id ℝ _ := by
      rw [hevent.mfderiv_eq, mfderiv_id]
    have hcomp := congrArg (fun A => A v) (hder.symm.trans hid)
    change mfderiv (𝓡 n) (𝓡 n) incl (lift x) (mfderiv (𝓡 n) (𝓡 n) lift x v) = v at hcomp
    rw [hcomp]
    exact congrArg (fun z => g.tangentNorm z v) (hlift x hx)
  apply le_antisymm
  · have h := g.volumeMeasure_image_le_of_tangentNorm_le_on_compact gL U.isOpen hS hSU
      (hliftsmooth.of_le (by simp)) (by norm_num : (0 : ℝ) < 1)
      (fun x hx v => by rw [hnormlift x hx v]; simp)
    simpa only [himage, ENNReal.ofReal_one, one_pow, one_mul] using h
  · have h := gL.volumeMeasure_image_le_of_tangentNorm_le_on_compact g isOpen_univ
      hcompact (subset_univ _) (hincl.of_le (by simp)).contMDiffOn
      (by norm_num : (0 : ℝ) < 1) (fun z _ v => by rw [← hnorm]; simp)
    simpa only [hinclimage, ENNReal.ofReal_one, one_pow, one_mul] using h

theorem openFiber_zero_volume_real_preimage_of_isCompact
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {f : M → Fin 0 → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, Fin 0 → ℝ) ∞ f)
    (U : Opens M)
    (hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 n) 𝓘(ℝ, Fin 0 → ℝ) f x))
    (c : Fin 0 → ℝ) {S : Set M} (hS : IsCompact S) (hSU : S ⊆ U) :
    let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n + 0) :=
      ⟨by simp⟩
    let := openFiberChartedSpace (m := n) hf U hreg c
    let := isManifold_openFiber (m := n) hf U hreg c
    (g.openRegularFiberMetric (m := n) (k := 0) hf U hreg c).volumeMeasure.real
      {z | openFiberIncl f U c z ∈ S} = g.volumeMeasure.real S := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n + 0) := ⟨by simp⟩
  let := openFiberChartedSpace (m := n) hf U hreg c
  let := isManifold_openFiber (m := n) hf U hreg c
  exact congrArg ENNReal.toReal (g.openFiber_zero_volume_preimage_of_isCompact hf U hreg c hS hSU)

end PoincareConjecture.RiemannianMetric

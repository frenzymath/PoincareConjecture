import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.RegularChart
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set Function
open scoped Topology ContDiff Manifold





namespace Poincare.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]


theorem exists_kernel_coordinate_equiv {n : ℕ} (hn : Module.finrank ℝ E = n + 1)
    (L : E →L[ℝ] ℝ) (hL : Surjective L) :
    ∃ A : (ℝ × L.ker) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      ∀ z, A z 0 = z.1 := by
  have hdim := L.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hL, finrank_top, Module.finrank_self, hn]
    at hdim
  have hker : Module.finrank ℝ L.ker = Module.finrank ℝ (Fin n → ℝ) := by
    rw [Module.finrank_fin_fun]
    omega
  let B : L.ker ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq hker
  let A := ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr B).trans
    ((Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).trans
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (n + 1))).symm)
  refine ⟨A, ?_⟩
  intro z
  rfl


variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]


theorem exists_normalized_regular_point_chart {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : M) (c : ℝ)
    (hreg : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f a)) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))),
      a ∈ e.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, E) ∞ e.symm e.target ∧
      (∀ x ∈ e.source, e x 0 = f x - c) ∧
      e.IsImage {x | c ≤ f x} {y | 0 ≤ y 0} := by
  let L : E →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f a
  obtain ⟨e0, ha, hea, he, hei, hef, helevel⟩ :=
    exists_manifold_superlevel_chart hf a hreg
  obtain ⟨A, hA⟩ := exists_kernel_coordinate_equiv hn L hreg
  let N : (ℝ × L.ker) ≃ₜ EuclideanSpace ℝ (Fin (n + 1)) :=
    (Homeomorph.subRight (c, (0 : L.ker))).trans A.toHomeomorph
  have hN : ContDiff ℝ ∞ N := A.contDiff.comp (contDiff_id.sub contDiff_const)
  have hNi : ContDiff ℝ ∞ N.symm := A.symm.contDiff.add contDiff_const
  let e := e0.trans N.toOpenPartialHomeomorph
  have hs : e.source = e0.source := by simp [e]
  have ht : ∀ y ∈ e.target, N.symm y ∈ e0.target := by
    intro y hy
    exact hy.2
  have hfirst : ∀ x ∈ e.source, e x 0 = f x - c := by
    intro x hx
    change A (e0 x - (c, (0 : L.ker))) 0 = f x - c
    rw [hA]
    simp only [Prod.fst_sub, hef x (hs ▸ hx)]
  refine ⟨e, hs.symm ▸ ha, ?_, ?_, hfirst, ?_⟩
  · exact hN.contMDiff.comp_contMDiffOn (he.mono (fun x hx => hs ▸ hx))
  · exact hei.comp hNi.contMDiff.contMDiffOn ht
  · intro x hx
    change 0 ≤ e x 0 ↔ c ≤ f x
    rw [hfirst x hx]
    exact sub_nonneg



theorem exists_interior_superlevel_halfspace_chart {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) {f : M → ℝ}
    (hf : Continuous f) (c : ℝ) (a : M) (ha : c < f a) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))),
      a ∈ e.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, E) ∞ e.symm e.target ∧
      e.IsImage {x | c ≤ f x} {y | 0 ≤ y 0} := by
  let B : E ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hn)
  let φ := chartAt E a
  let v : EuclideanSpace ℝ (Fin (n + 1)) :=
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (n + 1))).symm
      (fun _ => 1 - B (φ a) 0)
  let N := B.toHomeomorph.trans (Homeomorph.addRight v)
  have hN : ContDiff ℝ ∞ N := B.contDiff.add contDiff_const
  have hNi : ContDiff ℝ ∞ N.symm :=
    B.symm.contDiff.comp (contDiff_id.add contDiff_const)
  let ψ := φ.trans N.toOpenPartialHomeomorph
  have hψa : a ∈ ψ.source := by simp [ψ, φ]
  have hψa0 : ψ a 0 = 1 := by
    change B (φ a) 0 + (1 - B (φ a) 0) = 1
    ring
  have hpos : IsOpen {y : EuclideanSpace ℝ (Fin (n + 1)) | 0 < y 0} :=
    isOpen_lt continuous_const (by fun_prop)
  let O := {x | c < f x} ∩ (ψ.source ∩ ψ ⁻¹' {y | 0 < y 0})
  have hO : IsOpen O := (isOpen_lt continuous_const hf).inter
    (ψ.continuousOn.isOpen_inter_preimage ψ.open_source hpos)
  let e := ψ.restrOpen O hO
  have hea : a ∈ e.source := ⟨hψa, ha, hψa, by simp [hψa0]⟩
  have hψ : ContMDiffOn 𝓘(ℝ, E)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ ψ ψ.source :=
    hN.contMDiff.comp_contMDiffOn
      ((contMDiffOn_chart (I := 𝓘(ℝ, E))).mono (fun x hx => hx.1))
  have hψi : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, E) ∞ ψ.symm ψ.target :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, E))).comp
      hNi.contMDiff.contMDiffOn (fun y hy => hy.2)
  refine ⟨e, hea, hψ.mono (fun x hx => hx.1),
    hψi.mono (fun y hy => hy.1), ?_⟩
  intro x hx
  change 0 ≤ e x 0 ↔ c ≤ f x
  exact iff_of_true (le_of_lt hx.2.2.2) (le_of_lt hx.2.1)


theorem exists_regular_superlevel_halfspace_chart {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (c : ℝ)
    (hc : ∀ x, f x = c → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x))
    (a : M) (ha : c ≤ f a) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (n + 1))),
      a ∈ e.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, E) ∞ e.symm e.target ∧
      e.IsImage {x | c ≤ f x} {y | 0 ≤ y 0} := by
  rcases ha.eq_or_lt with h | h
  · obtain ⟨e, he, hes, hei, hef, helevel⟩ :=
      exists_normalized_regular_point_chart hn hf a c (hc a h.symm)
    exact ⟨e, he, hes, hei, helevel⟩
  · exact exists_interior_superlevel_halfspace_chart hn hf.continuous c a h


end Poincare.Manifold

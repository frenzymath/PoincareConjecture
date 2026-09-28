import PoincareConjecture.Proofs.M08.ClosedChartCoefficients
import PoincareConjecture.Proofs.M09.LocalSmoothInverse










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem closedFamily_eventually_bijective_sliceDerivative {C : Set ℝ} {U : Set E}
    (hC : UniqueDiffOn ℝ C) (hU : IsOpen U) (α : E × ℝ → E)
    (hα : ContDiffOn ℝ ∞ α (U ×ˢ C)) {x₀ : E} (hx₀ : x₀ ∈ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ C) (hi : ∀ x ∈ U, α (x, t₀) = x) :
    ∀ᶠ r in 𝓝[C] t₀, Function.Bijective (fderiv ℝ (fun x => α (x, r)) x₀) := by
  let f : ℝ × E → E := fun z => α (z.2, z.1)
  have hf : ContDiffOn ℝ ∞ f (C ×ˢ U) :=
    hα.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hz => ⟨hz.2, hz.1⟩)
  let D := M08.spatialWithinFDeriv C U f
  have hd (r : ℝ) (hr : r ∈ C) :
      HasFDerivAt (fun x => α (x, r)) (D (r, x₀)) x₀ :=
    M08.hasFDerivAt_spatialWithin hU f hf hr hx₀
  have hidentity : (fun x => α (x, t₀)) =ᶠ[𝓝 x₀] id := by
    filter_upwards [hU.mem_nhds hx₀] with x hx
    exact hi x hx
  have hD₀ : D (t₀, x₀) = ContinuousLinearMap.id ℝ E := by
    have h := (hd t₀ ht₀).fderiv
    rw [hidentity.fderiv_eq, fderiv_id] at h
    exact h.symm
  have hc : ContinuousOn (fun r => D (r, x₀)) C :=
    (M08.spatialWithinFDeriv_contDiffOn hC hU f hf).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ hr => ⟨hr, hx₀⟩)
  have hDinj : Function.Injective (D (t₀, x₀)) := by
    rw [hD₀]
    exact Function.injective_id
  have hnear : ∀ᶠ r in 𝓝[C] t₀, Function.Injective (D (r, x₀)) :=
    (hc t₀ ht₀).eventually (ContinuousLinearMap.isOpen_injective.mem_nhds hDinj)
  filter_upwards [hnear, self_mem_nhdsWithin] with r hr hrC
  rw [(hd r hrC).fderiv]
  exact ⟨hr, (D (r, x₀)).toLinearMap.injective_iff_surjective.mp hr⟩





theorem closedFamily_restart_of_bijective {C : Set ℝ} {U : Set E}
    (hU : IsOpen U) (α : E × ℝ → E) (hα : ContDiffOn ℝ ∞ α (U ×ˢ C))
    {x₀ : E} (hx₀ : x₀ ∈ U) {r : ℝ} (hr : r ∈ C)
    (hbij : Function.Bijective (fderiv ℝ (fun x => α (x, r)) x₀)) :
    ∃ V : Set E, IsOpen V ∧ α (x₀, r) ∈ V ∧ ∃ β : E × ℝ → E,
      ContDiffOn ℝ ∞ β (V ×ˢ C) ∧ ∀ y ∈ V,
        β (y, r) = y ∧ ∃ x ∈ U, ∀ s : ℝ, β (y, s) = α (x, s) := by
  let f := fun x => α (x, r)
  have hf : ContDiffOn ℝ ∞ f U :=
    hα.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hx => ⟨hx, hr⟩)
  obtain ⟨e, hx, heU, he, heinv, _⟩ :=
    Proofs.M09.exists_smooth_local_inverse f U hU hf x₀ hx₀ hbij
  let β : E × ℝ → E := fun z => α (e.symm z.1, z.2)
  have hβ : ContDiffOn ℝ ∞ β (e.target ×ˢ C) :=
    hα.comp ((heinv.comp contDiffOn_fst (fun _ hz => hz.1)).prodMk contDiffOn_snd)
      (fun _ hz => ⟨heU (e.map_target hz.1), hz.2⟩)
  have hcenter : α (x₀, r) ∈ e.target := by
    have h := e.map_source hx
    rwa [he] at h
  refine ⟨e.target, e.open_target, hcenter, β, hβ, ?_⟩
  intro y hy
  refine ⟨?_, e.symm y, heU (e.map_target hy), fun _ => rfl⟩
  change f (e.symm y) = y
  rw [← he]
  exact e.right_inv hy

end PoincareConjecture.M14

import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Variation.Density
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.TimeDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {J : Set ℝ}

theorem hasDerivAt_integral_weighted_pullbackVolumeDensity_surface
    (F : RicciFlow 2 M J) {t : ℝ} (ht : t ∈ interior J)
    {u : ℝ → M → ℝ}
    (hu : ∀ s ∈ interior J, ∀ y : M,
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => u p.1 p.2) (s, y))
    (f : EuclideanSpace ℝ (Fin 2) → M) {K L : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : MeasurableSet K) (hL : IsCompact L) (hKL : K ⊆ L)
    (hf : ∀ x ∈ L, ContMDiffAt (𝓡 2) (𝓡 2) ∞ f x)
    (hi : ∀ x ∈ L, Function.Injective (mfderiv (𝓡 2) (𝓡 2) f x)) :
    HasDerivAt (fun s => ∫ x in K, u s (f x) * (F.metric s).pullbackVolumeDensity f x)
      (∫ x in K, (deriv (fun s => u s (f x)) t -
          (F.connection t).scalarCurvature (f x) * u t (f x)) *
        (F.metric t).pullbackVolumeDensity f x) t := by
  let ρ := fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
    u p.1 (f p.2) * (F.metric p.1).pullbackVolumeDensity f p.2
  let q := fun s x => fderiv ℝ ρ (s, x) (1, 0)
  have hus (s : ℝ) (hs : s ∈ interior J) (x : EuclideanSpace ℝ (Fin 2))
      (hx : x ∈ L) :
      ContDiffAt ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => u p.1 (f p.2)) (s, x) := by
    have hp : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => (p.1, f p.2)) (s, x) :=
      contMDiffAt_fst.prodMk ((hf x hx).comp (s, x) contMDiffAt_snd)
    have h := (hu s hs (f x)).comp (s, x) hp
    simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffAt
  have hsmooth (s : ℝ) (hs : s ∈ interior J) (x : EuclideanSpace ℝ (Fin 2))
      (hx : x ∈ L) : ContDiffAt ℝ ∞ ρ (s, x) :=
    (hus s hs x hx).mul (F.contDiffAt_pullbackVolumeDensity_spacetime hs (hf x hx) (hi x hx))
  have hρ (s : ℝ) (hs : s ∈ interior J) : ContinuousOn (fun x => ρ (s, x)) L := by
    intro x hx
    exact ((hsmooth s hs x hx).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hq : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => q p.1 p.2)
      (interior J ×ˢ L) := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact (((hsmooth s hs x hx).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).continuousAt.continuousWithinAt
  have hqs (s : ℝ) (hs : s ∈ interior J) : ContinuousOn (q s) L :=
    hq.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hx => ⟨hs, hx⟩)
  have hd (s : ℝ) (hs : s ∈ interior J) (x : EuclideanSpace ℝ (Fin 2))
      (hx : x ∈ L) : HasDerivAt (fun r => ρ (r, x)) (q s x) s := by
    exact ((hsmooth s hs x hx).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior t ht
  have hcl : Metric.closedBall t (r / 2) ⊆ interior J :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t (r / 2)).prod hL).exists_bound_of_continuousOn
    (hq.mono (prod_mono hcl Subset.rfl))
  have hbound : Integrable (fun _ : EuclideanSpace ℝ (Fin 2) => C)
      (volume.restrict K) := integrableOn_const
        (lt_of_le_of_lt (measure_mono hKL) hL.measure_lt_top).ne
  have hint := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => ρ (s, x)) (F' := q) (μ := volume.restrict K)
    (bound := fun _ => C)
    (Metric.closedBall_mem_nhds t (by positivity : 0 < r / 2))
    (by
      filter_upwards [isOpen_interior.mem_nhds ht] with s hs
      exact ((hρ s hs).mono hKL).aestronglyMeasurable hK)
    (((hρ t ht).integrableOn_compact hL).mono_set hKL)
    (((hqs t ht).mono hKL).aestronglyMeasurable hK)
    (by
      filter_upwards [ae_restrict_mem hK] with x hx
      intro s hs
      exact hC (s, x) ⟨hs, hKL hx⟩)
    hbound
    (by
      filter_upwards [ae_restrict_mem hK] with x hx
      intro s hs
      exact hd s (hcl hs) x (hKL hx))).2
  apply hint.congr_deriv
  apply setIntegral_congr_fun hK
  intro x hx
  have hud : HasDerivAt (fun s => u s (f x)) (deriv (fun s => u s (f x)) t) t := by
    have hslice : ContDiffAt ℝ ∞ (fun s => u s (f x)) t :=
      (hus t ht x (hKL hx)).comp t (contDiffAt_id.prodMk contDiffAt_const)
    exact (hslice.differentiableAt (by simp)).hasDerivAt
  have hp := hud.mul (F.hasDerivAt_pullbackVolumeDensity_surface ht f x (hi x (hKL hx)))
  have heq := (hd t ht x (hKL hx)).unique hp
  rw [heq]
  ring

end PoincareConjecture.RicciFlow

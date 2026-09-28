import PoincareConjecture.Proofs.M03.Existence.EuclideanCutoffNative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension









set_option autoImplicit false

open MeasureTheory Set Filter LineDeriv
open scoped Topology ENNReal SchwartzMap LineDeriv ContDiff

noncomputable section

namespace PoincareConjecture.EuclideanDerivativeNative

variable {n : ℕ}

local notation "ModelE" => EuclideanSpace ℝ (Fin n)


theorem ae_zero_of_compact_cutoffs {U : Set ModelE} (hU : IsOpen U) {w : ModelE → ℝ}
    (hzero : ∀ (η : 𝓢(ModelE, ℝ)), HasCompactSupport η → tsupport η ⊆ U →
      (fun x => η x * w x) =ᵐ[volume] 0) : w =ᵐ[volume.restrict U] 0 := by
  classical
  have hex (x : U) : ∃ η : 𝓢(ModelE, ℝ),
      HasCompactSupport η ∧ tsupport η ⊆ U ∧ η x = 1 := by
    obtain ⟨f, hfU, hfc, hfs, _, hfx⟩ :=
      exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds x.property)
    exact ⟨hfc.toSchwartzMap hfs, hfc, hfU, hfx⟩
  choose η hcompact hsub hvalue using hex
  have hcover : (⋃ x : U, Function.support (η x)) = U := by
    apply Set.Subset.antisymm
    · apply Set.iUnion_subset
      intro x
      exact (subset_tsupport (η x)).trans (hsub x)
    · intro x hx
      apply Set.mem_iUnion.mpr
      refine ⟨⟨x, hx⟩, ?_⟩
      change η ⟨x, hx⟩ x ≠ 0
      rw [hvalue]
      exact one_ne_zero
  obtain ⟨s, hsc, hscover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U => Function.support (η x)) (fun x => (η x).continuous.isOpen_support)
  have hcommon : ∀ᵐ y ∂(volume : Measure ModelE), ∀ x ∈ s, η x y * w y = 0 := by
    apply (ae_ball_iff hsc).mpr
    intro x _
    exact hzero (η x) (hcompact x) (hsub x)
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [hcommon] with y hy
  intro hyU
  have hycover : y ∈ ⋃ x ∈ s, Function.support (η x) := by
    rw [hscover, hcover]
    exact hyU
  simp only [Set.mem_iUnion] at hycover
  obtain ⟨x, hxs, hyη⟩ := hycover
  exact (mul_eq_zero.mp (hy x hxs)).resolve_left hyη

variable {iota : Type*} [Fintype iota]

theorem firstOrder_cutoff_toLp
    (a : iota → 𝓢(ModelE, ℝ)) (v : iota → ModelE)
    (η : 𝓢(ModelE, ℝ)) (hη : HasCompactSupport η) {U : Set ModelE}
    (hU : IsOpen U) (hηU : tsupport η ⊆ U) (f : ModelE → ℝ)
    (hf : ContDiffOn ℝ ∞ f U) (hfLp : MemLp f 2 (volume.restrict U))
    (hAfLp : MemLp (fun x => ∑ i, a i x * fderiv ℝ f x (v i)) 2 (volume.restrict U)) :
    (firstOrderSchwartz a v (cutoffSchwartz η hη hU hηU f hf)).toLp 2 volume =
      cutoffL2 η hU.measurableSet (hAfLp.toLp (fun x => ∑ i, a i x * fderiv ℝ f x (v i))) +
        cutoffL2 (firstOrderSchwartz a v η) hU.measurableSet (hfLp.toLp f) := by
  apply Lp.ext
  have hcommU : tsupport (firstOrderSchwartz a v η) ⊆ U :=
    (tsupport_firstOrderSchwartz_subset a v η).trans hηU
  filter_upwards [
    (firstOrderSchwartz a v (cutoffSchwartz η hη hU hηU f hf)).coeFn_toLp 2 volume,
    cutoffL2_toLp_coe η hU.measurableSet hηU hAfLp,
    cutoffL2_toLp_coe (firstOrderSchwartz a v η) hU.measurableSet hcommU hfLp,
    Lp.coeFn_add
      (cutoffL2 η hU.measurableSet (hAfLp.toLp (fun x => ∑ i, a i x * fderiv ℝ f x (v i))))
      (cutoffL2 (firstOrderSchwartz a v η) hU.measurableSet (hfLp.toLp f))]
    with x hactual hmain hcomm hadd
  rw [hactual, hadd, Pi.add_apply, hmain, hcomm,
    firstOrder_cutoffSchwartz a v η hη hU hηU f hf]
  ring


theorem local_firstOrder_cutoff_limit_zero
    (a : iota → 𝓢(ModelE, ℝ)) (v : iota → ModelE) {U : Set ModelE}
    (hU : IsOpen U) (f : ℕ → ModelE → ℝ)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) U)
    (hfLp : ∀ j, MemLp (f j) 2 (volume.restrict U))
    (hAfLp : ∀ j, MemLp (fun x => ∑ i, a i x * fderiv ℝ (f j) x (v i))
      2 (volume.restrict U))
    (w : Lp ℝ 2 (volume.restrict U))
    (hflim : Tendsto (fun j => (hfLp j).toLp (f j)) atTop (𝓝 0))
    (hAflim : Tendsto (fun j => (hAfLp j).toLp
      (fun x => ∑ i, a i x * fderiv ℝ (f j) x (v i))) atTop (𝓝 w))
    (η : 𝓢(ModelE, ℝ)) (hη : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    cutoffL2 η hU.measurableSet w = 0 := by
  let g : ℕ → 𝓢(ModelE, ℝ) := fun j => cutoffSchwartz η hη hU hηU (f j) (hf j)
  have hglim : Tendsto (fun j => (g j).toLp 2 volume) atTop (𝓝 0) :=
    (cutoffL2_tendsto_zero η hU.measurableSet hflim).congr'
      (Eventually.of_forall (fun j =>
        cutoffL2_toLp_eq_cutoffSchwartz η hη hU hηU (hf j) (hfLp j)))
  have hmain := ((cutoffL2 η hU.measurableSet).continuous.tendsto w).comp hAflim
  have hcomm := cutoffL2_tendsto_zero (firstOrderSchwartz a v η) hU.measurableSet hflim
  have hderiv : Tendsto (fun j => (firstOrderSchwartz a v (g j)).toLp 2 volume)
      atTop (𝓝 (cutoffL2 η hU.measurableSet w)) := by
    have hsum := (hmain.add hcomm).congr' (Eventually.of_forall (fun j =>
      (firstOrder_cutoff_toLp a v η hη hU hηU (f j) (hf j) (hfLp j) (hAfLp j)).symm))
    simpa only [add_zero] using hsum
  exact firstOrderSchwartz_limit_zero a v g _ hglim hderiv


theorem local_firstOrder_limit_zero
    (a : iota → 𝓢(ModelE, ℝ)) (v : iota → ModelE) {U : Set ModelE}
    (hU : IsOpen U) (f : ℕ → ModelE → ℝ)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) U)
    (hfLp : ∀ j, MemLp (f j) 2 (volume.restrict U))
    (hAfLp : ∀ j, MemLp (fun x => ∑ i, a i x * fderiv ℝ (f j) x (v i))
      2 (volume.restrict U))
    (w : Lp ℝ 2 (volume.restrict U))
    (hflim : Tendsto (fun j => (hfLp j).toLp (f j)) atTop (𝓝 0))
    (hAflim : Tendsto (fun j => (hAfLp j).toLp
      (fun x => ∑ i, a i x * fderiv ℝ (f j) x (v i))) atTop (𝓝 w)) : w = 0 := by
  apply Lp.ext
  apply (ae_zero_of_compact_cutoffs hU ?_).trans (Lp.coeFn_zero ℝ 2 (volume.restrict U)).symm
  intro η hη hηU
  have hlim := local_firstOrder_cutoff_limit_zero a v hU f hf hfLp hAfLp w
    hflim hAflim η hη hηU
  have hcoe := cutoffL2_coe η hU.measurableSet hηU w
  rw [hlim] at hcoe
  exact hcoe.symm.trans (Lp.coeFn_zero ℝ 2 (volume : Measure ModelE))

end PoincareConjecture.EuclideanDerivativeNative

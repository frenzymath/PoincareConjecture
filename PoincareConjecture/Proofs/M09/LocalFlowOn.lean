import PoincareConjecture.Proofs.M09.LocalSmoothFlow
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false

open scoped ContDiff Topology
open Set Filter Metric

namespace PoincareConjecture.Proofs.M09

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_field_extension (S : Set E) (hS : IsOpen S)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f S) (x0 : E) (hx : x0 ∈ S) :
    ∃ (g : E → F) (V : Set E), ContDiff ℝ ∞ g ∧ IsOpen V ∧ x0 ∈ V ∧
      V ⊆ S ∧ Set.EqOn g f V := by
  obtain ⟨e, he, heS⟩ := Metric.isOpen_iff.mp hS x0 hx
  let b : ContDiffBump x0 := {
    rIn := e / 4
    rOut := e / 2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith
  }
  let g : E → F := fun y ↦ b y • f y
  have hbS : tsupport b ⊆ S := by
    rw [b.tsupport_eq]
    intro y hy
    apply heS
    have hd : dist y x0 ≤ e / 2 := hy
    change dist y x0 < e
    linarith
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ S
    · exact b.contDiffAt.smul (hf.contDiffAt (hS.mem_nhds hy))
    · have hnot : y ∉ tsupport b := fun h ↦ hy (hbS h)
      have hzero : g =ᶠ[𝓝 y] fun _ ↦ (0 : F) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with z hz
        change b z • f z = 0
        simp only [hz, Pi.zero_apply, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  refine ⟨g, ball x0 (e / 4), hg, isOpen_ball, mem_ball_self (by positivity), ?_, ?_⟩
  · intro y hy
    apply heS
    have hd : dist y x0 < e / 4 := hy
    change dist y x0 < e
    linarith
  · intro y hy
    change b y • f y = f y
    rw [b.one_of_mem_closedBall (show dist y x0 ≤ b.rIn from le_of_lt hy), one_smul]

theorem exists_local_smooth_flow_on (S : Set E) (hS : IsOpen S)
    (f : E → E) (hf : ContDiffOn ℝ ∞ f S) (x0 : E) (hx : x0 ∈ S) :
    ∃ (alpha : E × ℝ → E) (V : Set E) (d : ℝ),
      IsOpen V ∧ x0 ∈ V ∧ V ⊆ S ∧ 0 < d ∧
      ContDiffOn ℝ ∞ alpha (V ×ˢ Set.Ioo (-d) d) ∧
      (∀ x ∈ V, alpha (x, 0) = x) ∧
      ∀ x ∈ V, ∀ t ∈ Set.Ioo (-d) d,
        alpha (x, t) ∈ S ∧ HasDerivAt (fun a ↦ alpha (x, a)) (f (alpha (x, t))) t := by
  obtain ⟨g, Vg, hg, hVg, hxVg, hVgS, hgf⟩ := exists_smooth_field_extension S hS f hf x0 hx
  let gC : C(E, E) := ⟨g, hg.continuous⟩
  obtain ⟨alpha, V0, d0, hV0, hxV0, hd0, hasmooth, hainit, haode⟩ :=
    exists_local_smooth_flow gC hg x0
  let R : Set (E × ℝ) := V0 ×ˢ Set.Ioo (-d0) d0
  have hR : IsOpen R := hV0.prod isOpen_Ioo
  have hxR : (x0, (0 : ℝ)) ∈ R := ⟨hxV0, by constructor <;> linarith⟩
  have hac : ContinuousAt alpha (x0, (0 : ℝ)) :=
    (hasmooth.contDiffAt (hR.mem_nhds hxR)).continuousAt
  have hnearA : ∀ᶠ p in 𝓝 (x0, (0 : ℝ)), alpha p ∈ Vg :=
    hac.preimage_mem_nhds (hVg.mem_nhds (by simpa only [hainit x0 hxV0] using hxVg))
  have hnearX : ∀ᶠ p : E × ℝ in 𝓝 (x0, (0 : ℝ)), p.1 ∈ Vg :=
    continuousAt_fst.preimage_mem_nhds (hVg.mem_nhds hxVg)
  obtain ⟨r, hr, hrsub⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem (hR.mem_nhds hxR) (hnearX.and hnearA))
  have hsmall {x : E} {t : ℝ} (hx' : x ∈ ball x0 (r / 2))
      (ht : t ∈ Set.Ioo (-(r / 2)) (r / 2)) :
      (x, t) ∈ R ∧ x ∈ Vg ∧ alpha (x, t) ∈ Vg := by
    apply hrsub
    change dist (x, t) (x0, (0 : ℝ)) < r
    rw [Prod.dist_eq, Real.dist_eq, sub_zero]
    have hxd : dist x x0 < r / 2 := hx'
    have htd := abs_lt.mpr ht
    exact max_lt (by linarith) (by linarith)
  have hzero : (0 : ℝ) ∈ Set.Ioo (-(r / 2)) (r / 2) := by constructor <;> linarith
  refine ⟨alpha, ball x0 (r / 2), r / 2, isOpen_ball,
    mem_ball_self (by positivity), fun x hx' ↦ hVgS (hsmall hx' hzero).2.1,
    by positivity, ?_, ?_, ?_⟩
  · exact hasmooth.mono fun z hz ↦ (hsmall hz.1 hz.2).1
  · intro x hx'
    exact hainit x (hsmall hx' hzero).1.1
  · intro x hx' t ht
    have hs := hsmall hx' ht
    refine ⟨hVgS hs.2.2, ?_⟩
    have hd := haode x hs.1.1 t hs.1.2
    change HasDerivAt (fun a ↦ alpha (x, a)) (g (alpha (x, t))) t at hd
    rw [hgf hs.2.2] at hd
    exact hd

end PoincareConjecture.Proofs.M09

import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.SingularRegularLimit

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]

theorem exists_smooth_closure_extension {f : E → V} {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : ContDiffOn ℝ ∞ f U)
    (hbound : ∀ m : ℕ, ∃ B : ℝ, ∀ x ∈ U, ‖iteratedFDeriv ℝ m f x‖ ≤ B) :
    ∃ g : E → V, ContDiffOn ℝ ∞ g (closure U) ∧ EqOn f g U := by
  classical
  have hfd (m : ℕ) : FiniteDimensional ℝ (E [×m]→L[ℝ] V) := by
    induction m with
    | zero =>
      exact FiniteDimensional.of_injective
        (continuousMultilinearCurryFin0 ℝ E V).toLinearMap
        (continuousMultilinearCurryFin0 ℝ E V).injective
    | succ m ih =>
      let := ih
      exact FiniteDimensional.of_injective
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) V).toLinearMap
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) V).injective
  have hsmooth (m : ℕ) (x : E) (hx : x ∈ U) :
      ContDiffAt ℝ ∞ (iteratedFDeriv ℝ m f) x :=
    (hf.contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right (by exact_mod_cast le_top)
  have hext (m : ℕ) : ∃ J : E → E [×m]→L[ℝ] V,
      Continuous J ∧ EqOn (iteratedFDeriv ℝ m f) J U := by
    let := hfd m
    obtain ⟨B, hB⟩ := hbound (m + 1)
    have hlip : LipschitzOnWith ⟨max B 0, le_max_right _ _⟩
        (iteratedFDeriv ℝ m f) U := by
      apply hconv.lipschitzOnWith_of_nnnorm_fderiv_le
        (fun x hx => (hsmooth m x hx).differentiableAt (by simp))
      intro x hx
      change ‖fderiv ℝ (iteratedFDeriv ℝ m f) x‖ ≤ max B 0
      rw [norm_fderiv_iteratedFDeriv]
      exact (hB x hx).trans (le_max_left _ _)
    obtain ⟨J, hJ, heq⟩ := hlip.extend_finite_dimension
    exact ⟨J, hJ.continuous, heq⟩
  choose J hJ hJeq using hext
  have hderiv (m : ℕ) (x : E) (hx : x ∈ U) :
      HasFDerivAt (J m) (J (m + 1) x).curryLeft x := by
    have heq : J m =ᶠ[𝓝 x] iteratedFDeriv ℝ m f :=
      (hJeq m).symm.eventuallyEq_of_mem (hU.mem_nhds hx)
    rw [← hJeq (m + 1) hx]
    have hd := ((hsmooth m x hx).differentiableAt (by simp)).hasFDerivAt
    rw [fderiv_iteratedFDeriv] at hd
    exact hd.congr_of_eventuallyEq heq
  let g : E → V := fun x => (J 0 x).curry0
  have hseries : HasFTaylorSeriesUpToOn (∞ : ℕ∞ω) g (fun x m => J m x) (closure U) := by
    refine ⟨fun _ _ => rfl, ?_, fun m _ => (hJ m).continuousOn⟩
    intro m _ x _hx
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hderiv m y hy).differentiableAt.differentiableWithinAt)
      hconv hU (fun y _ => (hJ m).continuousAt.continuousWithinAt)
    have hc : Continuous (fun y => (J (m + 1) y).curryLeft) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) V).continuous.comp
        (hJ (m + 1))
    apply hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hderiv m y hy).fderiv.symm
  refine ⟨g, hseries.contDiffOn, ?_⟩
  intro x hx
  change f x = (J 0 x).curry0
  rw [← hJeq 0 hx]
  rfl

theorem contDiffOn_terminal_extension_of_jet_bounds
    {f : ℝ × E → V} {fT : E → V} {s T : ℝ} {U : Set E}
    (hsT : s < T) (hU : IsOpen U) (hconv : Convex ℝ U)
    (hf : ContDiffOn ℝ ∞ f (Ioo s T ×ˢ U))
    (hbound : ∀ m : ℕ, ∃ B : ℝ,
      ∀ p ∈ Ioo s T ×ˢ U, ‖iteratedFDeriv ℝ m f p‖ ≤ B)
    (hlimit : ∀ x ∈ U, Tendsto (fun t => f (t, x)) (𝓝[<] T) (𝓝 (fT x))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => if p.1 = T then fT p.2 else f p)
      (Ioc s T ×ˢ U) := by
  classical
  obtain ⟨g, hg, heq⟩ := exists_smooth_closure_extension
    (isOpen_Ioo.prod hU) ((convex_Ioo s T).prod hconv) hf hbound
  have hsub : Ioc s T ×ˢ U ⊆ closure (Ioo s T ×ˢ U) := by
    rw [closure_prod_eq, closure_Ioo hsT.ne]
    exact fun _ hp => ⟨⟨hp.1.1.le, hp.1.2⟩, subset_closure hp.2⟩
  have hterminal (x : E) (hx : x ∈ U) : g (T, x) = fT x := by
    have htail : ∀ᶠ t in 𝓝[<] T, t ∈ Ioo s T :=
      Ioo_mem_nhdsLT hsT
    have hp : Tendsto (fun t : ℝ => (t, x)) (𝓝[<] T)
        (𝓝[closure (Ioo s T ×ˢ U)] (T, x)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        _ ((tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds tendsto_const_nhds)
      filter_upwards [htail] with t ht
      exact subset_closure ⟨ht, hx⟩
    have hglimit : Tendsto (fun t => g (t, x)) (𝓝[<] T) (𝓝 (g (T, x))) :=
      (hg.continuousOn (T, x) (hsub ⟨⟨hsT, le_rfl⟩, hx⟩)).tendsto.comp hp
    have hfeq : (fun t => g (t, x)) =ᶠ[𝓝[<] T] (fun t => f (t, x)) := by
      filter_upwards [htail] with t ht
      exact (heq ⟨ht, hx⟩).symm
    exact tendsto_nhds_unique hglimit ((hlimit x hx).congr' hfeq.symm)
  apply (hg.mono hsub).congr
  intro p hp
  split_ifs with ht
  · subst ht
    exact (hterminal p.2 hp.2).symm
  · exact heq ⟨⟨hp.1.1, lt_of_le_of_ne hp.1.2 ht⟩, hp.2⟩

end PoincareConjecture.SingularRegularLimit

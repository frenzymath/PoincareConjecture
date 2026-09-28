import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.ODE.ExistUnique










set_option autoImplicit false

open Set
open scoped ContDiff Topology NNReal





theorem exists_periodic_scalar_curves_on_Icc {L H : ℝ}
    (hL : 0 < L) (hH : 0 < H) (X : ℝ → ℝ → ℝ)
    (hX : ContDiff ℝ 1 (Function.uncurry X))
    (hper : ∀ t, Function.Periodic (X t) L) :
    ∃ ψ : ℝ → ℝ → ℝ, (∀ x, ψ 0 x = x) ∧
      ∀ t ∈ Icc 0 H, ∀ x,
        HasDerivWithinAt (fun s => ψ s x) (X t (ψ t x)) (Icc 0 H) t := by
  classical
  let D : ℝ × ℝ → ℝ := fun z => fderiv ℝ (Function.uncurry X) z (0, 1)
  have hD : Continuous D :=
    (hX.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hderiv (t x : ℝ) : HasDerivAt (X t) (D (t, x)) x := by
    have hd := (hX.differentiable (by norm_num) (t, x)).hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))
    exact hd
  have hDper (t : ℝ) : Function.Periodic (fun x => D (t, x)) L := by
    have hd : Differentiable ℝ (X t) := fun x => (hderiv t x).differentiableAt
    simpa only [funext (fun x => (hderiv t x).deriv)] using
      (hper t).deriv_of_differentiable hd
  have hcompact : IsCompact (Icc (0 : ℝ) H ×ˢ Icc (0 : ℝ) L) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C0, hC0⟩ := hcompact.exists_bound_of_continuousOn hX.continuous.continuousOn
  obtain ⟨K0, hK0⟩ := hcompact.exists_bound_of_continuousOn hD.continuousOn
  let C : ℝ≥0 := ⟨max C0 0, le_max_right _ _⟩
  let K : ℝ≥0 := ⟨max K0 0, le_max_right _ _⟩
  have hreduce (f : ℝ → ℝ) (hf : Function.Periodic f L) (x : ℝ) :
      f x = f (toIcoMod hL 0 x) := by
    calc
      f x = f (toIcoMod hL 0 x + toIcoDiv hL 0 x • L) :=
        congrArg f (toIcoMod_add_toIcoDiv_zsmul hL 0 x).symm
      _ = f (toIcoMod hL 0 x) := hf.zsmul (toIcoDiv hL 0 x) (toIcoMod hL 0 x)
  have hbound (t : ℝ) (ht : t ∈ Icc 0 H) (x : ℝ) : ‖X t x‖ ≤ C := by
    rw [hreduce (X t) (hper t) x]
    exact (hC0 (t, toIcoMod hL 0 x)
      ⟨ht, (toIcoMod_mem_Ico' hL x).1, (toIcoMod_mem_Ico' hL x).2.le⟩).trans
        (le_max_left C0 0)
  have hDbound (t : ℝ) (ht : t ∈ Icc 0 H) (x : ℝ) : ‖D (t, x)‖ ≤ K := by
    rw [hreduce (fun y => D (t, y)) (hDper t) x]
    exact (hK0 (t, toIcoMod hL 0 x)
      ⟨ht, (toIcoMod_mem_Ico' hL x).1, (toIcoMod_mem_Ico' hL x).2.le⟩).trans
        (le_max_left K0 0)
  have hLip (t : ℝ) (ht : t ∈ Icc 0 H) : LipschitzWith K (X t) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hderiv t x).differentiableAt)
    intro x
    rw [(hderiv t x).deriv]
    exact_mod_cast hDbound t ht x
  let R : ℝ≥0 := ⟨C * H + 1, by positivity⟩
  have hex (x : ℝ) : ∃ α : ℝ → ℝ, α 0 = x ∧
      ∀ t ∈ Icc 0 H, HasDerivWithinAt α (X t (α t)) (Icc 0 H) t := by
    have hPic : IsPicardLindelof X ⟨0, ⟨le_rfl, hH.le⟩⟩ x R 0 C K := by
      refine ⟨fun t ht => (hLip t ht).lipschitzOnWith, ?_,
        fun t ht y _ => hbound t ht y, ?_⟩
      · intro y _
        exact (hX.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      · change (C : ℝ) * max (H - 0) (0 - 0) ≤ (C * H + 1 : ℝ) - 0
        rw [sub_zero, sub_self, max_eq_left hH.le, sub_zero]
        linarith
    exact hPic.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose α hα0 hα using hex
  exact ⟨fun t x => α x t, hα0, fun t ht x => hα x t ht⟩

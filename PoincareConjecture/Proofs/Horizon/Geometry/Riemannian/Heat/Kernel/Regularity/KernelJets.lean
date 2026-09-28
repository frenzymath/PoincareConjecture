import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Semigroup
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Time
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Equation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.Interior
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology InnerProductSpace BoundedContinuousFunction

namespace Poincare.Analysis.Calculus

theorem norm_iteratedFDeriv_bilinear_le_of_contDiffAt
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (m - l) g x‖ := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp (inter_mem hs ht)
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfs.mono (fun _ hy => (hv hy).1)) (hgt.mono (fun _ hy => (hv hy).2))
    hvo.uniqueDiffOn hxv (le_refl (m : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hvo hxv] using h

end Poincare.Analysis.Calculus

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary Poincare.Analysis.Dirichlet.Kernel

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

theorem hasDerivAt_heatSpectralPower_operator
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure k)
      (-heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure (k + 1) t) t :=
  Poincare.Analysis.Dirichlet.Spectral.hasDerivAt_heatPower
    (eigenbasis D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure)
    (eigenvalueNN D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure) k ht

theorem contDiffOn_heatSpectralPower_operator
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω) (k : ℕ) :
    ContDiffOn ℝ ∞
      (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure k) (Ioi 0) := by
  let P := heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure
  have hall : ∀ m : ℕ, ∀ j : ℕ, ContDiffOn ℝ m (P j) (Ioi 0) := by
    intro m
    induction m with
    | zero =>
      intro j
      simp only [Nat.cast_zero, contDiffOn_zero]
      exact fun t ht => (hasDerivAt_heatSpectralPower_operator D S j ht).continuousAt.continuousWithinAt
    | succ m ih =>
      intro j
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun t ht => (hasDerivAt_heatSpectralPower_operator D S j ht).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
      exact (ih (j + 1)).neg.congr (fun t ht => (hasDerivAt_heatSpectralPower_operator D S j ht).deriv)
  exact contDiffOn_infty.mpr (fun m => hall m k)

theorem iteratedDeriv_heatSpectralPower_operator
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (j k : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv j (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure k) t =
      (-1 : ℝ) ^ j • heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure (k + j) t := by
  let P := heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure
  change iteratedDeriv j (P k) t = (-1 : ℝ) ^ j • P (k + j) t
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv j (P k) =ᶠ[𝓝 t] fun s => (-1 : ℝ) ^ j • P (k + j) s := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact ih hs
      rw [heq.deriv_eq]
      have hd := ((hasDerivAt_heatSpectralPower_operator D S (k + j) ht).const_smul
        ((-1 : ℝ) ^ j)).deriv
      convert! hd using 1
      simp only [P, pow_succ, Nat.add_assoc, mul_smul, neg_smul, one_smul, smul_neg]

theorem norm_iteratedFDeriv_heatSpectralPower_operator_le
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (j k : ℕ) {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    ‖iteratedFDeriv ℝ j (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure k) t‖ ≤ (k + j).factorial / a ^ (k + j) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_heatSpectralPower_operator D S j k (ha.trans_le hat),
    norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact (norm_heatSpectralPower_le D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure (k + j) (ha.trans_le hat)).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos ha _)
      (pow_le_pow_left₀ ha.le hat _))

theorem inner_iteratedFDeriv_evaluationRow_coordinate
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (k j : ℕ) (t : ℝ) (ht : 0 < t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) (hxΩ : e x ∈ Ω)
    (v : Fin j → EuclideanSpace ℝ (Fin n))
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    inner ℝ
      (iteratedFDeriv ℝ j
        (fun z => evaluationRow (heatPowerContinuous D S k t ht) (e z)) x v) f =
      iteratedFDeriv ℝ j (fun z => heatPowerContinuous D S k t ht f (e z)) x v := by
  have hrow : ContDiffAt ℝ ∞
      (fun z => evaluationRow (heatPowerContinuous D S k t ht) (e z)) x :=
    contMDiffAt_iff_contDiffAt.mp
      (((contMDiffOn_evaluationRow_heatPowerContinuous D S k t ht).contMDiffAt
        (S.isOpen.mem_nhds hxΩ)).comp x (he.contMDiffAt (e.open_source.mem_nhds hx)))
  let l : Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] ℝ := innerSL ℝ f
  have h := l.iteratedFDeriv_comp_left (n := ∞) hrow (i := j) (by exact_mod_cast le_top)
  have heq : l ∘
      (fun z => evaluationRow (heatPowerContinuous D S k t ht) (e z)) =
      fun z => heatPowerContinuous D S k t ht f (e z) := by
    funext z
    simpa only [l, Function.comp_apply, innerSL_apply_apply, real_inner_comm] using
      inner_evaluationRow (heatPowerContinuous D S k t ht) (e z) f
  rw [heq] at h
  have hh := (congrArg (fun A => A v) h).symm
  change inner ℝ f
      (iteratedFDeriv ℝ j
        (fun z => evaluationRow (heatPowerContinuous D S k t ht) (e z)) x v) = _ at hh
  rw [real_inner_comm] at hh
  exact hh

theorem norm_iteratedFDeriv_evaluationRow_coordinate_le
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (k j : ℕ) (t : ℝ) (ht : 0 < t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) (hxΩ : e x ∈ Ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hscalar : ∀ f : Lp ℝ 2 (g.volumeMeasure.restrict Ω),
      ‖iteratedFDeriv ℝ j (fun z => heatPowerContinuous D S k t ht f (e z)) x‖ ≤ C * ‖f‖) :
    ‖iteratedFDeriv ℝ j
      (fun z => evaluationRow (heatPowerContinuous D S k t ht) (e z)) x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  let z := iteratedFDeriv ℝ j
    (fun z => evaluationRow (heatPowerContinuous D S k t ht) (e z)) x v
  have hpair : ‖inner ℝ z z‖ ≤ C * ‖z‖ * ∏ i, ‖v i‖ := by
    rw [inner_iteratedFDeriv_evaluationRow_coordinate D S e he k j t ht hx hxΩ v z]
    exact (ContinuousMultilinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right (hscalar z) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  rw [real_inner_self_eq_norm_sq, norm_pow, norm_norm] at hpair
  change ‖z‖ ≤ C * ∏ i, ‖v i‖
  by_cases hz : ‖z‖ = 0
  · rw [hz]
    exact mul_nonneg hC (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  · have hzpos := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
    nlinarith

theorem evaluationRow_heatPowerContinuous_add_eq_spectral
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (k : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : M) :
    evaluationRow (heatPowerContinuous D S k (s + t) (add_pos hs ht)) x =
      heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure 0 t
        (evaluationRow (heatPowerContinuous D S k s hs) x) := by
  rw [heatSpectralPower_zero_eq_heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure ht]
  apply ext_inner_right ℝ
  intro f
  rw [inner_evaluationRow, heatPowerContinuous_add_comp D S k s t hs ht]
  rw [(heatSemigroup_isSelfAdjoint D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure t.toNNReal).isSymmetric.apply_clm]
  exact (inner_evaluationRow (heatPowerContinuous D S k s hs) x _).symm

theorem heatKernelContinuousTime_eq_fixed_spectral_rows
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    {a t : ℝ} (ha : 0 < a) (hat : 2 * a < t) (x y : M) :
    heatKernelContinuousTime D S t x y =
      inner ℝ (evaluationRow (heatPowerContinuous D S 0 a ha) x)
        (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
          S.isOpen S.isCompact_closure 0 (t - 2 * a)
          (evaluationRow (heatPowerContinuous D S 0 a ha) y)) := by
  have ht : 0 < t := lt_trans (by positivity) hat
  have hta : 0 < t - a := by linarith
  have ht2a : 0 < t - 2 * a := sub_pos.mpr hat
  have hsplit : t = a + (t - a) := by ring
  rw [heatKernelContinuousTime_of_pos D S ht]
  have hk := heatKernelContinuous_add_eq_inner D S a (t - a) ha hta x y
  have hr := evaluationRow_heatPowerContinuous_add_eq_spectral D S 0 a
    (t - 2 * a) ha ht2a y
  have har : a + (t - 2 * a) = t - a := by ring
  simp only [har] at hr
  simpa only [← hsplit, hr] using hk

theorem hasDerivAt_evaluationRow_heatPowerContinuousTime
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (k : ℕ) {t : ℝ} (ht : 0 < t) (x : M) :
    HasDerivAt (fun s => evaluationRow (heatPowerContinuousTime D S k s) x)
      (-evaluationRow (heatPowerContinuousTime D S (k + 1) t) x) t := by
  let H := Lp ℝ 2 (g.volumeMeasure.restrict Ω)
  let ev : (H →L[ℝ] (M →ᵇ ℝ)) →L[ℝ] H :=
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.compL ℝ H (M →ᵇ ℝ) ℝ (BoundedContinuousFunction.evalCLM ℝ x))
  have h := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
    (F := Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] (M →ᵇ ℝ))
    (E := Lp ℝ 2 (g.volumeMeasure.restrict Ω)) t
    ev.hasFDerivAt (Boundary.hasDerivAt_heatPowerContinuousTime D S k ht)
  convert! h using 1
  exact (map_neg ev _).symm

theorem iteratedDeriv_evaluationRow_heatPowerContinuousTime
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (j k : ℕ) {t : ℝ} (ht : 0 < t) (x : M) :
    iteratedDeriv j (fun s => evaluationRow (heatPowerContinuousTime D S k s) x) t =
      (-1 : ℝ) ^ j • evaluationRow (heatPowerContinuousTime D S (k + j) t) x := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv j (fun s => evaluationRow (heatPowerContinuousTime D S k s) x)
          =ᶠ[𝓝 t] fun s => (-1 : ℝ) ^ j •
            evaluationRow (heatPowerContinuousTime D S (k + j) s) x := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact ih hs
      rw [heq.deriv_eq]
      have hd := ((hasDerivAt_evaluationRow_heatPowerContinuousTime D S (k + j) ht x).const_smul
        ((-1 : ℝ) ^ j)).deriv
      convert! hd using 1
      simp only [pow_succ, Nat.add_assoc, mul_smul, neg_smul, one_smul, smul_neg]

theorem hasDerivAt_heatPowerContinuousTime_fixed_row
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (k : ℕ) {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (x : M) :
    HasDerivAt (fun s => heatPowerContinuousTime D S k s f x)
      (-heatPowerContinuousTime D S (k + 1) t f x) t := by
  have h := Boundary.hasDerivAt_heatPowerContinuousTime D S k ht
  have hclm := (BoundedContinuousFunction.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt t
    (h.clm_apply (hasDerivAt_const t f))
  convert! hclm using 1
  simp

theorem heatKernelContinuousTime_eq_fixed_row
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    {a t : ℝ} (ha : 0 < a) (hat : a < t) (x y : M) :
    heatKernelContinuousTime D S t x y =
      heatPowerContinuousTime D S 0 (t - a)
        (evaluationRow (heatPowerContinuous D S 0 a ha) y) x := by
  rw [heatKernelContinuousTime_of_pos D S (ha.trans hat),
    Boundary.heatPowerContinuousTime_of_pos D S 0 (sub_pos.mpr hat)]
  simpa only [sub_add_cancel] using
    heatKernelContinuous_add_eq_heatPowerContinuous D S (t - a) a
      (sub_pos.mpr hat) ha x y

theorem hasDerivAt_heatKernelContinuousTime_fixed_row
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    {a t : ℝ} (ha : 0 < a) (hat : a < t) (x y : M) :
    HasDerivAt (fun s => heatKernelContinuousTime D S s x y)
      (-heatPowerContinuousTime D S 1 (t - a)
        (evaluationRow (heatPowerContinuous D S 0 a ha) y) x) t := by
  let f := evaluationRow (heatPowerContinuous D S 0 a ha) y
  have hd := hasDerivAt_heatPowerContinuousTime_fixed_row D S 0
    (sub_pos.mpr hat) f x
  have hshift : HasDerivAt (fun s => heatPowerContinuousTime D S 0 (s - a) f x)
      (-heatPowerContinuousTime D S 1 (t - a) f x) t := by
    convert! hd.scomp t ((hasDerivAt_id t).sub_const a) using 1
    simp only [one_smul]
  have heq : (fun s => heatKernelContinuousTime D S s x y) =ᶠ[𝓝 t]
      (fun s => heatPowerContinuousTime D S 0 (s - a) f x) := by
    filter_upwards [Ioi_mem_nhds hat] with s hs
    exact heatKernelContinuousTime_eq_fixed_row D S ha hs x y
  exact hshift.congr_of_eventuallyEq heq

theorem iteratedDeriv_heatPowerContinuousTime_fixed_row
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (j k : ℕ) {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (x : M) :
    iteratedDeriv j (fun s => heatPowerContinuousTime D S k s f x) t =
      (-1 : ℝ) ^ j * heatPowerContinuousTime D S (k + j) t f x := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv j (fun s => heatPowerContinuousTime D S k s f x)
          =ᶠ[𝓝 t] fun s => (-1 : ℝ) ^ j * heatPowerContinuousTime D S (k + j) s f x := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact ih hs
      rw [heq.deriv_eq]
      rw [((hasDerivAt_heatPowerContinuousTime_fixed_row D S (k + j) ht f x).const_mul
        ((-1 : ℝ) ^ j)).deriv]
      simp only [pow_succ, Nat.add_assoc]
      ring

theorem iteratedDeriv_heatKernelContinuousTime_fixed_row
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (j : ℕ) {a t : ℝ} (ha : 0 < a) (hat : a < t) (x y : M) :
    iteratedDeriv j (fun s => heatKernelContinuousTime D S s x y) t =
      (-1 : ℝ) ^ j * heatPowerContinuousTime D S j (t - a)
        (evaluationRow (heatPowerContinuous D S 0 a ha) y) x := by
  let f := evaluationRow (heatPowerContinuous D S 0 a ha) y
  have heq : (fun s => heatKernelContinuousTime D S s x y) =ᶠ[𝓝 t]
      fun s => heatPowerContinuousTime D S 0 (s - a) f x := by
    filter_upwards [Ioi_mem_nhds hat] with s hs
    exact heatKernelContinuousTime_eq_fixed_row D S ha hs x y
  rw [heq.iteratedDeriv_eq j]
  have hshift := iteratedDeriv_comp_add_const j
    (fun s => heatPowerContinuousTime D S 0 s f x) (-a)
  simp only [sub_eq_add_neg]
  rw [hshift]
  simpa only [zero_add, sub_eq_add_neg] using
    iteratedDeriv_heatPowerContinuousTime_fixed_row D S j 0 (sub_pos.mpr hat) f x

theorem iteratedDeriv_heatKernelContinuousTime_eq_iterate_laplacian
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (j : ℕ) {t : ℝ} (ht : 0 < t) (x y : M) (hx : x ∈ Ω) :
    iteratedDeriv j (fun s => heatKernelContinuousTime D S s x y) t =
      ((D.laplacian)^[j] (fun z => heatKernelContinuousTime D S t z y)) x := by
  have ha := half_pos ht
  have hat := half_lt_self ht
  have hta := sub_pos.mpr hat
  let f := evaluationRow (heatPowerContinuous D S 0 (t / 2) ha) y
  have hfun : (fun z => heatKernelContinuousTime D S t z y) =
      (heatPowerContinuous D S 0 (t - t / 2) hta f : M → ℝ) := by
    funext z
    rw [heatKernelContinuousTime_eq_fixed_row D S ha hat z y,
      heatPowerContinuousTime_of_pos D S 0 hta]
  rw [iteratedDeriv_heatKernelContinuousTime_fixed_row D S j ha hat,
    heatPowerContinuousTime_of_pos D S j hta, hfun,
    iterate_laplacian_heatPowerContinuous D S j 0 (t - t / 2) hta f hx]
  simp [f]

end PoincareConjecture.LeviCivitaData.Dirichlet

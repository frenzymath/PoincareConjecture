import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.Instances.Real

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace Poincare.Manifold

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem integralCurve_eqOn_Ioo_of_contMDiffOn
    {X : (x : M) → TangentSpace (𝓡 n) x} {U : Set M} (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% X) U)
    {α β : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hαU : ∀ t ∈ Ioo a b, α t ∈ U)
    (hα : IsMIntegralCurveOn (I := 𝓡 n) α X (Ioo a b))
    (hβ : IsMIntegralCurveOn (I := 𝓡 n) β X (Ioo a b))
    (hinit : α t₀ = β t₀) : EqOn α β (Ioo a b) := by
  let S := {t | α t = β t} ∩ Ioo a b
  suffices hsub : Ioo a b ⊆ S from fun t ht => (hsub ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := S) _
    ⟨t₀, ⟨ht₀, ⟨hinit, ht₀⟩⟩⟩
  · dsimp only [S]
    rw [inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      exact (hα.continuousWithinAt ht).continuousAt (Ioo_mem_nhds ht.1 ht.2)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      exact (hβ.continuousWithinAt ht).continuousAt (Ioo_mem_nhds ht.1 ht.2)
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    have hmem := Ioo_mem_nhds ht.2.1 ht.2.2
    have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      (hX.contMDiffAt (hU.mem_nhds (hαU t ht.2)))
      (hα.isMIntegralCurveAt hmem) (hβ.isMIntegralCurveAt hmem) ht.1
    exact (heq.and hmem).mono (fun _ hs => hs)

private theorem localFlow_comp_eventuallyEq
    {X : (x : M) → TangentSpace (𝓡 n) x}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% X) U)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {Φ : ℝ × M → M}
    (hinit : ∀ y ∈ V, Φ (0, y) = y)
    (hstays : ∀ y ∈ V, ∀ t ∈ Ioo a b, Φ (t, y) ∈ U)
    (horbit : ∀ y ∈ V, IsMIntegralCurveOn (I := 𝓡 n)
      (fun t => Φ (t, y)) X (Ioo a b))
    {y : M} (hy : y ∈ V) {t : ℝ} (ht : t ∈ Ioo a b) :
    (fun s => Φ (t, Φ (s, y))) =ᶠ[𝓝 0] (fun s => Φ (s + t, y)) := by
  obtain ⟨a', haa', ha'min⟩ := exists_between (lt_min ha ht.1)
  obtain ⟨b', hmaxb', hb'b⟩ := exists_between (max_lt hb ht.2)
  have ha'0 : a' < 0 := ha'min.trans_le (min_le_left _ _)
  have ha't : a' < t := ha'min.trans_le (min_le_right _ _)
  have hb'0 : 0 < b' := (le_max_left _ _).trans_lt hmaxb'
  have htb' : t < b' := (le_max_right _ _).trans_lt hmaxb'
  have hsub : Ioo a' b' ⊆ Ioo a b := Ioo_subset_Ioo haa'.le hb'b.le
  have hcont := (horbit y hy).isMIntegralCurveAt (Ioo_mem_nhds ha hb) |>.continuousAt
  have hnear : ∀ᶠ s in 𝓝 0, Φ (s, y) ∈ V := by
    apply hcont.preimage_mem_nhds
    rw [hinit y hy]
    exact hV.mem_nhds hy
  have hshifts : Ioo (a - a') (b - b') ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (sub_neg.mpr haa') (sub_pos.mpr hb'b)
  filter_upwards [hnear, hshifts] with s hs hsinterval
  have hshift : ∀ r ∈ Ioo a' b', r + s ∈ Ioo a b := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2, hsinterval.1, hsinterval.2]
  have hα := (horbit (Φ (s, y)) hs).mono hsub
  have hβ : IsMIntegralCurveOn (I := 𝓡 n) (fun r => Φ (r + s, y)) X (Ioo a' b') :=
    ((horbit y hy).comp_add s).mono hshift
  have heq := integralCurve_eqOn_Ioo_of_contMDiffOn hU hX ⟨ha'0, hb'0⟩
    (fun r hr => hstays (Φ (s, y)) hs r (hsub hr)) hα hβ
    (by simpa using hinit (Φ (s, y)) hs)
  simpa only [add_comm] using heq ⟨ha't, htb'⟩

theorem mfderiv_localFlow_vectorField
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {X : (x : M) → TangentSpace (𝓡 n) x}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% X) U)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    {Φ : ℝ × M → M}
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) 1 Φ (Ioo a b ×ˢ V))
    (hinit : ∀ y ∈ V, Φ (0, y) = y)
    (hstays : ∀ y ∈ V, ∀ t ∈ Ioo a b, Φ (t, y) ∈ U)
    (horbit : ∀ y ∈ V, IsMIntegralCurveOn (I := 𝓡 n)
      (fun t => Φ (t, y)) X (Ioo a b))
    {y : M} (hy : y ∈ V) {t : ℝ} (ht : t ∈ Ioo a b) :
    mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y (X y) =
      X (Φ (t, y)) := by
  have hcomp := localFlow_comp_eventuallyEq hU hV hX ha hb hinit hstays horbit hy ht
  have hzero := (horbit y hy).isMIntegralCurveAt (Ioo_mem_nhds ha hb)
  have htime := (horbit y hy).isMIntegralCurveAt (Ioo_mem_nhds ht.1 ht.2)
  have hspatial : MDifferentiableAt (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y :=
    ((hΦ.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨ht, hy⟩)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hspatial' : MDifferentiableAt (𝓡 n) (𝓡 n)
      (fun z => Φ (t, z)) (Φ (0, y)) := by
    simpa only [hinit y hy] using hspatial
  have hleft := hspatial'.hasMFDerivAt.comp 0 hzero.hasMFDerivAt
  have hright : IsMIntegralCurveAt (I := 𝓡 n) (fun s => Φ (s + t, y)) X 0 := by
    simpa only [sub_self, Function.comp_def] using htime.comp_add t
  have heq := (hleft.congr_of_eventuallyEq hcomp.symm).mfderiv.symm.trans
    hright.hasMFDerivAt.mfderiv
  have heval := congrArg (fun A => A (1 : ℝ)) heq
  change (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) (Φ (0, y)))
      ((1 : ℝ) • X (Φ (0, y))) = (1 : ℝ) • X (Φ (0 + t, y)) at heval
  simp only [one_smul] at heval
  rw [zero_add, hinit y hy] at heval
  exact heval

end Poincare.Manifold

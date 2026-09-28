import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Initial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Semigroup
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.EnergyFlow
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.SpectralAnalytic
import Mathlib.Topology.Connected.Clopen











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology InnerProductSpace BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary Poincare.Analysis.Dirichlet.Kernel

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

variable (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)

private theorem evaluationRow_add' (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : M) :
    evaluationRow (heatPowerContinuous D S 0 (s + t) (add_pos hs ht)) x =
      heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure
        t.toNNReal (evaluationRow (heatPowerContinuous D S 0 s hs) x) := by
  apply ext_inner_right ℝ
  intro f
  rw [inner_evaluationRow, heatPowerContinuous_add_comp D S 0 s t hs ht]
  rw [(heatSemigroup_isSelfAdjoint D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure t.toNNReal).isSymmetric.apply_clm]
  exact (inner_evaluationRow (heatPowerContinuous D S 0 s hs) x _).symm

private theorem row_zero_of_diag_zero {s : ℝ} (hs : 0 < s) (x : M)
    (hdiag : heatKernelContinuous D S (s + s) (add_pos hs hs) x x = 0) :
    evaluationRow (heatPowerContinuous D S 0 s hs) x = 0 := by
  have hi : inner ℝ (evaluationRow (heatPowerContinuous D S 0 s hs) x)
      (evaluationRow (heatPowerContinuous D S 0 s hs) x) = 0 := by
    rw [← heatKernelContinuous_add_eq_inner D S s s hs hs x x]
    exact hdiag
  exact inner_self_eq_zero.mp hi

theorem heatKernelContinuous_diag_pos (t : ℝ) (ht : 0 < t) (x : M) (hx : x ∈ Ω) :
    0 < heatKernelContinuous D S t ht x x := by
  by_contra hnot
  have hdiag : heatKernelContinuous D S t ht x x = 0 :=
    le_antisymm (le_of_not_gt hnot) (heatKernelContinuous_nonneg D S t ht x x)
  let a : ℕ → ℝ := fun m => t / (2 : ℝ) ^ (m + 1)
  have ha_pos : ∀ m, 0 < a m := fun m => div_pos ht (pow_pos (by norm_num) _)
  have hsplit : ∀ m, a m = a (m + 1) + a (m + 1) := by
    intro m
    dsimp [a]
    rw [show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ]
    field_simp
    ring
  have hrow : ∀ m, evaluationRow
      (heatPowerContinuous D S 0 (a m) (ha_pos m)) x = 0 := by
    intro m
    induction m with
    | zero =>
        have hs : a 0 = t / 2 := by simp [a]
        apply row_zero_of_diag_zero D S (ha_pos 0) x
        simpa [hs, add_halves] using hdiag
    | succ m ihm =>
        let r := a (m + 1)
        have hr : 0 < r := ha_pos (m + 1)
        have hfac := evaluationRow_add' D S r r hr hr x
        have hfac0 : heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
            S.isOpen S.isCompact_closure r.toNNReal
            (evaluationRow (heatPowerContinuous D S 0 r hr) x) = 0 := by
          have hsum : r + r = a m := (hsplit m).symm
          have hh : evaluationRow (heatPowerContinuous D S 0 (r + r) (add_pos hr hr)) x = 0 := by
            simpa only [hsum] using ihm
          exact hfac.symm.trans hh
        apply Poincare.Analysis.Dirichlet.Spectral.heat_injective
          (eigenbasis D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure)
          (eigenvalueNN D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure)
          r.toNNReal
        simpa only [heatSemigroup, map_zero] using hfac0
  obtain ⟨b, -, hb⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
      (S.isOpen.mem_nhds hx)
  let φ : EnergyTest D Ω :=
    ⟨b, b.contMDiff, b.hasCompactSupport, hb⟩
  have hφx : φ x = 1 := b.eq_one
  have hlim := tendsto_integral_heatKernelContinuousTime D S
    (φ := (φ : M → ℝ)) φ.smooth.continuous.continuousOn x hx
  have hpow : Tendsto (fun m : ℕ => ((1 / 2 : ℝ) ^ m)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have hc := hpow.const_mul (t / 2)
    convert hc using 1
    · ext m
      dsimp [a]
      rw [pow_succ, div_pow, one_pow]
      field_simp
    · simp
  have ha : Tendsto a atTop (𝓝[Ioi (0 : ℝ)] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha0,
      Filter.Eventually.of_forall (fun m => ha_pos m)⟩
  have hz : ∀ m, (∫ y in Ω, heatKernelContinuousTime D S (a m) x y * φ y
      ∂g.volumeMeasure) = 0 := by
    intro m
    simp only [heatKernelContinuousTime_of_pos D S (ha_pos m)]
    rw [integral_heatKernelContinuous_test D S (a m) (ha_pos m) x φ]
    rw [← inner_evaluationRow (heatPowerContinuous D S 0 (a m) (ha_pos m)) x
      (toDomainL2 D Ω (φ : H1Zero D Ω))]
    rw [hrow m, inner_zero_left]
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (φ x)) := by
    apply hlim.comp ha |>.congr'
    filter_upwards [] with m
    exact hz m
  have : (0 : ℝ) = φ x := tendsto_nhds_unique tendsto_const_nhds hzero
  linarith [hφx]

private theorem analyticAt_heatKernelContinuousTime (t₀ : ℝ) (ht₀ : 0 < t₀)
    (x y : M) :
    AnalyticAt ℝ (fun t : ℝ => heatKernelContinuousTime D S t x y) t₀ := by
  let a : ℝ := t₀ / 4
  have ha : 0 < a := by dsimp [a]; linarith
  let q₀ : ℝ := t₀ - 2 * a
  have hq₀ : 0 < q₀ := by dsimp [q₀, a]; linarith
  let v := evaluationRow (heatPowerContinuous D S 0 a ha) y
  let L : Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] ℝ :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp
      (heatPowerContinuous D S 0 a ha)
  have hspec : AnalyticOnNhd ℝ
      (fun q : ℝ => heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure 0 q v) (Ioi 0) := by
    have h := Poincare.Analysis.Dirichlet.Spectral.analyticOnNhd_heatPower_zero
      (eigenbasis D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure)
      (eigenvalueNN D Ω (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure)
    have h' := (ContinuousLinearMap.apply ℝ
      (Lp ℝ 2 (g.volumeMeasure.restrict Ω)) v).comp_analyticOnNhd h
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply, heatSpectralPower] using h'
  have hq : AnalyticAt ℝ
      (fun t : ℝ => L (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure 0 (t - 2 * a) v)) t₀ := by
    have hL : AnalyticAt ℝ
        (fun q : ℝ => L (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
          S.isOpen S.isCompact_closure 0 q v)) (t₀ - 2 * a) := by
      simpa only [Function.comp_def] using
        ((L.comp_analyticOnNhd hspec) (t₀ - 2 * a) (by simpa [q₀] using hq₀))
    have hsub : AnalyticAt ℝ (fun t : ℝ => t - 2 * a) t₀ :=
      analyticAt_id.sub (analyticAt_const)
    have hh := AnalyticAt.comp (g := fun q : ℝ =>
      L (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure 0 q v))
      (f := fun t : ℝ => t - 2 * a) hL hsub
    simpa only [Function.comp_def] using hh
  apply hq.congr
  filter_upwards [isOpen_Ioi.mem_nhds (show t₀ / 2 < t₀ by linarith [ht₀])] with t ht
  have ht' : t₀ / 2 < t := ht
  have htpos : 0 < t := lt_trans (by linarith [ht₀]) ht'
  have hqpos : 0 < t - 2 * a := by
    dsimp [a]
    linarith [ht']
  have hsa : 0 < t - a := by dsimp [a]; linarith [ht']
  have hsum₁ : (t - a) + a = t := by ring
  have hsum₂ : a + (t - 2 * a) = t - a := by ring
  calc
    L (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure 0 (t - 2 * a) v) =
        heatPowerContinuous D S 0 (t - a) hsa
          (evaluationRow (heatPowerContinuous D S 0 a ha) y) x := by
      have hcomp := heatPowerContinuous_add_comp D S 0 a (t - 2 * a) ha hqpos
      have hcomp' : heatPowerContinuous D S 0 (t - a) hsa =
          heatPowerContinuous D S 0 a ha ∘SL
            heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
              S.isOpen S.isCompact_closure (t - 2 * a).toNNReal := by
        simpa only [hsum₂] using hcomp
      dsimp [L, v]
      rw [heatSpectralPower_zero_eq_heatSemigroup D Ω
        (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure hqpos]
      simpa only [L, v, ContinuousLinearMap.comp_apply, Function.comp_apply,
        BoundedContinuousFunction.evalCLM_apply] using
        congrArg (fun A => A (evaluationRow (heatPowerContinuous D S 0 a ha) y) x)
          hcomp'.symm
    _ = heatKernelContinuous D S t htpos x y := by
      simpa only [hsum₁] using
        (heatKernelContinuous_add_eq_heatPowerContinuous D S (t - a) a hsa ha x y).symm
    _ = heatKernelContinuousTime D S t x y :=
      (heatKernelContinuousTime_of_pos D S htpos x y).symm


private theorem heatKernelContinuous_zero_of_lt (s t : ℝ) (hs : 0 < s) (hst : s < t)
    (x y : M) (hy : y ∈ Ω)
    (hzero : heatKernelContinuous D S t (by linarith) x y = 0) :
    heatKernelContinuous D S s hs x y = 0 := by
  let r : ℝ := t - s
  have hr : 0 < r := sub_pos.mpr hst
  have hsemi := heatKernelContinuous_semigroup D S s r hs hr x y
  have hzero' : heatKernelContinuous D S (s + r) (add_pos hs hr) x y = 0 := by
    convert hzero using 1 <;> simp [r]
  have hzint : (∫ z, heatKernelContinuous D S s hs x z *
      heatKernelContinuous D S r hr z y ∂(g.volumeMeasure.restrict Ω)) = 0 := by
    rw [← hsemi.2]
    exact hzero'
  have hnonneg : 0 ≤ᵐ[g.volumeMeasure.restrict Ω]
      (fun z => heatKernelContinuous D S s hs x z * heatKernelContinuous D S r hr z y) :=
    Filter.Eventually.of_forall (fun z => mul_nonneg
      (heatKernelContinuous_nonneg D S s hs x z)
      (heatKernelContinuous_nonneg D S r hr z y))
  have hzeroae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hsemi.1).mp hzint
  have hcont : ContinuousOn (fun z => heatKernelContinuous D S s hs x z *
      heatKernelContinuous D S r hr z y) Ω := by
    have h1 : Continuous (fun z : M => heatKernelContinuous D S s hs x z) := by
      simpa only [Function.comp_def, id_eq] using
        (continuous_heatKernelContinuous D S s hs).comp
          (continuous_const.prodMk (continuous_id : Continuous (id : M → M)))
    have h2 : Continuous (fun z : M => heatKernelContinuous D S r hr z y) := by
      simpa only [Function.comp_def, id_eq] using
        (continuous_heatKernelContinuous D S r hr).comp
          ((continuous_id : Continuous (id : M → M)).prodMk continuous_const)
    exact (h1.mul h2).continuousOn
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  have heq := Measure.eqOn_open_of_ae_eq hzeroae S.isOpen hcont continuousOn_const
  have hyeq := heq hy
  have hdiag : 0 < heatKernelContinuous D S r hr y y :=
    heatKernelContinuous_diag_pos D S r hr y hy
  rcases mul_eq_zero.mp hyeq with hxy | hdiag0
  · exact hxy
  · exact False.elim ((ne_of_gt hdiag) hdiag0)

private theorem heatKernelContinuous_zero_all (t : ℝ) (ht : 0 < t)
    (x y : M) (hy : y ∈ Ω)
    (hzero : heatKernelContinuous D S t ht x y = 0) :
    ∀ s (hs : 0 < s), heatKernelContinuous D S s hs x y = 0 := by
  have hanalytic : AnalyticOnNhd ℝ (fun s : ℝ => heatKernelContinuousTime D S s x y) (Ioi 0) := by
    intro s hs
    exact analyticAt_heatKernelContinuousTime D S s hs x y
  have hmid : 0 < t / 2 := half_pos ht
  have hlocal : (Ioo (t / 4) (3 * t / 4) : Set ℝ) ∈ 𝓝 (t / 2) := by
    apply isOpen_Ioo.mem_nhds
    constructor <;> linarith [ht]
  have hlocalzero : (fun s : ℝ => heatKernelContinuousTime D S s x y) =ᶠ[𝓝 (t / 2)] 0 := by
    filter_upwards [hlocal] with s hs
    have hspos : 0 < s := by linarith [hs.1]
    have hst : s < t := by linarith [hs.2]
    have hz := heatKernelContinuous_zero_of_lt D S s t hspos hst x y hy hzero
    simpa only [heatKernelContinuousTime_of_pos D S hspos, Pi.zero_apply] using hz
  have hall := hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_Ioi (show t / 2 ∈ Ioi (0 : ℝ) by exact hmid) hlocalzero
  intro s hs
  have hsall := hall (show s ∈ Ioi (0 : ℝ) by exact hs)
  simpa only [heatKernelContinuousTime_of_pos D S hs, Pi.zero_apply] using hsall

private theorem heatKernelContinuous_transitive (t : ℝ) (ht : 0 < t)
    (x y z : M) (hx : x ∈ Ω) (hy : y ∈ Ω) (hz : z ∈ Ω)
    (hxy : 0 < heatKernelContinuous D S t ht x y)
    (hyz : 0 < heatKernelContinuous D S t ht y z) :
    0 < heatKernelContinuous D S t ht x z := by
  by_contra hnot
  have hzero_t : heatKernelContinuous D S t ht x z = 0 := by
    exact le_antisymm (le_of_not_gt hnot)
      (heatKernelContinuous_nonneg D S t ht x z)
  have hzero_all := heatKernelContinuous_zero_all D S t ht x z hz hzero_t
  have hzero_2t : heatKernelContinuous D S (t + t) (add_pos ht ht) x z = 0 :=
    hzero_all (t + t) (add_pos ht ht)
  have hsemi := heatKernelContinuous_semigroup D S t t ht ht x z
  have hzint : (∫ w, heatKernelContinuous D S t ht x w *
      heatKernelContinuous D S t ht w z ∂(g.volumeMeasure.restrict Ω)) = 0 := by
    rw [← hsemi.2]
    exact hzero_2t
  have hnonneg : 0 ≤ᵐ[g.volumeMeasure.restrict Ω]
      (fun w => heatKernelContinuous D S t ht x w * heatKernelContinuous D S t ht w z) :=
    Filter.Eventually.of_forall (fun w => mul_nonneg
      (heatKernelContinuous_nonneg D S t ht x w)
      (heatKernelContinuous_nonneg D S t ht w z))
  have hzeroae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hsemi.1).mp hzint
  have hcont : ContinuousOn (fun w => heatKernelContinuous D S t ht x w *
      heatKernelContinuous D S t ht w z) Ω := by
    have h1 : Continuous (fun w : M => heatKernelContinuous D S t ht x w) := by
      simpa only [Function.comp_def, id_eq] using
        (continuous_heatKernelContinuous D S t ht).comp
          (continuous_const.prodMk (continuous_id : Continuous (id : M → M)))
    have h2 : Continuous (fun w : M => heatKernelContinuous D S t ht w z) := by
      simpa only [Function.comp_def, id_eq] using
        (continuous_heatKernelContinuous D S t ht).comp
          ((continuous_id : Continuous (id : M → M)).prodMk continuous_const)
    exact (h1.mul h2).continuousOn
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  have heq := Measure.eqOn_open_of_ae_eq hzeroae S.isOpen hcont continuousOn_const
  have hyeq := heq hy
  have hmul : heatKernelContinuous D S t ht x y *
      heatKernelContinuous D S t ht y z = 0 := hyeq
  rcases mul_eq_zero.mp hmul with hxy0 | hyz0
  · exact (ne_of_gt hxy) hxy0
  · exact (ne_of_gt hyz) hyz0

theorem heatKernelContinuous_pos (t : ℝ) (ht : 0 < t)
    (x y : M) (hx : x ∈ Ω) (hy : y ∈ Ω) :
    0 < heatKernelContinuous D S t ht x y := by
  let A : Set Ω := {q | 0 < heatKernelContinuous D S t ht x q.1}
  have hAopen : IsOpen A := by
    have hcont : Continuous (fun q : Ω => heatKernelContinuous D S t ht x q.1) := by
      simpa only [Function.comp_def, id_eq] using
        ((continuous_heatKernelContinuous D S t ht).comp
          (continuous_const.prodMk (continuous_subtype_val : Continuous (fun q : Ω => (q : M)))))
    exact isOpen_lt continuous_const hcont
  have hAclosed : IsClosed A := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_forall_mem_open]
    intro q hq
    let U : Set Ω := {w | 0 < heatKernelContinuous D S t ht q.1 w.1}
    refine ⟨U, ?_, ?_, ?_⟩
    · intro w hw hAw
      have hqx : 0 < heatKernelContinuous D S t ht q.1 w.1 := hw
      have hxy : 0 < heatKernelContinuous D S t ht x w.1 := hAw
      have hqw : 0 < heatKernelContinuous D S t ht w.1 q.1 := by
        simpa only [heatKernelContinuous_symm D S t ht q.1 w.1] using hqx
      have htrans := heatKernelContinuous_transitive D S t ht x w.1 q.1 hx w.2 q.2 hxy hqw
      have hqnot : ¬ 0 < heatKernelContinuous D S t ht x q.1 := by
        change ¬ 0 < heatKernelContinuous D S t ht x q.1 at hq
        exact hq
      exact hqnot htrans
    · have hcont : Continuous (fun w : Ω => heatKernelContinuous D S t ht q.1 w.1) := by
        simpa only [Function.comp_def, id_eq] using
          ((continuous_heatKernelContinuous D S t ht).comp
            (continuous_const.prodMk (continuous_subtype_val : Continuous (fun w : Ω => (w : M)))))
      exact isOpen_lt continuous_const hcont
    · exact heatKernelContinuous_diag_pos D S t ht q.1 q.2
  letI : PreconnectedSpace Ω := isPreconnected_iff_preconnectedSpace.mp S.isConnected.isPreconnected
  have hAeq : A = Set.univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩
    ⟨⟨x, hx⟩, heatKernelContinuous_diag_pos D S t ht x hx⟩
  have hyA : (⟨y, hy⟩ : Ω) ∈ A := by rw [hAeq]; trivial
  exact hyA

end PoincareConjecture.LeviCivitaData.Dirichlet

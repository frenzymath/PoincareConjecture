import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Diffeomorphism.Perturbation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Order.Interval.Set.Infinite

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped ContDiff Topology

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

theorem fderiv_add_mul_ne_zero_of_norm_lt
    {h b : E -> Real} {x : E} (hh : DifferentiableAt Real h x)
    (hb : DifferentiableAt Real b x) {t : Real}
    (hsmall : |t| * ‖fderiv Real b x‖ < ‖fderiv Real h x‖) :
    fderiv Real (fun y => h y + t * b y) x ≠ 0 := by
  have hd : HasFDerivAt (fun y => h y + t * b y)
      (fderiv Real h x + t • fderiv Real b x) x :=
    hh.hasFDerivAt.add (hb.hasFDerivAt.const_mul t)
  rw [hd.fderiv]
  intro heq
  have heq' : fderiv Real h x = -(t • fderiv Real b x) := eq_neg_of_add_eq_zero_left heq
  have hnorm := congrArg norm heq'
  rw [norm_neg, norm_smul, Real.norm_eq_abs] at hnorm
  linarith

theorem exists_pos_forall_fderiv_add_mul_ne_zero_on_compact
    {h b : E -> Real} (hh : ContDiff Real ∞ h) (hb : ContDiff Real ∞ b)
    {K : Set E} (hK : IsCompact K) (hregular : ∀ x ∈ K, fderiv Real h x ≠ 0) :
    ∃ δ > 0, ∀ t : Real, |t| < δ ->
      ∀ x ∈ K, fderiv Real (fun y => h y + t * b y) x ≠ 0 := by
  by_cases hne : K.Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne
      (hh.continuous_fderiv (by simp)).norm.continuousOn
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      (hb.continuous_fderiv (by simp)).continuousOn
    let C := max B 0 + 1
    have hC : 0 < C := by dsimp [C]; positivity
    have hm : 0 < ‖fderiv Real h x0‖ := norm_pos_iff.mpr (hregular x0 hx0)
    refine ⟨‖fderiv Real h x0‖ / C, div_pos hm hC, fun t ht x hx => ?_⟩
    apply fderiv_add_mul_ne_zero_of_norm_lt
      (hh.differentiable (by simp) x) (hb.differentiable (by simp) x)
    have hBx : ‖fderiv Real b x‖ ≤ C := by
      exact (hB x hx).trans ((le_max_left B 0).trans (by dsimp [C]; linarith))
    calc
      |t| * ‖fderiv Real b x‖ ≤ |t| * C := mul_le_mul_of_nonneg_left hBx (abs_nonneg t)
      _ < ‖fderiv Real h x0‖ := (lt_div_iff₀ hC).mp ht
      _ ≤ ‖fderiv Real h x‖ := hmin hx
  · exact ⟨1, zero_lt_one, fun _ _ x hx => (hne ⟨x, hx⟩).elim⟩

theorem exists_pos_forall_cutoff_translation_homeomorph [CompleteSpace E]
    {χ : E -> Real} (hχ : ContDiff Real ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ δ > 0, ∀ a : E, ‖a‖ < δ ->
      ∃ e : E ≃ₜ E,
        (∀ x, e x = x + χ x • a) ∧
        ContDiff Real ∞ e ∧ ContDiff Real ∞ e.symm ∧
        (∀ x, χ x = 1 -> e x = x + a) ∧
        (∀ x, x ∉ tsupport χ -> e x = x) := by
  obtain ⟨B, hB⟩ := hχc.isCompact.exists_bound_of_continuousOn
    (hχ.continuous_fderiv (by simp)).continuousOn
  let C := max B 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨1 / (2 * C), by positivity, fun a ha => ?_⟩
  have hs : ContDiff Real ∞ (fun x => x + χ x • a) :=
    contDiff_id.add (hχ.smul contDiff_const)
  have hclose (x : E) :
      ‖fderiv Real (fun y => y + χ y • a) x - ContinuousLinearMap.id Real E‖ ≤
        (1 / 2 : Real) := by
    by_cases hx : x ∈ tsupport χ
    · have hd := (hasFDerivAt_id x).add
        ((hχ.differentiable (by simp) x).hasFDerivAt.smul_const a)
      change HasFDerivAt (fun y => y + χ y • a)
        (ContinuousLinearMap.id Real E + (fderiv Real χ x).smulRight a) x at hd
      rw [hd.fderiv, add_sub_cancel_left, ContinuousLinearMap.norm_smulRight_apply]
      have hBx : ‖fderiv Real χ x‖ ≤ C :=
        (hB x hx).trans ((le_max_left B 0).trans (by dsimp [C]; linarith))
      have ha' : C * ‖a‖ < 1 / 2 := by
        have h := (lt_div_iff₀ (show 0 < 2 * C by positivity)).mp ha
        nlinarith
      exact (mul_le_mul_of_nonneg_right hBx (norm_nonneg a)).trans ha'.le
    · have heq : (fun y => y + χ y • a) =ᶠ[𝓝 x] id := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        simp only [Pi.zero_apply] at hy
        simp [hy]
      rw [heq.fderiv_eq, fderiv_id, sub_self, norm_zero]
      norm_num
  obtain ⟨e, he, hes, hei⟩ :=
    Poincare.Analysis.Calculus.exists_smooth_homeomorph_of_fderiv_close_id hs
      (by norm_num : (1 / 2 : NNReal) < 1) (by simpa using hclose)
  refine ⟨e, fun x => congrFun he x, hes, hei, ?_, ?_⟩
  · intro x hx
    simp [he, hx]
  · intro x hx
    simp [he, image_eq_zero_of_notMem_tsupport hx]

theorem exists_bump_preserving_critical_points [FiniteDimensional Real E]
    {h : E -> Real} (hh : ContDiff Real ∞ h) (p : E)
    {r R : Real} (hr : 0 < r) (hrR : r < R)
    (hregular : ∀ x ∈ closedBall p R \ ball p r, fderiv Real h x ≠ 0) :
    ∃ χ : E -> Real, ContDiff Real ∞ χ ∧ HasCompactSupport χ ∧
      EqOn χ 1 (closedBall p r) ∧ tsupport χ ⊆ closedBall p R ∧
      ∃ δ > 0, ∀ t : Real, |t| < δ ->
        (∀ x, fderiv Real (fun y => h y + t * χ y) x = 0 ↔
          fderiv Real h x = 0) ∧
        EqOn (fun x => h x + t * χ x) (fun x => h x + t) (closedBall p r) ∧
        EqOn (fun x => h x + t * χ x) h (closedBall p R)ᶜ := by
  let χ : ContDiffBump p := ⟨r, R, hr, hrR⟩
  obtain ⟨δ, hδ, hδregular⟩ := exists_pos_forall_fderiv_add_mul_ne_zero_on_compact
    hh χ.contDiff ((isCompact_closedBall p R).diff isOpen_ball) hregular
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_, ?_, δ, hδ, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · intro x hx
    exact χ.one_of_mem_closedBall hx
  · rw [χ.tsupport_eq]
  · intro x
    by_cases hx : x ∈ ball p r
    · have heq : (fun y => h y + t * χ y) =ᶠ[𝓝 x] (fun y => h y + t) := by
        filter_upwards [χ.eventuallyEq_one_of_mem_ball hx] with y hy
        simp only [Pi.one_apply] at hy
        simp [hy]
      rw [heq.fderiv_eq, fderiv_add_const]
    · by_cases hxR : x ∈ closedBall p R
      · exact iff_of_false (hδregular t ht x ⟨hxR, hx⟩) (hregular x ⟨hxR, hx⟩)
      · have hxχ : x ∉ tsupport χ := by rwa [χ.tsupport_eq]
        have heq : (fun y => h y + t * χ y) =ᶠ[𝓝 x] h := by
          filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
          simp only [Pi.zero_apply] at hy
          simp [hy]
        rw [heq.fderiv_eq]
  · intro x hx
    simp [χ.one_of_mem_closedBall hx]
  · intro x hx
    have hxχ : x ∉ tsupport χ := by rwa [χ.tsupport_eq]
    simp [image_eq_zero_of_notMem_tsupport hxχ]

theorem exists_bump_shift_avoiding_finite_heights [FiniteDimensional Real E]
    {h : E -> Real} (hh : ContDiff Real ∞ h) (p : E)
    {r R ε : Real} (hr : 0 < r) (hrR : r < R) (hε : 0 < ε)
    (hregular : ∀ x ∈ closedBall p R \ ball p r, fderiv Real h x ≠ 0)
    {A : Set Real} (hA : A.Finite) :
    ∃ (g : E -> Real) (t : Real), ContDiff Real ∞ g ∧ |t| < ε ∧
      (∀ x, fderiv Real g x = 0 ↔ fderiv Real h x = 0) ∧
      EqOn g (fun x => h x + t) (closedBall p r) ∧
      EqOn g h (closedBall p R)ᶜ ∧ g p ∉ A := by
  obtain ⟨χ, hχ, _, _, _, δ, hδ, hshift⟩ :=
    exists_bump_preserving_critical_points hh p hr hrR hregular
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  obtain ⟨t, ht, htA⟩ := (Ioo_infinite (show -η < η by linarith)).exists_notMem_finite
    (hA.image (fun a => a - h p))
  have htη : |t| < η := abs_lt.mpr ht
  obtain ⟨hcrit, hinner, houter⟩ := hshift t (htη.trans_le (min_le_right _ _))
  refine ⟨fun x => h x + t * χ x, t, hh.add (contDiff_const.mul hχ),
    htη.trans_le (min_le_left _ _), hcrit, hinner, houter, ?_⟩
  rw [hinner (mem_closedBall_self hr.le)]
  intro ha
  apply htA
  exact ⟨h p + t, ha, by ring⟩

theorem exists_ambient_graph_cutoff [FiniteDimensional Real E]
    {h b : E -> Real} (hh : Continuous h) (hb : ContDiff Real ∞ b)
    (hbc : HasCompactSupport b) :
    ∃ χ : E × Real -> Real, ContDiff Real ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, χ (x, h x) = b x) ∧
      ∀ x z, x ∉ tsupport b -> χ (x, z) = 0 := by
  obtain ⟨B, hB⟩ := hbc.isCompact.exists_bound_of_continuousOn hh.continuousOn
  let M := max B 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let ρ : ContDiffBump (0 : Real) := ⟨M, M + 1, hM, lt_add_one M⟩
  let χ : E × Real -> Real := fun z => b z.1 * ρ z.2
  have hχ : ContDiff Real ∞ χ := (hb.comp contDiff_fst).mul (ρ.contDiff.comp contDiff_snd)
  have hχc : HasCompactSupport χ := by
    apply HasCompactSupport.of_support_subset_isCompact
      (hbc.isCompact.prod ρ.hasCompactSupport.isCompact)
    rintro ⟨x, z⟩ hxz
    constructor
    · by_contra hx
      exact hxz (by simp [χ, image_eq_zero_of_notMem_tsupport hx])
    · by_contra hz
      exact hxz (by simp [χ, image_eq_zero_of_notMem_tsupport hz])
  refine ⟨χ, hχ, hχc, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport b
    · have hxM : h x ∈ closedBall (0 : Real) M := by
        rw [mem_closedBall, dist_zero_right]
        exact (hB x hx).trans ((le_max_left B 0).trans (by dsimp [M]; linarith))
      simp [χ, ρ.one_of_mem_closedBall hxM]
    · simp [χ, image_eq_zero_of_notMem_tsupport hx]
  · intro x z hx
    simp [χ, image_eq_zero_of_notMem_tsupport hx]

theorem exists_ambient_graph_shift_avoiding_finite_heights [FiniteDimensional Real E]
    {h : E -> Real} (hh : ContDiff Real ∞ h) (p : E)
    {r R ε : Real} (hr : 0 < r) (hrR : r < R) (hε : 0 < ε)
    (hregular : ∀ x ∈ closedBall p R \ ball p r, fderiv Real h x ≠ 0)
    {A : Set Real} (hA : A.Finite) :
    ∃ (e : (E × Real) ≃ₜ (E × Real)) (g : E -> Real) (t : Real),
      ContDiff Real ∞ e ∧ ContDiff Real ∞ e.symm ∧
      (∃ K : Set (E × Real), IsCompact K ∧ ∀ z ∉ K, e z = z) ∧
      ContDiff Real ∞ g ∧ |t| < ε ∧
      (∀ x, e (x, h x) = (x, g x)) ∧
      (∀ x, fderiv Real g x = 0 ↔ fderiv Real h x = 0) ∧
      EqOn g (fun x => h x + t) (closedBall p r) ∧
      (∀ x z, x ∉ closedBall p R -> e (x, z) = (x, z)) ∧ g p ∉ A := by
  obtain ⟨b, hb, hbc, _, hbR, δ, hδ, hshift⟩ :=
    exists_bump_preserving_critical_points hh p hr hrR hregular
  obtain ⟨χ, hχ, hχc, hχgraph, hχzero⟩ :=
    exists_ambient_graph_cutoff hh.continuous hb hbc
  obtain ⟨α, hα, hambient⟩ := exists_pos_forall_cutoff_translation_homeomorph hχ hχc
  let η := min ε (min δ α)
  have hη : 0 < η := lt_min hε (lt_min hδ hα)
  obtain ⟨t, ht, htA⟩ := (Ioo_infinite (show -η < η by linarith)).exists_notMem_finite
    (hA.image (fun a => a - h p))
  have htη : |t| < η := abs_lt.mpr ht
  have htδ : |t| < δ := htη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htα : |t| < α := htη.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨e, he, hes, hei, _, hefix⟩ := hambient (0, t) (by simpa using htα)
  obtain ⟨hcrit, hinner, _⟩ := hshift t htδ
  refine ⟨e, fun x => h x + t * b x, t, hes, hei,
    ⟨tsupport χ, hχc.isCompact, hefix⟩, hh.add (contDiff_const.mul hb),
    htη.trans_le (min_le_left _ _), ?_, hcrit, hinner, ?_, ?_⟩
  · intro x
    rw [he, hχgraph]
    simp [mul_comm]
  · intro x z hx
    rw [he, hχzero x z (fun h => hx (hbR h))]
    simp
  · rw [hinner (mem_closedBall_self hr.le)]
    intro ha
    exact htA ⟨h p + t, ha, by ring⟩

theorem exists_ambient_graph_shift_of_finite_critical_points [FiniteDimensional Real E]
    {h : E -> Real} (hh : ContDiff Real ∞ h)
    (hfinite : {x | fderiv Real h x = 0}.Finite)
    {p : E} (_hp : fderiv Real h p = 0) {U : Set E} (hU : IsOpen U) (hpU : p ∈ U)
    {ε : Real} (hε : 0 < ε) {A : Set Real} (hA : A.Finite) :
    ∃ (e : (E × Real) ≃ₜ (E × Real)) (g : E -> Real),
      ContDiff Real ∞ e ∧ ContDiff Real ∞ e.symm ∧
      (∃ K : Set (E × Real), IsCompact K ∧ ∀ z ∉ K, e z = z) ∧
      ContDiff Real ∞ g ∧
      (∀ x, e (x, h x) = (x, g x)) ∧
      (∀ x, fderiv Real g x = 0 ↔ fderiv Real h x = 0) ∧
      (∀ x z, x ∉ U -> e (x, z) = (x, z)) ∧
      |g p - h p| < ε ∧ g p ∉ A ∧
      (∀ q, fderiv Real h q = 0 -> q ≠ p -> g q = h q) ∧
      ∀ q, fderiv Real h q = 0 ->
        g =ᶠ[𝓝 q] (fun x => h x + (g q - h q)) := by
  let C : Set E := {x | fderiv Real h x = 0}
  let V := U \ (C \ {p})
  have hV : IsOpen V := hU.sdiff hfinite.sdiff.isClosed
  have hpV : p ∈ V := ⟨hpU, by simp [C]⟩
  obtain ⟨R, hR, hRV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hpV)
  have hregular : ∀ x ∈ closedBall p R \ ball p (R / 2), fderiv Real h x ≠ 0 := by
    intro x hx hcrit
    have hxp : x ≠ p := by
      intro heq
      subst x
      exact hx.2 (mem_ball_self (half_pos hR))
    exact (hRV hx.1).2 ⟨hcrit, hxp⟩
  obtain ⟨e, g, t, hes, hei, hec, hg, ht, hegraph, hcrit, hinner, hefix, hgA⟩ :=
    exists_ambient_graph_shift_avoiding_finite_heights hh p (half_pos hR)
      (half_lt_self hR) hε hregular hA
  have hother (q : E) (hq : fderiv Real h q = 0) (hqp : q ≠ p) :
      q ∉ closedBall p R := fun hqR => (hRV hqR).2 ⟨hq, hqp⟩
  have hout (x : E) (hx : x ∉ closedBall p R) : g x = h x := by
    exact congrArg Prod.snd ((hegraph x).symm.trans (hefix x (h x) hx))
  have hgp : g p = h p + t := hinner (mem_closedBall_self (half_pos hR).le)
  refine ⟨e, g, hes, hei, hec, hg, hegraph, hcrit, ?_, ?_, hgA, ?_, ?_⟩
  · intro x z hx
    exact hefix x z (fun hxR => hx (hRV hxR).1)
  · simpa [hgp] using ht
  · exact fun q hq hqp => hout q (hother q hq hqp)
  · intro q hq
    by_cases hqp : q = p
    · subst q
      filter_upwards [closedBall_mem_nhds p (half_pos hR)] with x hx
      simpa [hgp] using hinner hx
    · have hqR := hother q hq hqp
      have hqeq := hout q hqR
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hqR] with x hx
      simpa [hqeq] using hout x hx

theorem exists_ambient_graph_distinct_critical_values [FiniteDimensional Real E]
    {h : E -> Real} (hh : ContDiff Real ∞ h)
    (hfinite : {x | fderiv Real h x = 0}.Finite)
    {ε : Real} (hε : 0 < ε) :
    ∃ (e : (E × Real) ≃ₜ (E × Real)) (g : E -> Real),
      ContDiff Real ∞ e ∧ ContDiff Real ∞ e.symm ∧
      (∃ K : Set (E × Real), IsCompact K ∧ ∀ z ∉ K, e z = z) ∧
      ContDiff Real ∞ g ∧
      (∀ x, e (x, h x) = (x, g x)) ∧
      (∀ x, fderiv Real g x = 0 ↔ fderiv Real h x = 0) ∧
      InjOn g {x | fderiv Real h x = 0} ∧
      (∀ q, fderiv Real h q = 0 -> |g q - h q| < ε) ∧
      ∀ q, fderiv Real h q = 0 ->
        g =ᶠ[𝓝 q] (fun x => h x + (g q - h q)) := by
  classical
  let C : Set E := {x | fderiv Real h x = 0}
  have haux : ∀ S : Set E, S.Finite -> S ⊆ C ->
      ∃ (e : (E × Real) ≃ₜ (E × Real)) (g : E -> Real),
        ContDiff Real ∞ e ∧ ContDiff Real ∞ e.symm ∧
        (∃ K : Set (E × Real), IsCompact K ∧ ∀ z ∉ K, e z = z) ∧
        ContDiff Real ∞ g ∧
        (∀ x, e (x, h x) = (x, g x)) ∧
        (∀ x, fderiv Real g x = 0 ↔ fderiv Real h x = 0) ∧
        InjOn g S ∧ (∀ q ∈ C, |g q - h q| < ε) ∧
        (∀ q ∈ C, q ∉ S -> g q = h q) ∧
        ∀ q ∈ C, g =ᶠ[𝓝 q] (fun x => h x + (g q - h q)) := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty =>
      intro _
      refine ⟨Homeomorph.refl _, h, contDiff_id, contDiff_id,
        ⟨∅, isCompact_empty, fun _ _ => rfl⟩, hh, fun _ => rfl,
        fun _ => Iff.rfl, injOn_empty _, ?_, fun _ _ _ => rfl, ?_⟩
      · intro q _
        simpa using hε
      · intro q _
        exact Eventually.of_forall (by simp)
    | @insert p S hpS hS ih =>
      intro hSC
      have hpC : p ∈ C := hSC (mem_insert p S)
      have hSC' : S ⊆ C := (subset_insert p S).trans hSC
      obtain ⟨e, g, hes, hei, hec, hg, hegraph, hcrit, hginj, hsmall, hfixed, hgerm⟩ :=
        ih hSC'
      have hfiniteg : {x | fderiv Real g x = 0}.Finite := by
        have heq : {x | fderiv Real g x = 0} = C := by
          ext x
          exact hcrit x
        rw [heq]
        exact hfinite
      obtain ⟨d, k, hds, hdi, hdc, hk, hdgraph, hkcrit, _, hkp, hkA, hkfixed, hkgerm⟩ :=
        exists_ambient_graph_shift_of_finite_critical_points hg hfiniteg
          ((hcrit p).mpr hpC) isOpen_univ (mem_univ p) hε (hS.image g)
      have hkg (q : E) (hq : q ∈ C) (hqp : q ≠ p) : k q = g q :=
        hkfixed q ((hcrit q).mpr hq) hqp
      have hkgS (q : E) (hq : q ∈ S) : k q = g q :=
        hkg q (hSC' hq) (fun heq => hpS (heq ▸ hq))
      refine ⟨e.trans d, k, hds.comp hes, hei.comp hdi, ?_, hk, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · obtain ⟨K, hK, heK⟩ := hec
        obtain ⟨L, hL, hdL⟩ := hdc
        refine ⟨K ∪ L, hK.union hL, fun z hz => ?_⟩
        change d (e z) = z
        rw [heK z (fun hzK => hz (Or.inl hzK)), hdL z (fun hzL => hz (Or.inr hzL))]
      · intro x
        change d (e (x, h x)) = _
        rw [hegraph, hdgraph]
      · intro x
        exact (hkcrit x).trans (hcrit x)
      · apply (injOn_insert hpS).mpr
        constructor
        · intro x hx y hy heq
          exact hginj hx hy (by simpa only [hkgS x hx, hkgS y hy] using heq)
        · rintro ⟨q, hq, heq⟩
          exact hkA ⟨q, hq, (hkgS q hq).symm.trans heq⟩
      · intro q hq
        by_cases hqp : q = p
        · subst q
          simpa only [hfixed p hpC hpS] using hkp
        · simpa only [hkg q hq hqp] using hsmall q hq
      · intro q hq hqS
        have hqp : q ≠ p := fun heq => hqS (Or.inl heq)
        exact (hkg q hq hqp).trans (hfixed q hq (fun hqS' => hqS (Or.inr hqS')))
      · intro q hq
        filter_upwards [hkgerm q ((hcrit q).mpr hq), hgerm q hq] with x hx hx'
        rw [hx, hx']
        ring
  obtain ⟨e, g, hes, hei, hec, hg, hegraph, hcrit, hginj, hsmall, _, hgerm⟩ :=
    haux C hfinite subset_rfl
  exact ⟨e, g, hes, hei, hec, hg, hegraph, hcrit, hginj, hsmall, hgerm⟩

end Poincare.Manifold.Schoenflies

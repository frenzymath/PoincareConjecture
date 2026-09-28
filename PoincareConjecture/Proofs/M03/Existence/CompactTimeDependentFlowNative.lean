import PoincareConjecture.Proofs.M03.Existence.SmoothManifoldLocalFlowNative
import PoincareConjecture.Proofs.M03.Existence.TimeDependentConjugatingFlowNative
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Set Filter Manifold
open scoped Topology ContDiff Bundle

noncomputable section

namespace PoincareConjecture.CompactTimeDependentFlowNative

section CompactGluing

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N] [T2Space N]

theorem exists_contDiff_local_flow_on_compact {k : ℕ∞} (hk : k ≠ 0)
    (V : (x : N) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) k
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) N)))
    {K : Set N} (hK : IsCompact K) :
    ∃ U : Set N, IsOpen U ∧ K ⊆ U ∧ ∃ ε > 0, ∃ α : N × ℝ → N,
      (∀ x ∈ U, α (x, 0) = x) ∧
      (∀ x ∈ U, IsMIntegralCurveOn (fun t => α (x, t)) V (Ioo (-ε) ε)) ∧
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) k α
        (U ×ˢ Ioo (-ε) ε) := by
  classical
  choose A hAo hA τ hτ f hf0 hf hfsm using
    SmoothManifoldLocalFlowNative.exists_contDiff_local_flow hk V hV
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover A hAo
    (fun x _ => mem_iUnion.mpr ⟨x, hA x⟩)
  obtain ⟨ε, hε, hbound⟩ := exists_common_positive_time s τ (fun i _ => hτ i)
  let U : Set N := ⋃ i ∈ s, A i
  have hUo : IsOpen U := isOpen_iUnion (fun i => isOpen_iUnion (fun _ => hAo i))
  have hrep (x : N) (hx : x ∈ U) : ∃ i, i ∈ s ∧ x ∈ A i := by
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact ⟨i, hi, hxi⟩
  let α : N × ℝ → N := fun q =>
    if hx : q.1 ∈ U then f (hrep q.1 hx).choose q else q.1
  have hwindow (i : N) (hi : i ∈ s) : Ioo (-ε) ε ⊆ Ioo (-τ i) (τ i) :=
    Ioo_subset_Ioo (neg_le_neg (hbound i hi)) (hbound i hi)
  have hV1 : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) N)) :=
    hV.of_le (by exact_mod_cast (Order.one_le_iff_ne_zero.mpr hk : (1 : ℕ∞) ≤ k))
  have hagree (i : N) (hi : i ∈ s) (x : N) (hx : x ∈ A i) :
      EqOn (fun t => α (x, t)) (fun t => f i (x, t)) (Ioo (-ε) ε) := by
    have hxU : x ∈ U := mem_iUnion₂.mpr ⟨i, hi, hx⟩
    let j := (hrep x hxU).choose
    have hj := (hrep x hxU).choose_spec
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (t₀ := (0 : ℝ)) ⟨neg_lt_zero.mpr hε, hε⟩ hV1
      ((hf j x hj.2).mono (hwindow j hj.1)) ((hf i x hx).mono (hwindow i hi))
      ((hf0 j x hj.2).trans (hf0 i x hx).symm)
    intro t ht
    simpa only [α, dif_pos hxU, j] using heq ht
  refine ⟨U, hUo, hs, ε, hε, α, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := hrep x hx
    exact (hagree i hi x hxi ⟨neg_lt_zero.mpr hε, hε⟩).trans (hf0 i x hxi)
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := hrep x hx
    intro t ht
    have heq : (fun u => α (x, u)) =ᶠ[𝓝 t] (fun u => f i (x, u)) :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) (hagree i hi x hxi)
    have hd := ((hf i x hxi) t (hwindow i hi ht)).hasMFDerivAt
      (Ioo_mem_nhds (hwindow i hi ht).1 (hwindow i hi ht).2)
    rw [← hagree i hi x hxi ht] at hd
    exact (hd.congr_of_eventuallyEq heq).hasMFDerivWithinAt
  · intro q hq
    obtain ⟨i, hi, hqi⟩ := hrep q.1 hq.1
    have hlocal : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) k (f i)
        (A i ×ˢ Ioo (-ε) ε) :=
      (hfsm i).mono (prod_mono (Subset.refl _) (hwindow i hi))
    have hnhds : A i ×ˢ Ioo (-ε) ε ∈ 𝓝 q :=
      ((hAo i).prod isOpen_Ioo).mem_nhds ⟨hqi, hq.2⟩
    have heq : α =ᶠ[𝓝 q] f i := by
      filter_upwards [hnhds] with z hz
      exact hagree i hi z.1 hz.1 hz.2
    exact ((hlocal q ⟨hqi, hq.2⟩).contMDiffAt hnhds
      |>.congr_of_eventuallyEq heq).contMDiffWithinAt

theorem exists_smooth_local_flow_on_compact
    (V : (x : N) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) N)))
    {K : Set N} (hK : IsCompact K) :
    ∃ U : Set N, IsOpen U ∧ K ⊆ U ∧ ∃ ε > 0, ∃ α : N × ℝ → N,
      (∀ x ∈ U, α (x, 0) = x) ∧
      (∀ x ∈ U, IsMIntegralCurveOn (fun t => α (x, t)) V (Ioo (-ε) ε)) ∧
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ α
        (U ×ˢ Ioo (-ε) ε) :=
  exists_contDiff_local_flow_on_compact (by simp) V hV hK

end CompactGluing

section Inverse

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [BoundarylessManifold I N] [T2Space N]

def prependCurve (β γ : ℝ → N) : ℝ → N := fun t => if t < 0 then β t else γ t

theorem isMIntegralCurveOn_prependCurve
    {V : (x : N) → TangentSpace I x} {β γ : ℝ → N} {ε T : ℝ}
    (hε : 0 < ε) (hT : 0 < T)
    (hβ : IsMIntegralCurveOn β V (Ioo (-ε) ε))
    (hγ : IsMIntegralCurveOn γ V (Ico 0 T)) (hzero : β 0 = γ 0) :
    IsMIntegralCurveOn (prependCurve β γ) V (Ioo (-ε) T) := by
  intro t ht
  by_cases htneg : t < 0
  · have hbt : t ∈ Ioo (-ε) ε := ⟨ht.1, htneg.trans hε⟩
    have hd := (hβ t hbt).hasMFDerivAt (Ioo_mem_nhds hbt.1 hbt.2)
    have heq : prependCurve β γ =ᶠ[𝓝 t] β :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds htneg)
        (fun s hs => by simp only [prependCurve, if_pos (mem_Iio.mp hs)])
    have hvalue : prependCurve β γ t = β t := by simp only [prependCurve, if_pos htneg]
    rw [← hvalue] at hd
    exact (hd.congr_of_eventuallyEq heq).hasMFDerivWithinAt
  · by_cases htpos : 0 < t
    · have hd := (hγ t ⟨htpos.le, ht.2⟩).hasMFDerivAt
        (mem_of_superset (Ioo_mem_nhds htpos ht.2) Ioo_subset_Ico_self)
      have heq : prependCurve β γ =ᶠ[𝓝 t] γ :=
        Filter.eventuallyEq_of_mem (Ioi_mem_nhds htpos)
          (fun s hs => by simp only [prependCurve, if_neg (not_lt.mpr (mem_Ioi.mp hs).le)])
      have hvalue : prependCurve β γ t = γ t := by simp only [prependCurve, if_neg htneg]
      rw [← hvalue] at hd
      exact (hd.congr_of_eventuallyEq heq).hasMFDerivWithinAt
    · have ht0 : t = 0 := le_antisymm (not_lt.mp htpos) (not_lt.mp htneg)
      subst t
      have hvalue : prependCurve β γ 0 = γ 0 := by simp only [prependCurve, lt_self_iff_false, if_false]
      have hright : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (prependCurve β γ) (Ici 0) 0
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (prependCurve β γ 0))) := by
        rw [hvalue]
        apply ((hγ 0 ⟨le_rfl, hT⟩).mono_of_mem_nhdsWithin
          (Ico_mem_nhdsGE hT)).congr_mono
        · intro s hs
          simp only [prependCurve, if_neg (not_lt.mpr (mem_Ici.mp hs))]
        · exact hvalue
        · exact Subset.refl _
      have hleft : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (prependCurve β γ) (Iic 0) 0
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (prependCurve β γ 0))) := by
        rw [hvalue, ← hzero]
        have hd := (hβ 0 ⟨neg_lt_zero.mpr hε, hε⟩).hasMFDerivAt
          (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε)
        apply hd.hasMFDerivWithinAt.congr_mono
        · intro s hs
          by_cases hsneg : s < 0
          · simp only [prependCurve, if_pos hsneg]
          · have hs0 : s = 0 := le_antisymm hs (not_lt.mp hsneg)
            subst s
            exact hvalue.trans hzero.symm
        · exact hvalue.trans hzero.symm
        · exact Subset.refl _
      have hd : HasMFDerivAt 𝓘(ℝ, ℝ) I (prependCurve β γ) 0
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (prependCurve β γ 0))) := by
        apply hasMFDerivWithinAt_univ.mp
        simpa only [Iic_union_Ici] using hleft.union hright
      exact hd.hasMFDerivWithinAt

theorem isMIntegralCurveOn_Ico_eqOn [CompleteSpace E]
    {V : (x : N) → TangentSpace I x}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun x => (⟨x, V x⟩ : TangentBundle I N)))
    {γ γ' : ℝ → N} {T : ℝ} (hT : 0 < T)
    (hγ : IsMIntegralCurveOn γ V (Ico 0 T))
    (hγ' : IsMIntegralCurveOn γ' V (Ico 0 T)) (hzero : γ 0 = γ' 0) :
    EqOn γ γ' (Ico 0 T) := by
  obtain ⟨β, hβ0, hβ⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (0 : ℝ) (hV (γ 0))
  obtain ⟨ε, hε, hβcurve⟩ := isMIntegralCurveAt_iff'.mp hβ
  have hβIoo : IsMIntegralCurveOn β V (Ioo (-ε) ε) := by
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hβcurve
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := (0 : ℝ)) ⟨neg_lt_zero.mpr hε, hT⟩ hV
    (isMIntegralCurveOn_prependCurve hε hT hβIoo hγ hβ0)
    (isMIntegralCurveOn_prependCurve hε hT hβIoo hγ' (hβ0.trans hzero))
    (by simpa only [prependCurve, lt_self_iff_false, if_false] using hzero)
  intro t ht
  simpa only [prependCurve, if_neg (not_lt.mpr ht.1)] using
    heq ⟨(neg_lt_zero.mpr hε).trans_le ht.1, ht.2⟩

theorem local_flow_reverse
    {V : (x : N) → TangentSpace I x}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun x => (⟨x, V x⟩ : TangentBundle I N)))
    {U : Set N} {ε : ℝ} (hε : 0 < ε) {α : N × ℝ → N}
    (hzero : ∀ x ∈ U, α (x, 0) = x)
    (hcurve : ∀ x ∈ U,
      IsMIntegralCurveOn (fun t => α (x, t)) V (Ioo (-ε) ε))
    {x : N} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-(ε / 2)) (ε / 2))
    (hreturn : α (x, t) ∈ U) : α (α (x, t), -t) = x := by
  have hsmall : Ioo (-(ε / 2)) (ε / 2) ⊆ Ioo (-ε) ε :=
    Ioo_subset_Ioo (by linarith) (by linarith)
  have hshift : Ioo (-(ε / 2)) (ε / 2) ⊆ {s : ℝ | s + t ∈ Ioo (-ε) ε} := by
    intro s hs
    exact ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := (0 : ℝ)) (show 0 ∈ Ioo (-(ε / 2)) (ε / 2) by
      constructor <;> linarith) hV
    (((hcurve x hx).comp_add t).mono hshift)
    ((hcurve _ hreturn).mono hsmall)
    (by simp only [Function.comp_apply, zero_add, hzero _ hreturn])
  have hm : -t ∈ Ioo (-(ε / 2)) (ε / 2) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa only [Function.comp_apply, neg_add_cancel, hzero x hx] using (heq hm).symm

end Inverse

section SuspendedFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓡 n
local notation "J" => ModelWithCorners.prod (𝓡 n) 𝓘(ℝ, ℝ)

open TimeDependentConjugatingFlowNative.TimeDependentFlowNative

set_option backward.isDefEq.respectTransparency false in
theorem suspended_time_coordinate
    (V : SmoothTimeDependentVectorField (n := n) (M := M))
    {ε : ℝ} (hε : 0 < ε) {α : (M × ℝ) × ℝ → M × ℝ} {z : M × ℝ}
    (hzero : α (z, 0) = z)
    (hcurve : IsMIntegralCurveOn (fun s => α (z, s)) V.suspension (Ioo (-ε) ε))
    {s : ℝ} (hs : s ∈ Ioo (-ε) ε) : (α (z, s)).2 = z.2 + s := by
  have hder (t : ℝ) (ht : t ∈ Ioo (-ε) ε) :
      HasDerivAt (fun u => (α (z, u)).2) 1 t := by
    have hp := (hasMFDerivAt_snd (α (z, t))).comp t
      ((hcurve t ht).hasMFDerivAt (Ioo_mem_nhds ht.1 ht.2))
    have hD : (1 : ℝ →L[ℝ] ℝ) =
        (ContinuousLinearMap.snd ℝ (TangentSpace I (α (z, t)).1)
          (TangentSpace 𝓘(ℝ, ℝ) (α (z, t)).2)) ∘L
            ((1 : ℝ →L[ℝ] ℝ).smulRight (V.suspension (α (z, t)))) := by
      apply ContinuousLinearMap.ext
      intro r
      change r = (r • V.suspension (α (z, t))).2
      rw [V.suspension_eq, equivTangentBundleProd_symm_apply_snd]
      change r = r * (1 : ℝ)
      exact (mul_one r).symm
    change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u => (α (z, u)).2) t
      ((ContinuousLinearMap.snd ℝ (TangentSpace I (α (z, t)).1)
        (TangentSpace 𝓘(ℝ, ℝ) (α (z, t)).2)) ∘L
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V.suspension (α (z, t))))) at hp
    have hp' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u => (α (z, u)).2) t
        (1 : ℝ →L[ℝ] ℝ) := hp.congr_mfderiv hD.symm
    have hfd : HasFDerivAt (fun u : ℝ => (α (z, u)).2) (1 : ℝ →L[ℝ] ℝ) t :=
      hp'.hasFDerivAt
    simpa only [one_apply_eq_self] using hfd.hasDerivAt
  have hlinear (t : ℝ) : HasDerivAt (fun u : ℝ => z.2 + u) 1 t :=
    (hasDerivAt_id t).const_add z.2
  have heq := isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
    (fun t ht => (hder t ht).differentiableAt.differentiableWithinAt)
    (fun t _ => (hlinear t).differentiableAt.differentiableWithinAt)
    (fun t ht => (hder t ht).deriv.trans (hlinear t).deriv.symm)
    (show 0 ∈ Ioo (-ε) ε from ⟨neg_lt_zero.mpr hε, hε⟩)
    (by simp only [hzero, add_zero])
  exact heq hs

set_option backward.isDefEq.respectTransparency false in
theorem exists_smooth_suspended_local_flow [CompactSpace M]
    (V : SmoothTimeDependentVectorField (n := n) (M := M)) :
    ∃ U : Set (M × ℝ), IsOpen U ∧
      ((univ : Set M) ×ˢ Icc (-1 : ℝ) 1) ⊆ U ∧
      ∃ ε > 0, ∃ α : (M × ℝ) × ℝ → M × ℝ,
        (∀ z ∈ U, α (z, 0) = z) ∧
        (∀ z ∈ U, IsMIntegralCurveOn (fun s => α (z, s)) V.suspension (Ioo (-ε) ε)) ∧
        ContMDiffOn (ModelWithCorners.prod J 𝓘(ℝ, ℝ)) J ∞ α (U ×ˢ Ioo (-ε) ε) := by
  have hprod : IsManifold J ∞ (M × ℝ) := inferInstance
  letI : ChartedSpace (E × ℝ) (M × ℝ) := prodChartedSpace E M ℝ ℝ
  letI : IsManifold 𝓘(ℝ, E × ℝ) ∞ (M × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact hprod
  have hV : ContMDiff 𝓘(ℝ, E × ℝ)
      (𝓘(ℝ, E × ℝ).prod 𝓘(ℝ, E × ℝ)) ∞
      (fun z => (⟨z, V.suspension z⟩ : TangentBundle 𝓘(ℝ, E × ℝ) (M × ℝ))) := by
    simpa +instances only [modelWithCornersSelf_prod] using V.suspension_smooth
  obtain ⟨U, hUo, hK, ε, hε, α, hzero, hcurve, hsm⟩ :=
    exists_smooth_local_flow_on_compact V.suspension hV
      (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)))
  refine ⟨U, hUo, hK, ε, hε, α, hzero, ?_, ?_⟩
  · intro z hz
    exact hcurve z hz
  · simp_rw +instances [modelWithCornersSelf_prod] at hsm
    exact hsm

theorem suspended_spatial_derivative
    (V : SmoothTimeDependentVectorField (n := n) (M := M))
    {ε : ℝ} {α : (M × ℝ) × ℝ → M × ℝ} {z : M × ℝ}
    (hcurve : IsMIntegralCurveOn (fun s => α (z, s)) V.suspension (Ioo (-ε) ε))
    {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => (α (z, s)).1) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (α (z, t)))) := by
  have hp := (hasMFDerivAt_fst (α (z, t))).comp t
    ((hcurve t ht).hasMFDerivAt (Ioo_mem_nhds ht.1 ht.2))
  have hD : (1 : ℝ →L[ℝ] ℝ).smulRight (V (α (z, t))) =
      (ContinuousLinearMap.fst ℝ (TangentSpace I (α (z, t)).1)
        (TangentSpace 𝓘(ℝ, ℝ) (α (z, t)).2)) ∘L
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V.suspension (α (z, t)))) := by
    apply ContinuousLinearMap.ext
    intro r
    change r • V (α (z, t)) = (r • V.suspension (α (z, t))).1
    rw [V.suspension_eq, equivTangentBundleProd_symm_apply_snd]
    rfl
  rw [hD]
  exact hp

theorem exists_diffeomorph_family [CompactSpace M]
    (V : SmoothTimeDependentVectorField (n := n) (M := M)) :
    ∃ T > 0, ∃ Phi : ℝ → Diffeomorph I I M M ∞,
      Phi 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => Phi q.1 q.2) (Ico 0 T ×ˢ univ) ∧
      ∀ t ∈ Ico 0 T, ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => Phi s x) (Ico 0 T) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Phi t x, t))) := by
  classical
  obtain ⟨U, hUo, hK, ε, hε, α, hzero, hcurve, hα⟩ :=
    exists_smooth_suspended_local_flow V
  let T := min 1 (ε / 2)
  have hT : 0 < T := lt_min zero_lt_one (half_pos hε)
  have hhalf {t : ℝ} (ht : t ∈ Ioo (-T) T) : t ∈ Ioo (-(ε / 2)) (ε / 2) :=
    Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _) ht
  have hfull {t : ℝ} (ht : t ∈ Ioo (-T) T) : t ∈ Ioo (-ε) ε :=
    Ioo_subset_Ioo (by linarith) (by linarith) (hhalf ht)
  have hneg {t : ℝ} (ht : t ∈ Ioo (-T) T) : -t ∈ Ioo (-T) T :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hstart (x : M) {a : ℝ} (ha : a ∈ Ioo (-T) T) : (x, a) ∈ U := by
    apply hK
    refine ⟨mem_univ _, ?_⟩
    have hT1 : T ≤ 1 := min_le_left _ _
    exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have h0 : (0 : ℝ) ∈ Ioo (-T) T := ⟨neg_lt_zero.mpr hT, hT⟩
  let f : ℝ → M → M := fun t x => (α ((x, 0), t)).1
  let r : ℝ → M → M := fun t x => (α ((x, t), -t)).1
  have hforward (x : M) {t : ℝ} (ht : t ∈ Ioo (-T) T) :
      α ((x, 0), t) = (f t x, t) := by
    apply Prod.ext
    · rfl
    simpa only [zero_add] using
      suspended_time_coordinate V hε (hzero _ (hstart x h0))
        (hcurve _ (hstart x h0)) (hfull ht)
  have hbackward (x : M) {t : ℝ} (ht : t ∈ Ioo (-T) T) :
      α ((x, t), -t) = (r t x, 0) := by
    apply Prod.ext
    · rfl
    simpa only [add_neg_cancel] using
      suspended_time_coordinate V hε (hzero _ (hstart x ht))
        (hcurve _ (hstart x ht)) (hfull (hneg ht))
  have hV1 : ContMDiff J (ModelWithCorners.prod J 𝓘(ℝ, E × ℝ)) 1
      (fun z => (⟨z, V.suspension z⟩ : TangentBundle J (M × ℝ))) :=
    V.suspension_smooth.of_le (by norm_num)
  have hleft (t : ℝ) (ht : t ∈ Ioo (-T) T) (x : M) : r t (f t x) = x := by
    have hret : α ((x, 0), t) ∈ U := by
      rw [hforward x ht]
      exact hstart _ ht
    have h := local_flow_reverse hV1 hε hzero hcurve (hstart x h0) (hhalf ht) hret
    rw [hforward x ht] at h
    exact congrArg Prod.fst h
  have hright (t : ℝ) (ht : t ∈ Ioo (-T) T) (x : M) : f t (r t x) = x := by
    have hret : α ((x, t), -t) ∈ U := by
      rw [hbackward x ht]
      exact hstart _ h0
    have h := local_flow_reverse hV1 hε hzero hcurve (hstart x ht)
      (hhalf (hneg ht)) hret
    rw [hbackward x ht, neg_neg] at h
    exact congrArg Prod.fst h
  have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => f q.1 q.2) (Ioo (-T) T ×ˢ univ) := by
    have he : ContMDiff (𝓘(ℝ, ℝ).prod I) (ModelWithCorners.prod J 𝓘(ℝ, ℝ)) ∞
        (fun q : ℝ × M => ((q.2, (0 : ℝ)), q.1)) :=
      (contMDiff_snd.prodMk contMDiff_const).prodMk contMDiff_fst
    have hh : ContMDiffOn (𝓘(ℝ, ℝ).prod I) J ∞
        (fun q : ℝ × M => α ((q.2, (0 : ℝ)), q.1)) (Ioo (-T) T ×ˢ univ) :=
      hα.comp he.contMDiffOn (fun q hq => ⟨hstart q.2 h0, hfull hq.1⟩)
    exact fun q hq => (hh q hq).fst
  have hr : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => r q.1 q.2) (Ioo (-T) T ×ˢ univ) := by
    have hn : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => -t) :=
      contDiff_neg.contMDiff
    have he : ContMDiff (𝓘(ℝ, ℝ).prod I) (ModelWithCorners.prod J 𝓘(ℝ, ℝ)) ∞
        (fun q : ℝ × M => ((q.2, q.1), -q.1)) :=
      (contMDiff_snd.prodMk contMDiff_fst).prodMk (hn.comp contMDiff_fst)
    have hh : ContMDiffOn (𝓘(ℝ, ℝ).prod I) J ∞
        (fun q : ℝ × M => α ((q.2, q.1), -q.1)) (Ioo (-T) T ×ˢ univ) :=
      hα.comp he.contMDiffOn (fun q hq => ⟨hstart q.2 hq.1, hfull (hneg hq.1)⟩)
    exact fun q hq => (hh q hq).fst
  have hfixed {F : ℝ → M → M}
      (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => F q.1 q.2) (Ioo (-T) T ×ˢ univ))
      (t : ℝ) (ht : t ∈ Ioo (-T) T) : ContMDiff I I ∞ (F t) := by
    rw [← contMDiffOn_univ]
    exact hF.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩)
  let F (t : ℝ) (ht : t ∈ Ioo (-T) T) : Diffeomorph I I M M ∞ :=
    { toEquiv :=
        { toFun := f t
          invFun := r t
          left_inv := hleft t ht
          right_inv := hright t ht }
      contMDiff_toFun := hfixed hf t ht
      contMDiff_invFun := hfixed hr t ht }
  let Phi : ℝ → Diffeomorph I I M M ∞ := fun t =>
    if ht : t ∈ Ioo (-T) T then F t ht else Diffeomorph.refl I M ∞
  have hPhi (t : ℝ) (ht : t ∈ Ioo (-T) T) (x : M) : Phi t x = f t x := by
    simp only [Phi, dif_pos ht]
    rfl
  have hIco : Ico (0 : ℝ) T ⊆ Ioo (-T) T :=
    fun t ht => ⟨(neg_lt_zero.mpr hT).trans_le ht.1, ht.2⟩
  refine ⟨T, hT, Phi, ?_, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro x
    rw [hPhi 0 h0 x]
    exact congrArg Prod.fst (hzero (x, 0) (hstart x h0))
  · exact (hf.mono (prod_mono hIco (Subset.refl _))).congr
      (fun q hq => hPhi q.1 (hIco hq.1) q.2)
  · intro t ht x
    have hder := suspended_spatial_derivative V (hcurve _ (hstart x h0)) (hfull (hIco ht))
    rw [hforward x (hIco ht)] at hder
    have heq : (fun s => Phi s x) =ᶠ[𝓝 t] (fun s => f s x) :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds (hIco ht).1 (hIco ht).2)
        (fun s hs => hPhi s hs x)
    rw [← hPhi t (hIco ht) x] at hder
    exact (hder.congr_of_eventuallyEq heq).hasMFDerivWithinAt

theorem exists_neg_intrinsicDeTurck_family [CompactSpace M]
    {g : ℝ → RiemannianMetric n M} {background : RiemannianMetric n M}
    (D : ∀ t : ℝ, LeviCivitaData (g t)) (B : LeviCivitaData background)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (ModelWithCorners.prod I 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2
          (DeTurckNative.intrinsicDeTurckField (D q.1) B q.2) : TangentBundle I M))) :
    ∃ T > 0, ∃ Phi : ℝ → Diffeomorph I I M M ∞,
      Phi 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => Phi q.1 q.2) (Ico 0 T ×ˢ univ) ∧
      ∀ t ∈ Ico 0 T, ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s => Phi s x) (Ico 0 T) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(DeTurckNative.intrinsicDeTurckField (D t) B (Phi t x)))) := by
  have hneg := TimeDependentConjugatingFlowNative.contMDiff_neg_intrinsicDeTurckField D B hW
  have hsection : ContMDiff J (ModelWithCorners.prod I 𝓘(ℝ, E)) ∞
      (fun q : M × ℝ =>
        (Bundle.TotalSpace.mk' E q.1
          (-(DeTurckNative.intrinsicDeTurckField (D q.2) B q.1)) : TangentBundle I M)) :=
    hneg.comp (contMDiff_snd.prodMk contMDiff_fst)
  let V := SmoothTimeDependentVectorField.ofSection
    (fun q : M × ℝ => -(DeTurckNative.intrinsicDeTurckField (D q.2) B q.1)) hsection
  obtain ⟨T, hT, Phi, h0, hsm, hgen⟩ := exists_diffeomorph_family V
  exact ⟨T, hT, Phi, h0, hsm, hgen⟩

end SuspendedFlow

end PoincareConjecture.CompactTimeDependentFlowNative

end

import PoincareConjecture.Proofs.M51.EventPolicy
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.M48.StaticNeck
import PoincareConjecture.Proofs.M48.StaticCap
import PoincareConjecture.Proofs.M48.StaticComponents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace SurgeryVanishingEventData

variable {P₀ P₁ : SurgeryParameters}
    {slice₀ slice₁ : ℝ → GeneralizedSliceCarrier.{u}}
    {metric₀ : ∀ t, RiemannianMetric 3 (slice₀ t).carrier}
    {metric₁ : ∀ t, RiemannianMetric 3 (slice₁ t).carrier}
    {T : ℝ}

structure PullbackData (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    (slice₁ : ℝ → GeneralizedSliceCarrier.{u})
    (metric₁ : ∀ t, RiemannianMetric 3 (slice₁ t).carrier)
    (initial : Diffeomorph (𝓡 3) (𝓡 3)
      (slice₁ A.tMinus).carrier (slice₀ A.tMinus).carrier ∞) where
  sliceMap : ∀ t : Set.Ico A.tMinus T,
    Diffeomorph (𝓡 3) (𝓡 3)
      (slice₀ t.1).carrier (slice₁ t.1).carrier ∞
  initial_sliceMap : ∀ x,
    sliceMap ⟨A.tMinus, le_rfl, A.tMinus_lt⟩ (initial x) = x
  slice_isometry : ∀ (t : Set.Ico A.tMinus T)
      (y : (slice₀ t.1).carrier) (v w : TangentSpace (𝓡 3) y),
      (metric₁ t.1).inner (sliceMap t y)
          (mfderiv (𝓡 3) (𝓡 3) (sliceMap t) y v)
          (mfderiv (𝓡 3) (𝓡 3) (sliceMap t) y w) =
        (metric₀ t.1).inner y v w

noncomputable def PullbackData.toEvent
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    {initial : Diffeomorph (𝓡 3) (𝓡 3)
      (slice₁ A.tMinus).carrier (slice₀ A.tMinus).carrier ∞}
    (D : PullbackData A slice₁ metric₁ initial) :
    SurgeryVanishingEventData P₀ slice₁ metric₁ T := by
  let e := initial
  let he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e := initial.isLocalDiffeomorph
  let F := A.pre_flow.pullbackWithConnection e he
      (fun t => ((A.pre_flow.metric t).pullbackOfLocalDiffeomorph e he).leviCivitaData)
  let preId : ∀ t : Set.Ico A.tMinus T,
      Diffeomorph (𝓡 3) (𝓡 3)
        (slice₁ A.tMinus).carrier (slice₁ t.1).carrier ∞ := fun t =>
    e.trans ((A.pre_identify t).trans (D.sliceMap t))
  have hpre : ∀ t : Set.Ico A.tMinus T,
      MetricHomothety (F.metric t.1) (A.pre_flow.metric t.1) initial 1 := by
    intro t x v w
    simp only [one_mul]
    change (A.pre_flow.metric t.1).inner (e x)
        (mfderiv (𝓡 3) (𝓡 3) e x v)
        (mfderiv (𝓡 3) (𝓡 3) e x w) =
      (F.metric t.1).inner x v w
    rfl
  have hpre_calculus : ∀ t : Set.Ico A.tMinus T,
      MetricHomothetyCalculus (F.metric t.1) (A.pre_flow.metric t.1)
        initial 1 := by
    intro t
    exact m13.metric_homothety _ _ _ _ _ 1 (by norm_num) (hpre t)
  have hpre_initial : ∀ x, preId ⟨A.tMinus, le_rfl, A.tMinus_lt⟩ x = x := by
    intro x
    change D.sliceMap ⟨A.tMinus, le_rfl, A.tMinus_lt⟩
      (A.pre_identify ⟨A.tMinus, le_rfl, A.tMinus_lt⟩ (e x)) = x
    rw [A.pre_initial, D.initial_sliceMap]
  refine {
    tMinus := A.tMinus
    tMinus_nonnegative := A.tMinus_nonnegative
    tMinus_lt := A.tMinus_lt
    pre_nonempty := by
      obtain ⟨y⟩ := A.pre_nonempty
      exact ⟨D.sliceMap ⟨A.tMinus, le_rfl, A.tMinus_lt⟩ y⟩
    pre_flow := F
    pre_identify := preId
    pre_initial := hpre_initial
    pre_metric := ?_
    left_limit_volume := A.left_limit_volume
    left_limit_volume_tendsto := ?_
    disappearing_start := A.disappearing_start
    disappearing_start_bounds := A.disappearing_start_bounds
    disappearing_curvature := ?_
    disappearing_cover := ?_ }
  · intro t x v w
    let j := A.pre_identify t
    let k := D.sliceMap t
    let c := e.trans (j.trans k)
    have hc : (c : (slice₁ A.tMinus).carrier → (slice₁ t.1).carrier) =
        k ∘ j ∘ e := by
      funext z
      rfl
    change (metric₁ t.1).inner (preId t x)
        (mfderiv (𝓡 3) (𝓡 3) (preId t) x v)
        (mfderiv (𝓡 3) (𝓡 3) (preId t) x w) =
      (F.metric t.1).inner x v w
    rw [show (preId t : (slice₁ A.tMinus).carrier → (slice₁ t.1).carrier) = c from rfl, hc,
      mfderiv_comp x
        (k.contMDiff.mdifferentiable (by simp) (j (e x)))
        ((j.contMDiff.comp e.contMDiff).mdifferentiable (by simp) x),
      mfderiv_comp x
        (j.contMDiff.mdifferentiable (by simp) (e x))
        (e.contMDiff.mdifferentiable (by simp) x)]
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    change (metric₁ t.1).inner (D.sliceMap t (A.pre_identify t (e x)))
        (mfderiv (𝓡 3) (𝓡 3) (D.sliceMap t) (A.pre_identify t (e x))
          (mfderiv (𝓡 3) (𝓡 3) (A.pre_identify t) (e x)
            (mfderiv (𝓡 3) (𝓡 3) e x v)))
        (mfderiv (𝓡 3) (𝓡 3) (D.sliceMap t) (A.pre_identify t (e x))
          (mfderiv (𝓡 3) (𝓡 3) (A.pre_identify t) (e x)
            (mfderiv (𝓡 3) (𝓡 3) e x w))) =
      (F.metric t.1).inner x v w
    rw [D.slice_isometry t (j (e x)) _ _, A.pre_metric t (e x) _ _]
    rfl
  · apply A.left_limit_volume_tendsto.congr'
    filter_upwards [Ioo_mem_nhdsLT A.tMinus_lt] with t ht
    let rt : Set.Ico A.tMinus T := ⟨t, ht.1.le, ht.2⟩
    have hi : MetricHomothety (metric₀ t) (metric₁ t) (D.sliceMap rt) 1 := by
      intro x v w
      simpa only [one_mul] using D.slice_isometry rt x v w
    have hv := (m13.metric_homothety (slice₀ t).carrier (slice₁ t).carrier
      (metric₀ t) (metric₁ t) (D.sliceMap rt) 1 (by norm_num) hi).volume_image Set.univ
    change calibratedMetricVolume (metric₁ t) (D.sliceMap rt '' Set.univ) =
      ENNReal.ofReal ((1 : ℝ) ^ ((3 : ℝ) / 2)) *
        calibratedMetricVolume (metric₀ t) Set.univ at hv
    rw [image_univ_of_surjective
      (f := (D.sliceMap rt : (slice₀ t).carrier → (slice₁ t).carrier))
      (D.sliceMap rt).surjective,
      Real.one_rpow, ENNReal.ofReal_one, one_mul] at hv
    exact hv.symm
  · intro L hL
    obtain ⟨s, hs0, hs1, hs⟩ := A.disappearing_curvature L hL
    refine ⟨s, hs0, hs1, ?_⟩
    intro t ht x
    have H := hpre_calculus ⟨t, hs0.trans ht.1, ht.2⟩
    exact (hs t ht (e x)).trans_eq (by
      simpa only [div_one] using
        H.scalar_eq (F.connection t) (A.pre_flow.connection t) x)
  · intro t ht x
    have htpre : t ∈ Set.Ico A.tMinus T :=
      ⟨A.disappearing_start_bounds.1.le.trans ht.1, ht.2⟩
    have he := hpre ⟨t, htpre⟩
    have H := hpre_calculus ⟨t, htpre⟩
    obtain hcover := A.disappearing_cover t ht (e x)
    cases hcover with
    | inl hneck =>
        obtain ⟨N, hcenter, hepsilon⟩ := hneck
        refine Or.inl ⟨N.m48_pullback he H (F.connection t), ?_, hepsilon⟩
        change e.symm N.center = x
        rw [hcenter]
        exact e.symm_apply_apply x
    | inr hrest =>
        cases hrest with
        | inl hcap =>
            obtain ⟨N, hx, hepsilon, hconstant⟩ := hcap
            refine Or.inr (Or.inl ⟨N.m48_pullback he H (F.connection t), ?_,
              hepsilon, hconstant⟩)
            change e x ∈ N.core
            exact hx
        | inr hcomponent =>
            obtain ⟨U, hx, hU, hpositive⟩ := hcomponent
            let V : Set (slice₁ A.tMinus).carrier := e ⁻¹' U
            refine Or.inr (Or.inr ⟨V, ?_, ?_, ?_⟩)
            · exact hx
            · change e ⁻¹' U = connectedComponent x
              rw [hU]
              change e.toHomeomorph ⁻¹' connectedComponent (e x) = connectedComponent x
              rw [M48.preimage_connectedComponent e.toHomeomorph]
              exact congrArg connectedComponent (e.symm_apply_apply x)
            · intro y hy v w hpair
              change e y ∈ U at hy
              have hpairOld :
                  LeviCivitaData.IsOrthonormalPair (A.pre_flow.metric t) (e y)
                    (mfderiv (𝓡 3) (𝓡 3) e y v)
                    (mfderiv (𝓡 3) (𝓡 3) e y w) := by
                simpa only [e, LeviCivitaData.IsOrthonormalPair,
                  he y v v, he y w w, he y v w, one_mul] using hpair
              have hbound := hpositive (e y) hy _ _ hpairOld
              simpa only [e, H.sectional_eq (F.connection t)
                (A.pre_flow.connection t), div_one] using hbound

@[simp] theorem PullbackData.toEvent_tMinus
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    {initial : Diffeomorph (𝓡 3) (𝓡 3)
      (slice₁ A.tMinus).carrier (slice₀ A.tMinus).carrier ∞}
    (D : PullbackData A slice₁ metric₁ initial) :
    (PullbackData.toEvent m13 A D).tMinus = A.tMinus := rfl

@[simp] theorem PullbackData.toEvent_disappearing_start
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    {initial : Diffeomorph (𝓡 3) (𝓡 3)
      (slice₁ A.tMinus).carrier (slice₀ A.tMinus).carrier ∞}
    (D : PullbackData A slice₁ metric₁ initial) :
    (PullbackData.toEvent m13 A D).disappearing_start = A.disappearing_start := rfl

@[simp] theorem PullbackData.toEvent_left_limit_volume
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    {initial : Diffeomorph (𝓡 3) (𝓡 3)
      (slice₁ A.tMinus).carrier (slice₀ A.tMinus).carrier ∞}
    (D : PullbackData A slice₁ metric₁ initial) :
    (PullbackData.toEvent m13 A D).left_limit_volume = A.left_limit_volume := rfl

theorem PullbackData.toEvent_pre_identify
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    {initial : Diffeomorph (𝓡 3) (𝓡 3)
      (slice₁ A.tMinus).carrier (slice₀ A.tMinus).carrier ∞}
    (D : PullbackData A slice₁ metric₁ initial)
    (t : Set.Ico A.tMinus T) (x : (slice₁ A.tMinus).carrier) :
    (PullbackData.toEvent m13 A D).pre_identify t x =
      D.sliceMap t (A.pre_identify t (initial x)) := rfl

theorem PullbackData.toEvent_pre_metric_homothety
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    {initial : Diffeomorph (𝓡 3) (𝓡 3)
      (slice₁ A.tMinus).carrier (slice₀ A.tMinus).carrier ∞}
    (D : PullbackData A slice₁ metric₁ initial) (t : ℝ) :
    MetricHomothety ((PullbackData.toEvent m13 A D).pre_flow.metric t)
      (A.pre_flow.metric t) initial 1 := by
  intro x v w
  simp only [one_mul]
  rfl

theorem PullbackData.toEvent_terminalPolicy
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    {initial : Diffeomorph (𝓡 3) (𝓡 3)
      (slice₁ A.tMinus).carrier (slice₀ A.tMinus).carrier ∞}
    (D : PullbackData A slice₁ metric₁ initial)
    (policy : SurgeryVanishingEventTerminalPolicy A) :
    SurgeryVanishingEventTerminalPolicy (PullbackData.toEvent m13 A D) := by
  exact transportTerminalPolicy m13 A (PullbackData.toEvent m13 A D)
    rfl rfl initial (fun t _ => D.toEvent_pre_metric_homothety m13 A t) policy

theorem volume_univ_eq_of_isometry
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (t : ℝ)
    (g : RiemannianMetric 3 (slice₁ t).carrier)
    (h : RiemannianMetric 3 (slice₀ t).carrier)
    (f : Diffeomorph (𝓡 3) (𝓡 3)
      (slice₁ t).carrier (slice₀ t).carrier ∞)
    (hf : MetricHomothety g h f 1) :
    calibratedMetricVolume g Set.univ =
      calibratedMetricVolume h Set.univ := by
  have hv := (m13.metric_homothety (slice₁ t).carrier (slice₀ t).carrier
    g h f 1 (by norm_num) hf).volume_image Set.univ
  change calibratedMetricVolume h (f '' Set.univ) =
    ENNReal.ofReal ((1 : ℝ) ^ ((3 : ℝ) / 2)) *
      calibratedMetricVolume g Set.univ at hv
  rw [image_univ_of_surjective (f := (f : (slice₁ t).carrier →
    (slice₀ t).carrier)) f.surjective, Real.one_rpow,
    ENNReal.ofReal_one, one_mul] at hv
  exact hv.symm

theorem volume_function_eq_on
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (B : SurgeryVanishingEventData P₁ slice₁ metric₁ T)
    (_A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    (q : ∀ (t : ℝ), t ∈ Set.Ico B.tMinus T →
      Diffeomorph (𝓡 3) (𝓡 3)
        (slice₁ t).carrier (slice₀ t).carrier ∞)
    (hq : ∀ (t : ℝ) (ht : t ∈ Set.Ico B.tMinus T),
      MetricHomothety (metric₁ t) (metric₀ t) (q t ht) 1) :
    ∀ (t : ℝ) (_ht : t ∈ Set.Ico B.tMinus T),
      calibratedMetricVolume (metric₁ t) Set.univ =
        calibratedMetricVolume (metric₀ t) Set.univ := by
  intro t ht
  exact volume_univ_eq_of_isometry m13 t (metric₁ t) (metric₀ t)
    (q t ht) (hq t ht)

theorem left_limit_volume_eq
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (B : SurgeryVanishingEventData P₁ slice₁ metric₁ T)
    (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    (q : ∀ (t : ℝ), t ∈ Set.Ico B.tMinus T →
      Diffeomorph (𝓡 3) (𝓡 3)
        (slice₁ t).carrier (slice₀ t).carrier ∞)
    (hq : ∀ (t : ℝ) (ht : t ∈ Set.Ico B.tMinus T),
      MetricHomothety (metric₁ t) (metric₀ t) (q t ht) 1) :
    B.left_limit_volume = A.left_limit_volume := by
  have hev : (fun t : ℝ => calibratedMetricVolume (metric₁ t) Set.univ)
      =ᶠ[nhdsWithin T (Set.Iio T)]
      (fun t : ℝ => calibratedMetricVolume (metric₀ t) Set.univ) := by
    filter_upwards [Ioo_mem_nhdsLT B.tMinus_lt] with t ht
    exact volume_function_eq_on m13 B A q hq t ⟨ht.1.le, ht.2⟩
  have hB : Tendsto (fun t : ℝ => calibratedMetricVolume (metric₁ t) Set.univ)
      (nhdsWithin T (Set.Iio T)) (𝓝 A.left_limit_volume) :=
    A.left_limit_volume_tendsto.congr' hev.symm
  exact (tendsto_nhds_unique hB B.left_limit_volume_tendsto).symm

theorem transport
    (m13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (B : SurgeryVanishingEventData P₁ slice₁ metric₁ T)
    (A : SurgeryVanishingEventData P₀ slice₀ metric₀ T)
    (parameters : P₁ = P₀) (reference : B.tMinus = A.tMinus)
    (e : Diffeomorph (𝓡 3) (𝓡 3)
      (slice₁ B.tMinus).carrier (slice₀ A.tMinus).carrier ∞)
    (hpre : ∀ t ∈ Set.Ico B.tMinus T,
      MetricHomothety (B.pre_flow.metric t) (A.pre_flow.metric t) e 1)
    (q : ∀ (t : ℝ), t ∈ Set.Ico B.tMinus T →
      Diffeomorph (𝓡 3) (𝓡 3)
        (slice₁ t).carrier (slice₀ t).carrier ∞)
    (hq : ∀ (t : ℝ) (ht : t ∈ Set.Ico B.tMinus T),
      MetricHomothety (metric₁ t) (metric₀ t) (q t ht) 1)
    (policy : SurgeryVanishingEventTerminalPolicy A) :
    B.left_limit_volume = A.left_limit_volume ∧
      SurgeryVanishingEventTerminalPolicy B := by
  refine ⟨left_limit_volume_eq m13 B A q hq,
    transportTerminalPolicy m13 A B parameters reference e hpre policy⟩

end SurgeryVanishingEventData

end PoincareConjecture

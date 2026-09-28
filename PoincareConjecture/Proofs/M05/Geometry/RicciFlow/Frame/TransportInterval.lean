import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Frame.RicciTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareConjecture.RicciFlow.Frame

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem exists_ricciTransport_on (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M (Ico a b)) (hab : a < b) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    ∃ U : ℝ → TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      U a = ContinuousLinearMap.id ℝ _ ∧
      (∀ t ∈ Ico a b, HasDerivWithinAt U
        ((ricciEndomorphism F x t).comp (U t)) (Ico a b) t) ∧
      (∀ t ∈ Ico a b, ∀ v w,
        (F.metric t).inner x (U t v) (U t w) = (F.metric a).inner x v w) ∧
      (∀ t ∈ Ico a b, (U t).IsInvertible) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) := inferInstance
  let A := ricciEndomorphism F x
  choose Ψ hzero hderiv hpair hinv using fun T : Ioo a b =>
    exists_ricciTransport hC F T.2.1 T.2.2 x
  have hcompare (S T : Ioo a b) {t : ℝ} (hat : a ≤ t) (htS : t ≤ S) (htT : t ≤ T) :
      Ψ S t = Ψ T t := by
    have hs : Icc a (min S.1 T.1) ⊆ Ico a b := fun r hr =>
      ⟨hr.1, (hr.2.trans (min_le_left _ _)).trans_lt S.2.2⟩
    have hc := (continuousOn_ricciEndomorphism hC F x).mono hs
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    let K' : ℝ≥0 := ⟨max K 0, le_max_right _ _⟩
    have hK' : ∀ r ∈ Icc a (min S.1 T.1), ‖A r‖₊ ≤ K' := by
      intro r hr
      exact_mod_cast (hK r hr).trans (le_max_left K 0)
    ext v
    have hdS : Poincare.ODE.Linear.IsSolOn A a (min S.1 T.1) (fun r => Ψ S r v) := by
      intro r hr
      have h := ((hderiv S r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩).clm_apply
        (hasDerivWithinAt_const r (Icc a S.1) v)).mono
          (Icc_subset_Icc le_rfl (min_le_left S.1 T.1))
      simpa using h
    have hdT : Poincare.ODE.Linear.IsSolOn A a (min S.1 T.1) (fun r => Ψ T r v) := by
      intro r hr
      have h := ((hderiv T r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩).clm_apply
        (hasDerivWithinAt_const r (Icc a T.1) v)).mono
          (Icc_subset_Icc le_rfl (min_le_right S.1 T.1))
      simpa using h
    exact Poincare.ODE.Linear.IsSolOn.eqOn_of_left hK' hdS hdT
      (by rw [hzero S, hzero T]) ⟨hat, le_min htS htT⟩
  let stage (t : Ico a b) : Ioo a b :=
    ⟨(t.1 + b) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
  let U := fun t : ℝ => if ht : t ∈ Ico a b then Ψ (stage ⟨t, ht⟩) t
    else ContinuousLinearMap.id ℝ _
  have hU (T : Ioo a b) {t : ℝ} (ht : t ∈ Icc a T.1) : U t = Ψ T t := by
    have htab : t ∈ Ico a b := ⟨ht.1, ht.2.trans_lt T.2.2⟩
    simp only [U, dif_pos htab]
    exact hcompare _ T ht.1 (by dsimp [stage]; linarith [htab.2]) ht.2
  have ha : a ∈ Ico a b := ⟨le_rfl, hab⟩
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · rw [hU (stage ⟨a, ha⟩) ⟨le_rfl, (stage ⟨a, ha⟩).2.1.le⟩, hzero]
  · intro t ht
    let T := stage ⟨t, ht⟩
    have htT : t < T.1 := by dsimp [T, stage]; linarith [ht.2]
    have hmem : Icc a T.1 ∈ 𝓝[Ico a b] t := by
      refine mem_nhdsWithin.mpr ⟨Iio T.1, isOpen_Iio, htT, ?_⟩
      intro r hr
      exact ⟨hr.2.1, hr.1.le⟩
    have heq : U =ᶠ[𝓝[Ico a b] t] Ψ T := by
      filter_upwards [hmem] with r hr using hU T hr
    rw [hU T ⟨ht.1, htT.le⟩]
    exact ((hderiv T t ⟨ht.1, htT.le⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
      heq (hU T ⟨ht.1, htT.le⟩)
  · intro t ht v w
    let T := stage ⟨t, ht⟩
    have hmem : t ∈ Icc a T.1 := ⟨ht.1, by dsimp [T, stage]; linarith [ht.2]⟩
    rw [hU T hmem]
    exact hpair T t hmem v w
  · intro t ht
    let T := stage ⟨t, ht⟩
    have hmem : t ∈ Icc a T.1 := ⟨ht.1, by dsimp [T, stage]; linarith [ht.2]⟩
    rw [hU T hmem]
    exact hinv T t hmem

end PoincareConjecture.RicciFlow.Frame

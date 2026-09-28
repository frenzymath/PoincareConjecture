import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.Representative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.Compactness
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.Normed.Operator.Banach








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

omit [NeZero n] in
theorem boundedContinuous_eq_of_ae (hΩ : IsOpen Ω) {F G : M →ᵇ ℝ}
    (hae : (F : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω] G)
    (hF : ∀ x ∉ Ω, F x = 0) (hG : ∀ x ∉ Ω, G x = 0) : F = G := by
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  have h := Measure.eqOn_open_of_ae_eq hae hΩ F.continuous.continuousOn
    G.continuous.continuousOn
  ext x
  by_cases hx : x ∈ Ω
  · exact h hx
  · rw [hF x hx, hG x hx]

omit [NeZero n] in
private theorem boundedContinuous_eq_of_toLp_eq
    [IsFiniteMeasure (g.volumeMeasure.restrict Ω)] (hΩ : IsOpen Ω)
    {F G : M →ᵇ ℝ}
    (h : BoundedContinuousFunction.toLp 2 (g.volumeMeasure.restrict Ω) ℝ F =
      BoundedContinuousFunction.toLp 2 (g.volumeMeasure.restrict Ω) ℝ G)
    (hF : ∀ x ∉ Ω, F x = 0) (hG : ∀ x ∉ Ω, G x = 0) : F = G := by
  apply boundedContinuous_eq_of_ae (g := g) hΩ _ hF hG
  exact (BoundedContinuousFunction.coeFn_toLp 2 _ ℝ F).symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun v : Lp ℝ 2
      (g.volumeMeasure.restrict Ω) => (v : M → ℝ)) h)).trans
      (BoundedContinuousFunction.coeFn_toLp 2 _ ℝ G))


theorem exists_heatPower_continuousLinearMap (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (k : ℕ) (t : ℝ) (ht : 0 < t) :
    ∃ T : Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] (M →ᵇ ℝ),
      ∀ f : Lp ℝ 2 (g.volumeMeasure.restrict Ω),
        (T f : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω]
          (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
            S.isOpen S.isCompact_closure k t f : M → ℝ) ∧
        (∀ x : M, x ∉ Ω → T f x = 0) ∧
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (T f : M → ℝ) Ω := by
  classical
  let : IsFiniteMeasure (g.volumeMeasure.restrict Ω) :=
    isFiniteMeasure_restrict.mpr ((measure_mono subset_closure).trans_lt
      (g.volumeMeasure_lt_top_of_isCompact S.isCompact_closure)).ne
  let P := heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure k t
  have hex (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
      ∃ F : M →ᵇ ℝ, (F : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω] (P f : M → ℝ) ∧
        (∀ x ∉ Ω, F x = 0) ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (F : M → ℝ) Ω := by
    obtain ⟨F, hFc, hFs, hFcomp, -, hFae, hFzero⟩ :=
      exists_heatPower_continuous_representative D S k t ht f
    obtain ⟨C, hC⟩ := hFcomp.exists_bound_of_continuous hFc
    refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup F hFc C hC, ?_, hFzero, hFs⟩
    have h := toDomainL2_ae (energyHeatSpectralPower D Ω
      (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure k t f)
    rw [toDomainL2_energyHeatSpectralPower D Ω
      (Nat.pos_of_ne_zero (NeZero.ne n)) S.isOpen S.isCompact_closure k ht] at h
    exact hFae.trans h.symm
  choose F hF using hex
  let J := BoundedContinuousFunction.toLp (E := ℝ) 2 (g.volumeMeasure.restrict Ω) ℝ
  have hJ (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) : J (F f) = P f := by
    apply Lp.ext
    exact (BoundedContinuousFunction.coeFn_toLp 2 _ ℝ (F f)).trans (hF f).1
  let T : Lp ℝ 2 (g.volumeMeasure.restrict Ω) →ₗ[ℝ] (M →ᵇ ℝ) :=
    { toFun := F
      map_add' := by
        intro f h
        apply boundedContinuous_eq_of_toLp_eq (g := g) S.isOpen
        · change J (F (f + h)) = J (F f + F h)
          simp only [map_add, hJ]
        · exact (hF (f + h)).2.1
        · intro x hx
          simp [(hF f).2.1 x hx, (hF h).2.1 x hx]
      map_smul' := by
        intro c f
        apply boundedContinuous_eq_of_toLp_eq (g := g) S.isOpen
        · change J (F (c • f)) = J (c • F f)
          simp only [map_smul, hJ]
        · exact (hF (c • f)).2.1
        · intro x hx
          simp [(hF f).2.1 x hx] }
  have hTc : Continuous T := by
    apply T.continuous_of_seq_closed_graph
    intro u f G hu hG
    have hJlim : Tendsto (fun i => J (T (u i))) atTop (𝓝 (J G)) :=
      (J.continuous.tendsto G).comp hG
    have hPlim : Tendsto (fun i => J (T (u i))) atTop (𝓝 (P f)) := by
      have heq : (fun i => J (T (u i))) = P ∘ u := funext fun i => hJ (u i)
      rw [heq]
      exact (P.continuous.tendsto f).comp hu
    apply boundedContinuous_eq_of_toLp_eq (g := g) S.isOpen
    · change J G = J (T f)
      rw [show J (T f) = P f from hJ f]
      exact tendsto_nhds_unique hJlim hPlim
    · intro x hx
      have heval : Tendsto (fun i => T (u i) x) atTop (𝓝 (G x)) :=
        ((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto G).comp hG
      have hzseq : (fun i => T (u i) x) = fun _ => (0 : ℝ) :=
        funext fun i => (hF (u i)).2.1 x hx
      rw [hzseq] at heval
      exact tendsto_nhds_unique heval tendsto_const_nhds
    · exact (hF f).2.1
  exact ⟨⟨T, hTc⟩, hF⟩

variable (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)


def heatPowerContinuous (k : ℕ) (t : ℝ) (ht : 0 < t) :
    Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] (M →ᵇ ℝ) :=
  (exists_heatPower_continuousLinearMap D S k t ht).choose

theorem heatPowerContinuous_ae (k : ℕ) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    (heatPowerContinuous D S k t ht f : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω]
      (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure k t f : M → ℝ) :=
  ((exists_heatPower_continuousLinearMap D S k t ht).choose_spec f).1

theorem heatPowerContinuous_zero_outside (k : ℕ) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (x : M) (hx : x ∉ Ω) :
    heatPowerContinuous D S k t ht f x = 0 :=
  ((exists_heatPower_continuousLinearMap D S k t ht).choose_spec f).2.1 x hx

theorem contMDiffOn_heatPowerContinuous (k : ℕ) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (heatPowerContinuous D S k t ht f : M → ℝ) Ω :=
  ((exists_heatPower_continuousLinearMap D S k t ht).choose_spec f).2.2

theorem heatPowerContinuous_unique (k : ℕ) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (F : M →ᵇ ℝ)
    (hae : (F : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω]
      (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure k t f : M → ℝ))
    (hzero : ∀ x ∉ Ω, F x = 0) : F = heatPowerContinuous D S k t ht f :=
  boundedContinuous_eq_of_ae S.isOpen (hae.trans (heatPowerContinuous_ae D S k t ht f).symm)
    hzero (heatPowerContinuous_zero_outside D S k t ht f)

private theorem heatSpectralPower_add_comp (k : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure k (s + t) =
    (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure k s).comp
      (heatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure 0 t) := by
  ext f : 1
  apply (eigenbasis D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure).repr.injective
  ext i
  simp only [ContinuousLinearMap.comp_apply,
    heatSpectralPower_repr D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure k (add_pos hs ht),
    heatSpectralPower_repr D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure k hs,
    heatSpectralPower_repr D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
      S.isOpen S.isCompact_closure 0 ht, pow_zero, one_mul, mul_add, Real.exp_add]
  ring

theorem heatPowerContinuous_add_comp (k : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    heatPowerContinuous D S k (s + t) (add_pos hs ht) =
      (heatPowerContinuous D S k s hs).comp
        (heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
          S.isOpen S.isCompact_closure t.toNNReal) := by
  ext f : 1
  symm
  apply heatPowerContinuous_unique D S k (s + t) (add_pos hs ht) f
  · rw [heatSpectralPower_add_comp D S k s t hs ht,
      heatSpectralPower_zero_eq_heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
        S.isOpen S.isCompact_closure ht]
    exact heatPowerContinuous_ae D S k s hs _
  · exact heatPowerContinuous_zero_outside D S k s hs _


theorem isCompactOperator_heatPowerContinuous (k : ℕ) (t : ℝ) (ht : 0 < t) :
    IsCompactOperator (heatPowerContinuous D S k t ht) := by
  have hhalf : 0 < t / 2 := half_pos ht
  have hfac := heatPowerContinuous_add_comp D S k (t / 2) (t / 2) hhalf hhalf
  simp only [add_halves] at hfac
  rw [hfac]
  exact (isCompactOperator_heatSemigroup D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
    S.isOpen S.isCompact_closure (Real.toNNReal_pos.mpr hhalf)).clm_comp
      (heatPowerContinuous D S k (t / 2) hhalf)

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

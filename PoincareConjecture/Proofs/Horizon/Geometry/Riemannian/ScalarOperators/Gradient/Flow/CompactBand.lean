import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.ManifoldExpansion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Speed
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [T3Space M] in
private theorem contMDiffAt_normalizedGradient
    (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hreg : g.inner x (D.gradient f x) (D.gradient f x) ≠ 0) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (D.normalizedGradient f)) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgrad := D.contMDiffAt_gradient hf
  have hpair : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x :=
    hgrad.inner_bundle hgrad
  exact ((contDiffAt_inv ℝ hreg).contMDiffAt.comp x hpair).smul_section hgrad

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

end PoincareConjecture.LeviCivitaData


namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private structure ExpandingFlow (D : LeviCivitaData g) (f : M → ℝ)
    (U V : Set M) (l H a b : ℝ) (Φ : ℝ × M → M) : Prop where
  smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ (Ioo a b ×ˢ V)
  initial : ∀ y ∈ V, Φ (0, y) = y
  stays : ∀ y ∈ V, ∀ t ∈ Ioo a b, Φ (t, y) ∈ U
  orbit : ∀ y ∈ V, IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y))
    (D.normalizedGradient f) (Ioo a b)
  level : ∀ y ∈ V, ∀ t ∈ Ico 0 b, f (Φ (t, y)) = f y + t
  expansion : ∀ y ∈ V, ∀ t ∈ Ico 0 b, ∀ v : TangentSpace (𝓡 n) y,
    mvfderiv (𝓡 n) f y v = 0 →
      g.inner (Φ (t, y)) (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v)
        (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v) ≤
      g.inner y v v * Real.exp (2 * (H / l ^ 2) * t)

omit [T3Space M] in
private theorem ExpandingFlow.mono
    {D : LeviCivitaData g} {f : M → ℝ} {U V W : Set M}
    {l H a b a' b' : ℝ} {Φ : ℝ × M → M}
    (h : ExpandingFlow D f U V l H a b Φ) (hWV : W ⊆ V)
    (ha : a ≤ a') (hb : b' ≤ b) :
    ExpandingFlow D f U W l H a' b' Φ := by
  have hsub : Ioo a' b' ⊆ Ioo a b := Ioo_subset_Ioo ha hb
  exact ⟨h.smooth.mono (prod_mono hsub hWV), fun y hy => h.initial y (hWV hy),
    fun y hy t ht => h.stays y (hWV hy) t (hsub ht),
    fun y hy => (h.orbit y (hWV hy)).mono hsub,
    fun y hy t ht => h.level y (hWV hy) t ⟨ht.1, ht.2.trans_le hb⟩,
    fun y hy t ht => h.expansion y (hWV hy) t ⟨ht.1, ht.2.trans_le hb⟩⟩

omit [T3Space M] in
private theorem ExpandingFlow.congr
    {D : LeviCivitaData g} {f : M → ℝ} {U V : Set M}
    {l H a b : ℝ} {Φ Ψ : ℝ × M → M}
    (hV : IsOpen V) (ha : a < 0) (hb : 0 < b)
    (h : ExpandingFlow D f U V l H a b Φ)
    (he : EqOn Ψ Φ (Ioo a b ×ˢ V)) :
    ExpandingFlow D f U V l H a b Ψ := by
  have hev {p : ℝ × M} (hp : p ∈ Ioo a b ×ˢ V) : Ψ =ᶠ[𝓝 p] Φ :=
    Filter.Eventually.mono ((isOpen_Ioo.prod hV).mem_nhds hp) fun z hz => he hz
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact ((h.smooth.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds hp)).congr_of_eventuallyEq
      (hev hp)).contMDiffWithinAt
  · intro y hy
    exact (he ⟨⟨ha, hb⟩, hy⟩).trans (h.initial y hy)
  · intro y hy t ht
    rw [he ⟨ht, hy⟩]
    exact h.stays y hy t ht
  · intro y hy t ht
    have het : (fun s => Ψ (s, y)) =ᶠ[𝓝 t] (fun s => Φ (s, y)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact he ⟨hs, hy⟩
    have hd := (h.orbit y hy).isMIntegralCurveAt (isOpen_Ioo.mem_nhds ht)
    have hd' := hd.hasMFDerivAt.congr_of_eventuallyEq het
    convert! hd'.hasMFDerivWithinAt using 1
    dsimp only
    rw [he (show (t, y) ∈ Ioo a b ×ˢ V from ⟨ht, hy⟩)]
  · intro y hy t ht
    rw [he ⟨⟨ha.trans_le ht.1, ht.2⟩, hy⟩]
    exact h.level y hy t ht
  · intro y hy t ht v hv
    have ht' : t ∈ Ioo a b := ⟨ha.trans_le ht.1, ht.2⟩
    have hey : (fun z => Ψ (t, z)) =ᶠ[𝓝 y] (fun z => Φ (t, z)) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      exact he ⟨ht', hz⟩
    have hd := hey.mfderiv_eq (I := 𝓡 n) (I' := 𝓡 n)
    rw [hd, he ⟨ht', hy⟩]
    exact h.expansion y hy t ht v hv

end PoincareConjecture.LeviCivitaData


namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem ExpandingFlow.union
    {D : LeviCivitaData g} {f : M → ℝ} {U V W : Set M}
    {l H a b : ℝ} {Φ Ψ : ℝ × M → M}
    (hU : IsOpen U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% (D.normalizedGradient f)) U)
    (hV : IsOpen V) (hW : IsOpen W) (ha : a < 0) (hb : 0 < b)
    (hΦ : ExpandingFlow D f U V l H a b Φ)
    (hΨ : ExpandingFlow D f U W l H a b Ψ) :
    ∃ Ξ : ℝ × M → M, ExpandingFlow D f U (V ∪ W) l H a b Ξ := by
  classical
  have heq : ∀ y ∈ V ∩ W, EqOn (fun t => Φ (t, y)) (fun t => Ψ (t, y)) (Ioo a b) := by
    intro y hy
    exact integralCurve_eqOn_Ioo_of_contMDiffOn hU hX ⟨ha, hb⟩ (hΦ.stays y hy.1)
      (hΦ.orbit y hy.1) (hΨ.orbit y hy.2)
      ((hΦ.initial y hy.1).trans (hΨ.initial y hy.2).symm)
  let Ξ : ℝ × M → M := fun p => if p.2 ∈ V then Φ p else Ψ p
  have heΦ : EqOn Ξ Φ (Ioo a b ×ˢ V) := fun p hp => if_pos hp.2
  have heΨ : EqOn Ξ Ψ (Ioo a b ×ˢ W) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    by_cases hyV : y ∈ V
    · exact (if_pos hyV).trans (heq y ⟨hyV, hy⟩ ht)
    · exact if_neg hyV
  have hleft := hΦ.congr hV ha hb heΦ
  have hright := hΨ.congr hW ha hb heΨ
  refine ⟨Ξ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨t, y⟩ ⟨ht, hy | hy⟩
    · exact (hleft.smooth.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨ht, hy⟩)).contMDiffWithinAt
    · exact (hright.smooth.contMDiffAt ((isOpen_Ioo.prod hW).mem_nhds ⟨ht, hy⟩)).contMDiffWithinAt
  · intro y hy
    rcases hy with hy | hy
    · exact hleft.initial y hy
    · exact hright.initial y hy
  · intro y hy
    rcases hy with hy | hy
    · exact hleft.stays y hy
    · exact hright.stays y hy
  · intro y hy
    rcases hy with hy | hy
    · exact hleft.orbit y hy
    · exact hright.orbit y hy
  · intro y hy
    rcases hy with hy | hy
    · exact hleft.level y hy
    · exact hright.level y hy
  · intro y hy
    rcases hy with hy | hy
    · exact hleft.expansion y hy
    · exact hright.expansion y hy

private theorem exists_uniform_short_expandingFlow
    (D : LeviCivitaData g) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient f y))
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) f y v = 0 → D.hessian f y v v ≤ H * g.inner y v v)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ K ⊆ V ∧ 0 < δ ∧ ExpandingFlow D f U V l H (-δ) δ Φ := by
  have hregular (y : M) (hy : y ∈ U) :
      g.inner y (D.gradient f y) (D.gradient f y) ≠ 0 := by
    intro hz
    have hzero : g.tangentNorm y (D.gradient f y) = 0 := by
      simp only [RiemannianMetric.tangentNorm, hz, Real.sqrt_zero]
    linarith [hgrad y hy]
  have hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1
      (T% (D.normalizedGradient f)) U := by
    intro y hy
    exact ((contMDiffAt_normalizedGradient D (hf.contMDiffAt (hU.mem_nhds hy))
      (hregular y hy)).of_le (by simp)).contMDiffWithinAt
  let P : Set M → Prop := fun S =>
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ S ⊆ V ∧ 0 < δ ∧ ExpandingFlow D f U V l H (-δ) δ Φ
  change P K
  refine hK.induction_on (p := P) ?_ ?_ ?_ ?_
  · refine ⟨∅, 1, Prod.snd, isOpen_empty, subset_rfl, zero_lt_one, ?_⟩
    exact ⟨fun _ hp => False.elim hp.2, fun _ hy => False.elim hy,
      fun _ hy => False.elim hy, fun _ hy => False.elim hy,
      fun _ hy => False.elim hy, fun _ hy => False.elim hy⟩
  · rintro S S' hSS' ⟨V, δ, Φ, hV, hSV, hδ, hΦ⟩
    exact ⟨V, δ, Φ, hV, hSS'.trans hSV, hδ, hΦ⟩
  · rintro S S' ⟨V, δ, Φ, hV, hSV, hδ, hΦ⟩ ⟨W, ε, Ψ, hW, hS'W, hε, hΨ⟩
    have hmin : 0 < min δ ε := lt_min hδ hε
    obtain ⟨Ξ, hΞ⟩ := ExpandingFlow.union hU hX hV hW (by linarith) hmin
      (hΦ.mono Subset.rfl (neg_le_neg (min_le_left _ _)) (min_le_left _ _))
      (hΨ.mono Subset.rfl (neg_le_neg (min_le_right _ _)) (min_le_right _ _))
    exact ⟨V ∪ W, min δ ε, Ξ, hV.union hW, union_subset_union hSV hS'W, hmin, hΞ⟩
  · intro x hx
    obtain ⟨V, δ, Φ, hV, hxV, _, hδ, hs, hi, hd, he⟩ :=
      D.exists_local_normalizedGradient_manifoldFlow_with_expansion hU hf hl hH hgrad hhess
        (hKU hx)
    refine ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), V, δ, Φ,
      hV, subset_rfl, hδ, hs, hi, ?_, ?_, ?_, ?_⟩
    · exact fun y hy => (hd y hy).1
    · exact fun y hy => (hd y hy).2
    · exact fun y hy t ht => (he y hy t ht).1
    · exact fun y hy t ht => (he y hy t ht).2

end PoincareConjecture.LeviCivitaData


namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem ExpandingFlow.tangent
    {D : LeviCivitaData g} {f : M → ℝ} {U V : Set M}
    {l H a b : ℝ} {Φ : ℝ × M → M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hV : IsOpen V) (ha : a < 0) (hb : 0 < b)
    (h : ExpandingFlow D f U V l H a b Φ)
    {y : M} (hy : y ∈ V) {t : ℝ} (ht : t ∈ Ico 0 b)
    (v : TangentSpace (𝓡 n) y) (hv : mvfderiv (𝓡 n) f y v = 0) :
    mvfderiv (𝓡 n) f (Φ (t, y)) (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v) = 0 := by
  have ht' : t ∈ Ioo a b := ⟨ha.trans_le ht.1, ht.2⟩
  have hpointU : y ∈ U := by
    simpa only [h.initial y hy] using h.stays y hy 0 ⟨ha, hb⟩
  have hΦ := (h.smooth.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨ht', hy⟩)).comp y
    (contMDiffAt_const.prodMk contMDiffAt_id)
  have he : (fun z => f (Φ (t, z))) =ᶠ[𝓝 y] (fun z => f z + t) := by
    filter_upwards [hV.mem_nhds hy] with z hz
    exact h.level z hz t ht
  have hd := he.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ))
  have hchain := mvfderiv_comp y
    ((hf.contMDiffAt (hU.mem_nhds (h.stays y hy t ht'))).mdifferentiableAt (by simp))
    (hΦ.mdifferentiableAt (by simp))
  have hadd := mvfderiv_fun_add
    ((hf.contMDiffAt (hU.mem_nhds hpointU)).mdifferentiableAt (by simp))
    (mdifferentiableAt_const (c := t))
  have hdv := congrArg (fun L => L v) hd
  change mvfderiv (𝓡 n) (fun z => f (Φ (t, z))) y v =
    mvfderiv (𝓡 n) (fun z => f z + t) y v at hdv
  rw [hadd] at hdv
  simp only [mvfderiv_const, add_zero] at hdv
  exact (congrArg (fun L => L v) hchain).symm.trans (hdv.trans hv)

end PoincareConjecture.LeviCivitaData


namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem ExpandingFlow.extend
    {D : LeviCivitaData g} {f : M → ℝ} {U V W : Set M}
    {l H s d δ τ : ℝ} {Φ Ψ : ℝ × M → M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% (D.normalizedGradient f)) U)
    (hV : IsOpen V) (hW : IsOpen W) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (hδ : 0 < δ) (hτ : 0 < τ) (hsmall : d < τ)
    (hΦ : ExpandingFlow D f U V l H (-δ) (s + δ) Φ)
    (hΨ : ExpandingFlow D f U W l H (-τ) τ Ψ) :
    IsOpen (V ∩ (fun y => Φ (s, y)) ⁻¹' W) ∧
      ∃ ε > 0, ∃ Ξ : ℝ × M → M,
        ExpandingFlow D f U (V ∩ (fun y => Φ (s, y)) ⁻¹' W)
          l H (-ε) (s + d + ε) Ξ := by
  classical
  let V' := V ∩ (fun y => Φ (s, y)) ⁻¹' W
  have hs' : s ∈ Ioo (-δ) (s + δ) := ⟨by linarith, by linarith⟩
  have hΦs (y : M) (hy : y ∈ V) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun z => Φ (s, z)) y :=
    (hΦ.smooth.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨hs', hy⟩)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)
  have hV'o : IsOpen V' := (show ContinuousOn (fun y => Φ (s, y)) V from
    fun y hy => (hΦs y hy).continuousAt.continuousWithinAt).isOpen_inter_preimage hV hW
  let ε := min δ (τ - d) / 2
  have hε : 0 < ε := half_pos (lt_min hδ (sub_pos.mpr hsmall))
  have hεδ : ε < δ := (half_lt_self (lt_min hδ (sub_pos.mpr hsmall))).trans_le (min_le_left _ _)
  have hετ : d + ε < τ := by
    have he : ε < τ - d :=
      (half_lt_self (lt_min hδ (sub_pos.mpr hsmall))).trans_le (min_le_right _ _)
    linarith
  let η := min δ τ / 2
  have hη : 0 < η := half_pos (lt_min hδ hτ)
  have hηδ : η < δ := (half_lt_self (lt_min hδ hτ)).trans_le (min_le_left _ _)
  have hητ : η < τ := (half_lt_self (lt_min hδ hτ)).trans_le (min_le_right _ _)
  let Q : ℝ × M → M := fun p => Ψ (p.1 - s, Φ (s, p.2))
  have hQs (y : M) (hy : y ∈ V') : Q (s, y) = Φ (s, y) := by
    simpa only [Q, sub_self] using hΨ.initial _ hy.2
  have hQorbit (y : M) (hy : y ∈ V') :
      IsMIntegralCurveOn (I := 𝓡 n) (fun t => Q (t, y))
        (D.normalizedGradient f) {t | t - s ∈ Ioo (-τ) τ} := by
    simpa only [Q, Function.comp_def, sub_eq_add_neg] using (hΨ.orbit _ hy.2).comp_add (-s)
  have hQd (t : ℝ) (y : M) (hy : y ∈ V') (ht : t - s ∈ Ioo (-τ) τ) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Q (t, y) := by
    have hsecond : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
        (fun p : ℝ × M => Φ (s, p.2)) (t, y) :=
      (hΦ.smooth.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨hs', hy.1⟩)).comp
        (t, y) (contMDiffAt_const.prodMk contMDiffAt_snd)
    have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun p : ℝ × M => (p.1 - s, Φ (s, p.2))) (t, y) :=
      (contMDiffAt_fst.sub contMDiffAt_const).prodMk hsecond
    exact (hΨ.smooth.contMDiffAt ((isOpen_Ioo.prod hW).mem_nhds
      (show (t - s, Φ (s, y)) ∈ Ioo (-τ) τ ×ˢ W from ⟨ht, hy.2⟩))).comp (t, y) hpair
  have heq (y : M) (hy : y ∈ V') :
      EqOn (fun t => Φ (t, y)) (fun t => Q (t, y)) (Ioo (s - η) (s + η)) := by
    have hleft : Ioo (s - η) (s + η) ⊆ Ioo (-δ) (s + δ) := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hright : Ioo (s - η) (s + η) ⊆ {t | t - s ∈ Ioo (-τ) τ} := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    exact integralCurve_eqOn_Ioo_of_contMDiffOn hU hX ⟨by linarith, by linarith⟩
      (fun t ht => hΦ.stays y hy.1 t (hleft ht))
      ((hΦ.orbit y hy.1).mono hleft) ((hQorbit y hy).mono hright) (hQs y hy).symm
  let Ξ : ℝ × M → M := fun p => if p.1 ≤ s then Φ p else Q p
  have heleft : EqOn Ξ Φ (Ioo (-ε) (s + η) ×ˢ V') := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    by_cases hts : t ≤ s
    · exact if_pos hts
    · exact (if_neg hts).trans (heq y hy ⟨by linarith, ht.2⟩).symm
  have heright : EqOn Ξ Q (Ioo (s - η) (s + d + ε) ×ˢ V') := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    by_cases hts : t ≤ s
    · exact (if_pos hts).trans (heq y hy ⟨ht.1, by linarith⟩)
    · exact if_neg hts
  refine ⟨hV'o, ε, hε, Ξ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨t, y⟩ ⟨ht, hy⟩
    by_cases hts : t ≤ s
    · have hti : t ∈ Ioo (-δ) (s + δ) := ⟨by linarith [ht.1], by linarith⟩
      have he : Ξ =ᶠ[𝓝 (t, y)] Φ :=
        Filter.Eventually.mono ((isOpen_Ioo.prod hV'o).mem_nhds
          (show (t, y) ∈ Ioo (-ε) (s + η) ×ˢ V' from ⟨⟨ht.1, by linarith⟩, hy⟩))
          fun p hp => heleft hp
      exact ((hΦ.smooth.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨hti, hy.1⟩)).congr_of_eventuallyEq
        he).contMDiffWithinAt
    · have hti : t - s ∈ Ioo (-τ) τ := ⟨by linarith, by linarith [ht.2]⟩
      have he : Ξ =ᶠ[𝓝 (t, y)] Q :=
        Filter.Eventually.mono ((isOpen_Ioo.prod hV'o).mem_nhds
          (show (t, y) ∈ Ioo (s - η) (s + d + ε) ×ˢ V' from
            ⟨⟨by linarith, ht.2⟩, hy⟩)) fun p hp => heright hp
      exact ((hQd t y hy hti).congr_of_eventuallyEq he).contMDiffWithinAt
  · intro y hy
    change (if (0 : ℝ) ≤ s then Φ (0, y) else Q (0, y)) = y
    rw [if_pos hs, hΦ.initial y hy.1]
  · intro y hy t ht
    by_cases hts : t ≤ s
    · change (if t ≤ s then Φ (t, y) else Q (t, y)) ∈ U
      rw [if_pos hts]
      exact hΦ.stays y hy.1 t ⟨by linarith [ht.1], by linarith⟩
    · change (if t ≤ s then Φ (t, y) else Q (t, y)) ∈ U
      rw [if_neg hts]
      exact hΨ.stays _ hy.2 (t - s) ⟨by linarith, by linarith [ht.2]⟩
  · intro y hy t ht
    by_cases hts : t ≤ s
    · have hti : t ∈ Ioo (-δ) (s + δ) := ⟨by linarith [ht.1], by linarith⟩
      have he : (fun r => Ξ (r, y)) =ᶠ[𝓝 t] (fun r => Φ (r, y)) := by
        filter_upwards [Ioo_mem_nhds ht.1 (show t < s + η by linarith)] with r hr
        exact heleft ⟨hr, hy⟩
      have hd' := ((hΦ.orbit y hy.1).isMIntegralCurveAt
        (isOpen_Ioo.mem_nhds hti)).hasMFDerivAt.congr_of_eventuallyEq he
      convert! hd'.hasMFDerivWithinAt using 1
      dsimp only
      rw [show Ξ (t, y) = Φ (t, y) from if_pos hts]
    · have hti : t - s ∈ Ioo (-τ) τ := ⟨by linarith, by linarith [ht.2]⟩
      have he : (fun r => Ξ (r, y)) =ᶠ[𝓝 t] (fun r => Q (r, y)) := by
        filter_upwards [Ioo_mem_nhds (show s - η < t by linarith) ht.2] with r hr
        exact heright ⟨hr, hy⟩
      have hn : {r : ℝ | r - s ∈ Ioo (-τ) τ} ∈ 𝓝 t :=
        (isOpen_Ioo.preimage (continuous_id.sub continuous_const)).mem_nhds hti
      have hd' := ((hQorbit y hy).isMIntegralCurveAt hn).hasMFDerivAt.congr_of_eventuallyEq he
      convert! hd'.hasMFDerivWithinAt using 1
      dsimp only
      rw [show Ξ (t, y) = Q (t, y) from if_neg hts]
  · intro y hy t ht
    by_cases hts : t ≤ s
    · rw [show Ξ (t, y) = Φ (t, y) from if_pos hts]
      exact hΦ.level y hy.1 t ⟨ht.1, by linarith⟩
    · rw [show Ξ (t, y) = Ψ (t - s, Φ (s, y)) from if_neg hts,
        hΨ.level _ hy.2 (t - s) ⟨by linarith, by linarith [ht.2]⟩,
        hΦ.level y hy.1 s ⟨hs, by linarith⟩]
      ring
  · intro y hy t ht v hv
    by_cases hts : t ≤ s
    · have he : (fun z => Ξ (t, z)) = (fun z => Φ (t, z)) := by
        funext z
        exact if_pos hts
      rw [he, show Ξ (t, y) = Φ (t, y) from if_pos hts]
      exact hΦ.expansion y hy.1 t ⟨ht.1, by linarith⟩ v hv
    · have htime : t - s ∈ Ico 0 τ := ⟨by linarith, by linarith [ht.2]⟩
      have he : (fun z => Ξ (t, z)) = (fun z => Ψ (t - s, Φ (s, z))) := by
        funext z
        exact if_neg hts
      rw [he, show Ξ (t, y) = Ψ (t - s, Φ (s, y)) from if_neg hts]
      let w := mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (s, z)) y v
      have hw : mvfderiv (𝓡 n) f (Φ (s, y)) w = 0 :=
        hΦ.tangent hU hf hV (by linarith only [hδ]) (by linarith only [hs, hδ])
          hy.1 ⟨hs, by linarith only [hδ]⟩ v hv
      have hΨt : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun z => Ψ (t - s, z)) (Φ (s, y)) :=
        (hΨ.smooth.contMDiffAt ((isOpen_Ioo.prod hW).mem_nhds
          (show (t - s, Φ (s, y)) ∈ Ioo (-τ) τ ×ˢ W from
            ⟨⟨by linarith [htime.1], htime.2⟩, hy.2⟩))).comp (Φ (s, y))
          (contMDiffAt_const.prodMk contMDiffAt_id)
      have hdv := congrArg (fun L => L v) (mfderiv_comp y
        (hΨt.mdifferentiableAt (by simp)) ((hΦs y hy.1).mdifferentiableAt (by simp)))
      change mfderiv (𝓡 n) (𝓡 n) (fun z => Ψ (t - s, Φ (s, z))) y v =
        mfderiv (𝓡 n) (𝓡 n) (fun z => Ψ (t - s, z)) (Φ (s, y)) w at hdv
      rw [hdv]
      have hlast := hΨ.expansion _ hy.2 (t - s) htime w hw
      have hfirst := hΦ.expansion y hy.1 s ⟨hs, by linarith⟩ v hv
      apply hlast.trans
      calc
        g.inner (Φ (s, y)) w w * Real.exp (2 * (H / l ^ 2) * (t - s))
            ≤ (g.inner y v v * Real.exp (2 * (H / l ^ 2) * s)) *
              Real.exp (2 * (H / l ^ 2) * (t - s)) :=
          mul_le_mul_of_nonneg_right hfirst (Real.exp_pos _).le
        _ = g.inner y v v * Real.exp (2 * (H / l ^ 2) * t) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

end PoincareConjecture.LeviCivitaData



theorem PoincareConjecture.LeviCivitaData.exists_uniform_normalizedGradient_manifoldFlow_on_compact_band
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient f y))
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) f y v = 0 → D.hessian f y v v ≤ H * g.inner y v v)
    {a b : ℝ} (hband : IsCompact {y | y ∈ U ∧ f y ∈ Icc a b})
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U)
    {T : ℝ} (hT : 0 ≤ T)
    (hlower : ∀ x ∈ K, a ≤ f x) (hupper : ∀ x ∈ K, f x + T ≤ b) :
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ
        (Ioo (-δ) (T + δ) ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      (∀ y ∈ V, (∀ t ∈ Ioo (-δ) (T + δ), Φ (t, y) ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y))
          (D.normalizedGradient f) (Ioo (-δ) (T + δ))) ∧
      ∀ y ∈ V, ∀ t ∈ Icc 0 T,
        f (Φ (t, y)) = f y + t ∧
        ∀ v : TangentSpace (𝓡 n) y, mvfderiv (𝓡 n) f y v = 0 →
          g.inner (Φ (t, y)) (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v)
            (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v) ≤
          g.inner y v v * Real.exp (2 * (H / l ^ 2) * t) := by
  let S : Set M := {y | y ∈ U ∧ f y ∈ Icc a b}
  obtain ⟨W, τ, Ψ, hW, hSW, hτ, hΨ⟩ :=
    exists_uniform_short_expandingFlow D hU hf hl hH hgrad hhess hband
      (show S ⊆ U from fun _ hy => hy.1)
  obtain ⟨V₀, δ₀, Φ₀, hV₀, hKV₀, hδ₀, hΦ₀⟩ :=
    exists_uniform_short_expandingFlow D hU hf hl hH hgrad hhess hK hKU
  have hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1
      (T% (D.normalizedGradient f)) U := by
    intro y hy
    have hr : g.inner y (D.gradient f y) (D.gradient f y) ≠ 0 := by
      intro hz
      have hn : g.tangentNorm y (D.gradient f y) = 0 := by
        simp only [RiemannianMetric.tangentNorm, hz, Real.sqrt_zero]
      linarith [hgrad y hy]
    exact ((contMDiffAt_normalizedGradient D (hf.contMDiffAt (hU.mem_nhds hy)) hr).of_le
      (by simp)).contMDiffWithinAt
  obtain ⟨N, hN⟩ := exists_nat_gt (T / τ)
  have hNp : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hT hτ.le) hN
  let d := T / N
  let s : ℕ → ℝ := fun i => i * d
  have hd : 0 ≤ d := div_nonneg hT hNp.le
  have hsmall : d < τ := by
    apply (div_lt_iff₀ hNp).mpr
    have he := (div_lt_iff₀ hτ).mp hN
    nlinarith
  have hs0 : s 0 = 0 := by simp only [s, Nat.cast_zero, zero_mul]
  have hsN : s N = T := by dsimp only [s, d]; field_simp
  have hspos (i : ℕ) : 0 ≤ s i := mul_nonneg (Nat.cast_nonneg _) hd
  have hsle (i : ℕ) (hi : i ≤ N) : s i ≤ T := by
    rw [← hsN]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hd
  have hsstep (i : ℕ) : s (i + 1) = s i + d := by dsimp only [s]; push_cast; ring
  have hconstruct : ∀ i, i ≤ N →
      ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
        IsOpen V ∧ K ⊆ V ∧ 0 < δ ∧ ExpandingFlow D f U V l H (-δ) (s i + δ) Φ := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨V₀, δ₀, Φ₀, hV₀, hKV₀, hδ₀, by simpa only [hs0, zero_add] using hΦ₀⟩
    | succ i ih =>
      intro hi
      obtain ⟨V, δ, Φ, hV, hKV, hδ, hΦ⟩ := ih (Nat.le_of_succ_le hi)
      obtain ⟨hV', ε, hε, Ξ, hΞ⟩ :=
        hΦ.extend hU hf hX hV hW (hspos i) hd hδ hτ hsmall hΨ
      refine ⟨V ∩ (fun y => Φ (s i, y)) ⁻¹' W, ε, Ξ, hV', ?_, hε, ?_⟩
      · intro y hy
        refine ⟨hKV hy, hSW ?_⟩
        have hsi : s i ∈ Ico 0 (s i + δ) := ⟨hspos i, by linarith⟩
        refine ⟨hΦ.stays y (hKV hy) (s i) ⟨by linarith [hspos i], hsi.2⟩, ?_⟩
        rw [hΦ.level y (hKV hy) (s i) hsi]
        exact ⟨by linarith [hlower y hy, hspos i],
          by linarith [hupper y hy, hsle i (Nat.le_of_succ_le hi)]⟩
      · simpa only [hsstep] using hΞ
  obtain ⟨V, δ, Φ, hV, hKV, hδ, hΦ⟩ := hconstruct N le_rfl
  rw [hsN] at hΦ
  refine ⟨V, δ, Φ, hV, hKV, ?_, hδ, hΦ.smooth, hΦ.initial, ?_, ?_⟩
  · intro y hy
    simpa only [hΦ.initial y hy] using hΦ.stays y hy 0 ⟨by linarith, by linarith⟩
  · exact fun y hy => ⟨hΦ.stays y hy, hΦ.orbit y hy⟩
  · intro y hy t ht
    have ht' : t ∈ Ico 0 (T + δ) := ⟨ht.1, by linarith [ht.2]⟩
    exact ⟨hΦ.level y hy t ht', hΦ.expansion y hy t ht'⟩


theorem PoincareConjecture.LeviCivitaData.exists_uniform_normalizedGradient_manifoldFlow_on_compact_buffer
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient f y))
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) f y v = 0 → D.hessian f y v v ≤ H * g.inner y v v)
    {K S : Set M} (hK : IsCompact K) (hS : IsCompact S)
    (hKS : K ⊆ S) (hSU : S ⊆ U)
    {T : ℝ} (hT : 0 ≤ T)
    (hbuffer : ∀ x ∈ K, ∀ y, g.edist x y ≤ ENNReal.ofReal (T / l) → y ∈ S) :
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ
        (Ioo (-δ) (T + δ) ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      (∀ y ∈ V, (∀ t ∈ Ioo (-δ) (T + δ), Φ (t, y) ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y))
          (D.normalizedGradient f) (Ioo (-δ) (T + δ))) ∧
      ∀ y ∈ V, ∀ t ∈ Icc 0 T,
        f (Φ (t, y)) = f y + t ∧
        g.edist y (Φ (t, y)) ≤ ENNReal.ofReal (t / l) ∧
        ∀ v : TangentSpace (𝓡 n) y, mvfderiv (𝓡 n) f y v = 0 →
          g.inner (Φ (t, y)) (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v)
            (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v) ≤
          g.inner y v v * Real.exp (2 * (H / l ^ 2) * t) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hKU : K ⊆ U := hKS.trans hSU
  obtain ⟨W, τ, Ψ, hW, hSW, hτ, hΨ⟩ :=
    exists_uniform_short_expandingFlow D hU hf hl hH hgrad hhess hS hSU
  obtain ⟨V₀, δ₀, Φ₀, hV₀, hKV₀, hδ₀, hΦ₀⟩ :=
    exists_uniform_short_expandingFlow D hU hf hl hH hgrad hhess hK hKU
  have hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1
      (T% (D.normalizedGradient f)) U := by
    intro y hy
    have hr : g.inner y (D.gradient f y) (D.gradient f y) ≠ 0 := by
      intro hz
      have hn : g.tangentNorm y (D.gradient f y) = 0 := by
        simp only [RiemannianMetric.tangentNorm, hz, Real.sqrt_zero]
      linarith [hgrad y hy]
    exact ((contMDiffAt_normalizedGradient D (hf.contMDiffAt (hU.mem_nhds hy)) hr).of_le
      (by simp)).contMDiffWithinAt
  obtain ⟨N, hN⟩ := exists_nat_gt (T / τ)
  have hNp : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hT hτ.le) hN
  let d := T / N
  let s : ℕ → ℝ := fun i => i * d
  have hd : 0 ≤ d := div_nonneg hT hNp.le
  have hsmall : d < τ := by
    apply (div_lt_iff₀ hNp).mpr
    have he := (div_lt_iff₀ hτ).mp hN
    nlinarith
  have hs0 : s 0 = 0 := by simp only [s, Nat.cast_zero, zero_mul]
  have hsN : s N = T := by dsimp only [s, d]; field_simp
  have hspos (i : ℕ) : 0 ≤ s i := mul_nonneg (Nat.cast_nonneg _) hd
  have hsle (i : ℕ) (hi : i ≤ N) : s i ≤ T := by
    rw [← hsN]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hd
  have hsstep (i : ℕ) : s (i + 1) = s i + d := by dsimp only [s]; push_cast; ring
  have hconstruct : ∀ i, i ≤ N →
      ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
        IsOpen V ∧ K ⊆ V ∧ 0 < δ ∧ ExpandingFlow D f U V l H (-δ) (s i + δ) Φ := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨V₀, δ₀, Φ₀, hV₀, hKV₀, hδ₀, by simpa only [hs0, zero_add] using hΦ₀⟩
    | succ i ih =>
      intro hi
      obtain ⟨V, δ, Φ, hV, hKV, hδ, hΦ⟩ := ih (Nat.le_of_succ_le hi)
      obtain ⟨hV', ε, hε, Ξ, hΞ⟩ :=
        hΦ.extend hU hf hX hV hW (hspos i) hd hδ hτ hsmall hΨ
      refine ⟨V ∩ (fun y => Φ (s i, y)) ⁻¹' W, ε, Ξ, hV', ?_, hε, ?_⟩
      · intro y hy
        refine ⟨hKV hy, hSW ?_⟩
        have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞
            (fun t => Φ (t, y)) (Ioo (-δ) (s i + δ)) := by
          apply hΦ.smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
          exact fun t ht => ⟨ht, hKV hy⟩
        have hdist := D.edist_le_of_normalizedGradient_curve isOpen_Ioo hcurve
          (hΦ.orbit y (hKV hy)) hl (hspos i)
          (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
          (fun t ht => hgrad _ (hΦ.stays y (hKV hy) t ht))
        rw [hΦ.initial y (hKV hy), sub_zero] at hdist
        exact hbuffer y hy _ (hdist.trans (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (hsle i (Nat.le_of_succ_le hi)) hl.le)))
      · simpa only [hsstep] using hΞ
  obtain ⟨V, δ, Φ, hV, hKV, hδ, hΦ⟩ := hconstruct N le_rfl
  rw [hsN] at hΦ
  refine ⟨V, δ, Φ, hV, hKV, ?_, hδ, hΦ.smooth, hΦ.initial, ?_, ?_⟩
  · intro y hy
    simpa only [hΦ.initial y hy] using hΦ.stays y hy 0 ⟨by linarith, by linarith⟩
  · exact fun y hy => ⟨hΦ.stays y hy, hΦ.orbit y hy⟩
  · intro y hy t ht
    have ht' : t ∈ Ico 0 (T + δ) := ⟨ht.1, by linarith [ht.2]⟩
    refine ⟨hΦ.level y hy t ht', ?_, hΦ.expansion y hy t ht'⟩
    have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞
        (fun s => Φ (s, y)) (Ioo (-δ) (T + δ)) :=
      hΦ.smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
        (fun s hs => ⟨hs, hy⟩)
    have hdist := D.edist_le_of_normalizedGradient_curve isOpen_Ioo hcurve
      (hΦ.orbit y hy) hl ht.1
      (fun s (hs : s ∈ Icc 0 t) => ⟨by linarith [hs.1], by linarith [hs.2, ht.2]⟩)
      (fun s hs => hgrad _ (hΦ.stays y hy s hs))
    simpa only [hΦ.initial y hy, sub_zero] using hdist



theorem PoincareConjecture.LeviCivitaData.exists_uniform_normalizedGradient_manifoldFlow_on_closedBall
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient f y))
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) f y v = 0 → D.hessian f y v v ≤ H * g.inner y v v)
    (hcomplete : PoincareConjecture.MetricComplete g) (p : M)
    {r R T : ℝ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hroom : r + T / l ≤ R)
    (hball : {y | g.edist p y ≤ ENNReal.ofReal R} ⊆ U) :
    ∃ (V : Set M) (δ : ℝ) (Φ : ℝ × M → M),
      IsOpen V ∧ {y | g.edist p y ≤ ENNReal.ofReal r} ⊆ V ∧ V ⊆ U ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ Φ
        (Ioo (-δ) (T + δ) ×ˢ V) ∧
      (∀ y ∈ V, Φ (0, y) = y) ∧
      (∀ y ∈ V, (∀ t ∈ Ioo (-δ) (T + δ), Φ (t, y) ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y))
          (D.normalizedGradient f) (Ioo (-δ) (T + δ))) ∧
      ∀ y ∈ V, ∀ t ∈ Icc 0 T,
        f (Φ (t, y)) = f y + t ∧
        ∀ v : TangentSpace (𝓡 n) y, mvfderiv (𝓡 n) f y v = 0 →
          g.inner (Φ (t, y)) (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v)
            (mfderiv (𝓡 n) (𝓡 n) (fun z => Φ (t, z)) y v) ≤
          g.inner y v v * Real.exp (2 * (H / l ^ 2) * t) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hrR : r ≤ R := by linarith [div_nonneg hT hl.le]
  obtain ⟨V, δ, Φ, hV, hKV, hVU, hδ, hs, hi, ho, hb⟩ :=
    D.exists_uniform_normalizedGradient_manifoldFlow_on_compact_buffer hU hf hl hH
      hgrad hhess (g.isCompact_closedBall_of_metricComplete hcomplete p r)
      (g.isCompact_closedBall_of_metricComplete hcomplete p R)
      (fun y hy => hy.trans (ENNReal.ofReal_le_ofReal hrR)) hball hT (by
        intro x hx y hy
        have htri : g.edist p y ≤ g.edist p x + g.edist x y :=
          Manifold.riemannianEDist_triangle
        apply (htri.trans (add_le_add hx hy)).trans
        rw [← ENNReal.ofReal_add hr (div_nonneg hT hl.le)]
        exact ENNReal.ofReal_le_ofReal hroom)
  exact ⟨V, δ, Φ, hV, hKV, hVU, hδ, hs, hi, ho,
    fun y hy t ht => ⟨(hb y hy t ht).1, (hb y hy t ht).2.2⟩⟩

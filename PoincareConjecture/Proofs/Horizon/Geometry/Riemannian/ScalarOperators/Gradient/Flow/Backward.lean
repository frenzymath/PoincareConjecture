import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.CompactBand
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.LevelEvolution

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Function
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [T3Space M] in
private theorem normalizedGradient_contMDiffAt
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

private theorem uniform_short_curves_on_compact
    (D : LeviCivitaData g) {f : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient f y))
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) f y v = 0 → D.hessian f y v v ≤ H * g.inner y v v)
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∃ γ : ℝ → M, γ 0 = x ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-δ) δ) ∧
      (∀ t ∈ Ioo (-δ) δ, γ t ∈ U) ∧
      IsMIntegralCurveOn (I := 𝓡 n) γ (D.normalizedGradient f) (Ioo (-δ) δ) := by
  let P : Set M → Prop := fun A =>
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ A, ∃ γ : ℝ → M, γ 0 = x ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-δ) δ) ∧
      (∀ t ∈ Ioo (-δ) δ, γ t ∈ U) ∧
      IsMIntegralCurveOn (I := 𝓡 n) γ (D.normalizedGradient f) (Ioo (-δ) δ)
  change P K
  refine hK.induction_on (p := P) ?_ ?_ ?_ ?_
  · exact ⟨1, zero_lt_one, fun _ hx => False.elim hx⟩
  · rintro A B hAB ⟨δ, hδ, hcurves⟩
    exact ⟨δ, hδ, fun x hx => hcurves x (hAB hx)⟩
  · rintro A B ⟨δ, hδ, hA⟩ ⟨ε, hε, hB⟩
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨γ, hzero, hs, hst, ho⟩ := hA x hx
      have hsub : Ioo (-(min δ ε)) (min δ ε) ⊆ Ioo (-δ) δ :=
        Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
      exact ⟨γ, hzero, hs.mono hsub, fun t ht => hst t (hsub ht), ho.mono hsub⟩
    · obtain ⟨γ, hzero, hs, hst, ho⟩ := hB x hx
      have hsub : Ioo (-(min δ ε)) (min δ ε) ⊆ Ioo (-ε) ε :=
        Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
      exact ⟨γ, hzero, hs.mono hsub, fun t ht => hst t (hsub ht), ho.mono hsub⟩
  · intro x hx
    obtain ⟨V, δ, Φ, hV, hxV, _, hδ, hs, hi, hd, _⟩ :=
      D.exists_local_normalizedGradient_manifoldFlow_with_expansion
        hU hf hl hH hgrad hhess (hKU hx)
    refine ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), δ, hδ, ?_⟩
    intro y hy
    refine ⟨fun t => Φ (t, y), hi y hy, ?_, (hd y hy).1, (hd y hy).2⟩
    exact hs.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun t ht => ⟨ht, hy⟩)
end PoincareConjecture.LeviCivitaData
namespace PoincareConjecture.LeviCivitaData
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [T3Space M] in
private theorem smooth_integralCurve_piecewise
    {X : (x : M) → TangentSpace (𝓡 n) x}
    {α β : ℝ → M} {A B J : Set ℝ} {c : ℝ}
    (hA : IsOpen A) (hB : IsOpen B) (_hJ : IsOpen J)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ α A)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ β B)
    (hoα : IsMIntegralCurveOn (I := 𝓡 n) α X A)
    (hoβ : IsMIntegralCurveOn (I := 𝓡 n) β X B)
    (hcA : c ∈ A) (hcB : c ∈ B) (he : α c = β c)
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% X) (α c))
    (hleft : ∀ t ∈ J, t ≤ c → t ∈ B)
    (hright : ∀ t ∈ J, c ≤ t → t ∈ A) :
    let γ := fun t => if t ≤ c then β t else α t
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ J ∧
      IsMIntegralCurveOn (I := 𝓡 n) γ X J := by
  let γ := fun t => if t ≤ c then β t else α t
  have hlocal (t : ℝ) (ht : t ∈ J) :
      ∃ θ : ℝ → M, γ =ᶠ[𝓝 t] θ ∧
        ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ θ t ∧ IsMIntegralCurveAt (I := 𝓡 n) θ X t := by
    rcases lt_trichotomy t c with htc | htc | htc
    · have htB := hleft t ht htc.le
      refine ⟨β, ?_, hβ.contMDiffAt (hB.mem_nhds htB),
        hoβ.isMIntegralCurveAt (hB.mem_nhds htB)⟩
      filter_upwards [Iio_mem_nhds htc] with s hs
      exact if_pos hs.le
    · subst t
      have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless hX
        (hoα.isMIntegralCurveAt (hA.mem_nhds hcA))
        (hoβ.isMIntegralCurveAt (hB.mem_nhds hcB)) he
      refine ⟨α, ?_, hα.contMDiffAt (hA.mem_nhds hcA),
        hoα.isMIntegralCurveAt (hA.mem_nhds hcA)⟩
      filter_upwards [heq] with s hs
      dsimp only [γ]
      split_ifs with hsc
      · exact hs.symm
      · rfl
    · have htA := hright t ht htc.le
      refine ⟨α, ?_, hα.contMDiffAt (hA.mem_nhds htA),
        hoα.isMIntegralCurveAt (hA.mem_nhds htA)⟩
      filter_upwards [Ioi_mem_nhds htc] with s hs
      exact if_neg (not_le.mpr hs)
  constructor
  · intro t ht
    obtain ⟨θ, heq, hs, _⟩ := hlocal t ht
    exact (hs.congr_of_eventuallyEq heq).contMDiffWithinAt
  · change IsMIntegralCurveOn (I := 𝓡 n) γ X J
    intro t ht
    obtain ⟨θ, heq, _, ho⟩ := hlocal t ht
    have hd := ho.hasMFDerivAt.congr_of_eventuallyEq heq
    convert! (hd.hasMFDerivWithinAt (s := J)) using 1
    rw [heq.self_of_nhds]
end PoincareConjecture.LeviCivitaData

theorem PoincareConjecture.LeviCivitaData.exists_normalizedGradient_curve_ending_at_of_isCompact_closedBall
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hgrad : ∀ y ∈ U, l ≤ g.tangentNorm y (D.gradient f y))
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      mvfderiv (𝓡 n) f y v = 0 → D.hessian f y v v ≤ H * g.inner y v v)
    (x : M) {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (hroom : T / l ≤ R)
    (hcompact : IsCompact {y | g.edist x y ≤ ENNReal.ofReal R})
    (hball : {y | g.edist x y ≤ ENNReal.ofReal R} ⊆ U) :
    ∃ (ε : ℝ) (γ : ℝ → M), 0 < ε ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-ε) (T + ε)) ∧
      γ T = x ∧
      (∀ t ∈ Ioo (-ε) (T + ε), γ t ∈ U) ∧
      IsMIntegralCurveOn (I := 𝓡 n) γ (D.normalizedGradient f)
        (Ioo (-ε) (T + ε)) ∧
      ∀ t ∈ Icc 0 T, f (γ t) = f x - T + t ∧
        g.edist (γ t) x ≤ ENNReal.ofReal ((T - t) / l) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hregular (y : M) (hy : y ∈ U) :
      g.inner y (D.gradient f y) (D.gradient f y) ≠ 0 := by
    intro hz
    have hn : g.tangentNorm y (D.gradient f y) = 0 := by
      simp only [RiemannianMetric.tangentNorm, hz, Real.sqrt_zero]
    linarith [hgrad y hy]
  have hX (y : M) (hy : y ∈ U) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1
        (T% (D.normalizedGradient f)) y :=
    (normalizedGradient_contMDiffAt D (hf.contMDiffAt (hU.mem_nhds hy))
      (hregular y hy)).of_le (by simp)
  obtain ⟨τ, hτ, hshort⟩ := uniform_short_curves_on_compact D hU hf hl hH
    hgrad hhess hcompact hball
  have hxball : g.edist x x ≤ ENNReal.ofReal R := by
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
    simpa only [ENNReal.ofReal_zero] using ENNReal.ofReal_le_ofReal hR
  obtain ⟨α₀, hα₀, hs₀, hu₀, ho₀⟩ := hshort x hxball
  obtain ⟨N, hN⟩ := exists_nat_gt (T / τ)
  have hNp : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hT hτ.le) hN
  let d := T / N
  let s : ℕ → ℝ := fun i => i * d
  have hd : 0 ≤ d := div_nonneg hT hNp.le
  have hdτ : d < τ := by
    apply (div_lt_iff₀ hNp).mpr
    have he := (div_lt_iff₀ hτ).mp hN
    nlinarith
  have hs0 : s 0 = 0 := by simp only [s, Nat.cast_zero, zero_mul]
  have hsN : s N = T := by dsimp only [s, d]; field_simp
  have hspos (i : ℕ) : 0 ≤ s i := mul_nonneg (Nat.cast_nonneg _) hd
  have hsle (i : ℕ) (hi : i ≤ N) : s i ≤ T := by
    rw [← hsN]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hd
  have hsstep (i : ℕ) : s (i + 1) = s i + d := by
    dsimp only [s]
    push_cast
    ring
  have hconstruct : ∀ i, i ≤ N →
      ∃ (ε : ℝ) (α : ℝ → M), 0 < ε ∧ α 0 = x ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ α (Ioo (-s i - ε) ε) ∧
        (∀ t ∈ Ioo (-s i - ε) ε, α t ∈ U) ∧
        IsMIntegralCurveOn (I := 𝓡 n) α (D.normalizedGradient f)
          (Ioo (-s i - ε) ε) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨τ, α₀, hτ, hα₀, by simpa only [hs0, neg_zero, zero_sub] using hs₀,
        by simpa only [hs0, neg_zero, zero_sub] using hu₀,
        by simpa only [hs0, neg_zero, zero_sub] using ho₀⟩
    | succ i ih =>
      intro hi
      obtain ⟨ε, α, hε, hα, hsα, huα, hoα⟩ := ih (Nat.le_of_succ_le hi)
      have hsi : -s i ∈ Ioo (-s i - ε) ε := ⟨by linarith, by linarith [hspos i]⟩
      have hdist := D.edist_le_of_normalizedGradient_curve isOpen_Ioo hsα hoα hl
        (neg_nonpos.mpr (hspos i))
        (fun t (ht : t ∈ Icc (-s i) 0) => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        (fun t ht => hgrad _ (huα t ht))
      rw [hα, zero_sub, neg_neg] at hdist
      have hballi : g.edist x (α (-s i)) ≤ ENNReal.ofReal R := by
        have hsym : g.edist x (α (-s i)) = g.edist (α (-s i)) x :=
          Manifold.riemannianEDist_comm
        rw [hsym]
        exact hdist.trans (ENNReal.ofReal_le_ofReal
          ((div_le_div_of_nonneg_right (hsle i (Nat.le_of_succ_le hi)) hl.le).trans hroom))
      obtain ⟨β, hβ, hsβ, huβ, hoβ⟩ := hshort (α (-s i)) hballi
      let η := min ε (τ - d) / 2
      have hη : 0 < η := half_pos (lt_min hε (sub_pos.mpr hdτ))
      have hηε : η ≤ ε := by dsimp only [η]; linarith [min_le_left ε (τ - d)]
      have hdη : d + η < τ := by dsimp only [η]; linarith [min_le_right ε (τ - d)]
      let B := Ioo (-τ - s i) (τ - s i)
      let J := Ioo (-s (i + 1) - η) η
      let β' := fun t => β (t + s i)
      have hsβ' : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ β' B := by
        apply hsβ.comp (contMDiff_id.add contMDiff_const).contMDiffOn
        intro t ht
        change -τ < t + s i ∧ t + s i < τ
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hoβ' : IsMIntegralCurveOn (I := 𝓡 n) β'
          (D.normalizedGradient f) B := by
        apply (isMIntegralCurveOn_comp_add.mpr hoβ).mono
        intro t ht
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have he : α (-s i) = β' (-s i) := by simp only [β', neg_add_cancel, hβ]
      have hleft (t : ℝ) (ht : t ∈ J) (htc : t ≤ -s i) : t ∈ B := by
        dsimp only [J] at ht
        rw [hsstep] at ht
        exact ⟨by linarith [ht.1], by linarith⟩
      have hright (t : ℝ) (ht : t ∈ J) (hct : -s i ≤ t) :
          t ∈ Ioo (-s i - ε) ε := ⟨by linarith, ht.2.trans_le hηε⟩
      obtain ⟨hsγ, hoγ⟩ := smooth_integralCurve_piecewise isOpen_Ioo isOpen_Ioo isOpen_Ioo
        hsα hsβ' hoα hoβ' hsi (show -s i ∈ B from ⟨by linarith, by linarith⟩) he (hX _ (huα _ hsi)) hleft hright
      let γ := fun t => if t ≤ -s i then β' t else α t
      refine ⟨η, γ, hη, ?_, hsγ, ?_, hoγ⟩
      · dsimp only [γ]
        split_ifs with hi0
        · have hsi0 : s i = 0 := by linarith [hspos i]
          simp only [β', zero_add, hsi0, hβ, neg_zero, hα]
        · exact hα
      · intro t ht
        dsimp only [γ]
        split_ifs with htc
        · apply huβ
          have htB := hleft t ht htc
          exact ⟨by linarith [htB.1], by linarith [htB.2]⟩
        · exact huα t (hright t ht (not_le.mp htc).le)
  obtain ⟨ε, α, hε, hα, hsα, huα, hoα⟩ := hconstruct N le_rfl
  rw [hsN] at hsα huα hoα
  let γ := fun t => α (t - T)
  have hsγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-ε) (T + ε)) := by
    apply hsα.comp (contMDiff_id.sub contMDiff_const).contMDiffOn
    intro t ht
    change -T - ε < t - T ∧ t - T < ε
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have huγ (t : ℝ) (ht : t ∈ Ioo (-ε) (T + ε)) : γ t ∈ U :=
    huα _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hoγ : IsMIntegralCurveOn (I := 𝓡 n) γ (D.normalizedGradient f)
      (Ioo (-ε) (T + ε)) := by
    apply (isMIntegralCurveOn_comp_sub.mpr hoα).mono
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hγT : γ T = x := by simp only [γ, sub_self, hα]
  refine ⟨ε, γ, hε, hsγ, hγT, huγ, hoγ, ?_⟩
  intro t ht
  have htI : t ∈ Ioo (-ε) (T + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hTI : T ∈ Ioo (-ε) (T + ε) := ⟨by linarith, by linarith⟩
  have hlevel := D.comp_normalizedGradient_eq_add_on isOpen_Ioo isPreconnected_Ioo
    (fun s hs => (hf.contMDiffAt (hU.mem_nhds (huγ s hs))).mdifferentiableAt (by simp))
    (fun s hs => hregular _ (huγ s hs)) hoγ hTI htI
  have hdist := D.edist_le_of_normalizedGradient_curve isOpen_Ioo hsγ hoγ hl ht.2
    (fun s (hs : s ∈ Icc t T) => ⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩)
    (fun s hs => hgrad _ (huγ s hs))
  rw [hγT] at hlevel hdist
  exact ⟨by linarith, hdist⟩

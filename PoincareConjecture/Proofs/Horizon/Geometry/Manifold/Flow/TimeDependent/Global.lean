import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.Continuation
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.Uniform

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {X : ℝ → (x : M) → TangentSpace (𝓡 n) x}

theorem exists_smooth_local_timeDependentFlow_on_interval
    {J : Set ℝ} (hJ : IsOpen J)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun tx : ℝ × M => (⟨tx.2, X tx.1 tx.2⟩ : TangentBundle (𝓡 n) M))
      (J ×ˢ univ))
    {a b s : ℝ} (hs : s ∈ Ioo a b) (habJ : Icc a b ⊆ J) (x : M)
    (hconf : ∃ K : Set M, IsCompact K ∧ ∀ (I : Set ℝ),
      IsOpen I → Convex ℝ I → s ∈ I → ∀ (γ : ℝ → M), γ s = x →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I →
        (∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) γ t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) →
        ∀ t ∈ I ∩ Icc a b, γ t ∈ K) :
    ∃ (V : Set M) (Φ : ℝ × M → M), IsOpen V ∧ x ∈ V ∧
      SmoothTimeDependentIntegralFamily X V (Ioo a b) Φ ∧
      ∀ y ∈ V, Φ (s, y) = y := by
  let L := s - a
  let R := b - s
  have hL : 0 < L := sub_pos.mpr hs.1
  have hR : 0 < R := sub_pos.mpr hs.2
  let T := fun r : ℝ => Ioo (s - r * L) (s + r * R)
  let S : Set ℝ := {r | 0 < r ∧ T r ⊆ J ∧ ∃ (V : Set M) (Φ : ℝ × M → M),
    IsOpen V ∧ x ∈ V ∧ SmoothTimeDependentIntegralFamily X V (T r) Φ ∧
      ∀ y ∈ V, Φ (s, y) = y}
  have hsT {r : ℝ} (hr : 0 < r) : s ∈ T r := by
    constructor <;> nlinarith [mul_pos hr hL, mul_pos hr hR]
  obtain ⟨V₀, δ₀, Φ₀, hV₀, hxV₀, hδ₀, hδ₀J, hΦ₀, hi₀, hd₀⟩ :=
    exists_smooth_local_timeDependentFlow hJ hX (habJ (Ioo_subset_Icc_self hs)) x
  let ε := δ₀ / (L + R + 1)
  have hden : 0 < L + R + 1 := by linarith
  have hε : 0 < ε := div_pos hδ₀ hden
  have heq : ε * (L + R + 1) = δ₀ := div_mul_cancel₀ _ hden.ne'
  have hεL : ε * L < δ₀ := by nlinarith [mul_pos hε hR]
  have hεR : ε * R < δ₀ := by nlinarith [mul_pos hε hL]
  have hεsub : T ε ⊆ Ioo (s - δ₀) (s + δ₀) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hεS : ε ∈ S := ⟨hε, hεsub.trans hδ₀J, V₀, Φ₀, hV₀, hxV₀,
    (show SmoothTimeDependentIntegralFamily X V₀ (Ioo (s - δ₀) (s + δ₀)) Φ₀ from
      ⟨hΦ₀, hd₀⟩).mono subset_rfl hεsub, hi₀⟩
  have hSne : S.Nonempty := ⟨ε, hεS⟩
  have hex : ∃ r ∈ S, 1 < r := by
    by_contra! hstop
    have hbounded : BddAbove S := ⟨1, hstop⟩
    let B := sSup S
    have hεB : ε ≤ B := le_csSup hbounded hεS
    have hB : 0 < B := hε.trans_le hεB
    have hB1 : B ≤ 1 := csSup_le hSne hstop
    obtain ⟨K, hK, hconfK⟩ := hconf
    obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_smooth_local_timeDependentFlows hJ hX
      (isCompact_Icc.prod hK) (prod_mono habJ (subset_univ K))
    let η := min (B / 2) (δ / (4 * (L + R + 1)))
    have hη : 0 < η := lt_min (half_pos hB) (div_pos hδ (by positivity))
    have hηB : η ≤ B / 2 := min_le_left _ _
    have hηδ : η * (4 * (L + R + 1)) ≤ δ :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hηL : 2 * η * L < δ := by nlinarith [mul_pos hη hL, mul_pos hη hR]
    have hηR : 2 * η * R < δ := by nlinarith [mul_pos hη hL, mul_pos hη hR]
    obtain ⟨r, hrS, hnear⟩ := Real.add_neg_lt_sSup hSne (ε := -η) (by linarith)
    have hrB : r ≤ B := le_csSup hbounded hrS
    obtain ⟨hr, hrJ, V, Φ, hV, hxV, hΦ, hiΦ⟩ := hrS
    let u := B - η
    let q := B + η
    let l := s - u * L
    let v := s + u * R
    have hu : 0 < u := by dsimp [u]; linarith
    have hur : u < r := by simpa only [u, sub_eq_add_neg] using hnear
    have hu1 : u ≤ 1 := by dsimp [u]; linarith
    have hlT : l ∈ T r := by
      dsimp [l, T]
      constructor <;> nlinarith [mul_pos hu hL, mul_pos hr hR]
    have hvT : v ∈ T r := by
      dsimp [v, T]
      constructor <;> nlinarith [mul_pos hr hL, mul_pos hu hR]
    have hlab : l ∈ Icc a b := by
      dsimp [l, L, R] at *
      constructor <;> nlinarith
    have hvab : v ∈ Icc a b := by
      dsimp [v, L, R] at *
      constructor <;> nlinarith
    have hcurveK : ∀ t ∈ T r ∩ Icc a b, Φ (t, x) ∈ K :=
      hconfK (T r) isOpen_Ioo (convex_Ioo _ _) (hsT hr) (fun t => Φ (t, x))
        (hiΦ x hxV) (hΦ.smooth_orbit hxV) (hΦ.orbit x hxV)
    obtain ⟨Wl, Ψl, hWl, hxWl, hlJ, hΨls, hil, hΨld⟩ :=
      hlocal (l, Φ (l, x)) ⟨hlab, hcurveK l ⟨hlT, hlab⟩⟩
    obtain ⟨Wr, Ψr, hWr, hxWr, hvJ, hΨrs, hir, hΨrd⟩ :=
      hlocal (v, Φ (v, x)) ⟨hvab, hcurveK v ⟨hvT, hvab⟩⟩
    have hΨl : SmoothTimeDependentIntegralFamily X Wl (Ioo (l - δ) (l + δ)) Ψl :=
      ⟨hΨls, hΨld⟩
    have hΨr : SmoothTimeDependentIntegralFamily X Wr (Ioo (v - δ) (v + δ)) Ψr :=
      ⟨hΨrs, hΨrd⟩
    let Vl := V ∩ (fun y => Φ (l, y)) ⁻¹' Wl
    let Vr := V ∩ (fun y => Φ (v, y)) ⁻¹' Wr
    let W := Vl ∩ Vr
    obtain ⟨hVl, hleft⟩ := hΦ.restart hV hWl isOpen_Ioo isOpen_Ioo hlT hΨl
    obtain ⟨hVr, hright⟩ := hΦ.restart hV hWr isOpen_Ioo isOpen_Ioo hvT hΨr
    have hW : IsOpen W := hVl.inter hVr
    have hxW : x ∈ W := ⟨⟨hxV, hxWl⟩, ⟨hxV, hxWr⟩⟩
    have hWV : W ⊆ V := fun _ hy => hy.1.1
    have hX₁ := hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
    obtain ⟨Θ, hΘ, heΘ, _⟩ := (hΦ.mono hWV subset_rfl).glue hX₁
      isOpen_Ioo (convex_Ioo _ _) hrJ isOpen_Ioo (convex_Ioo _ _) hW
      (hleft.mono inter_subset_left subset_rfl)
      (show l ∈ T r ∩ Ioo (l - δ) (l + δ) from
        ⟨hlT, ⟨by linarith, by linarith⟩⟩) (fun y hy => (hil _ hy.1.2).symm)
    have hsubL : Ioo (s - q * L) (s + r * R) ⊆ T r ∪ Ioo (l - δ) (l + δ) := by
      intro t ht
      by_cases hlo : s - r * L < t
      · exact Or.inl ⟨hlo, ht.2⟩
      · right
        dsimp [l, u, q] at *
        constructor <;> nlinarith [ht.1, ht.2]
    have hvL : v ∈ Ioo (s - q * L) (s + r * R) := by
      dsimp [v, q]
      constructor <;> nlinarith [mul_pos hu hR, mul_pos hB hL, mul_pos hη hL]
    have hLJ : Ioo (s - q * L) (s + r * R) ⊆ J :=
      hsubL.trans (union_subset hrJ hlJ)
    obtain ⟨Ξ, hΞ, heΞ, _⟩ := (hΘ.mono subset_rfl hsubL).glue hX₁
      isOpen_Ioo (convex_Ioo _ _) hLJ isOpen_Ioo (convex_Ioo _ _) hW
      (hright.mono inter_subset_right subset_rfl)
      (show v ∈ Ioo (s - q * L) (s + r * R) ∩ Ioo (v - δ) (v + δ) from
        ⟨hvL, ⟨by linarith, by linarith⟩⟩)
      (fun y hy => (heΘ ⟨hvT, hy⟩).trans (hir _ hy.2.2).symm)
    have hsubR : T q ⊆ Ioo (s - q * L) (s + r * R) ∪ Ioo (v - δ) (v + δ) := by
      intro t ht
      by_cases hhi : t < s + r * R
      · exact Or.inl ⟨ht.1, hhi⟩
      · right
        dsimp [v, u, q, T] at *
        constructor <;> nlinarith [ht.1, ht.2]
    have hq : 0 < q := by dsimp [q]; positivity
    have hsL : s ∈ Ioo (s - q * L) (s + r * R) := by
      constructor <;> nlinarith [mul_pos hq hL, mul_pos hr hR]
    have hqS : q ∈ S := by
      refine ⟨hq, hsubR.trans (union_subset hLJ hvJ), W, Ξ, hW, hxW,
        hΞ.mono subset_rfl hsubR, ?_⟩
      intro y hy
      exact (heΞ ⟨hsL, hy⟩).trans ((heΘ ⟨hsT hr, hy⟩).trans (hiΦ y (hWV hy)))
    have hqB := le_csSup hbounded hqS
    dsimp [q] at hqB
    linarith
  obtain ⟨r, ⟨_, _, V, Φ, hV, hxV, hΦ, hiΦ⟩, hr⟩ := hex
  refine ⟨V, Φ, hV, hxV, hΦ.mono subset_rfl ?_, hiΦ⟩
  intro t ht
  dsimp [T, L, R]
  constructor <;> nlinarith [ht.1, ht.2]

private theorem exists_Ioo_containing_pair {J : Set ℝ} (hJ : IsOpen J)
    (hcJ : Convex ℝ J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    ∃ a b : ℝ, s ∈ Ioo a b ∧ t ∈ Ioo a b ∧ Icc a b ⊆ J := by
  have hlo : min s t ∈ J := by rcases le_total s t with h | h <;> simp [h, hs, ht]
  have hhi : max s t ∈ J := by rcases le_total s t with h | h <;> simp [h, hs, ht]
  obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ.mem_nhds hlo)
  obtain ⟨l', r', hlr', hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hJ.mem_nhds hhi)
  let a := (l + min s t) / 2
  let b := (max s t + r') / 2
  have ha : a < min s t := by dsimp [a]; linarith [hlr.1]
  have hb : max s t < b := by dsimp [b]; linarith [hlr'.2]
  have haJ : a ∈ J := hsub ⟨by dsimp [a]; linarith [hlr.1], ha.trans hlr.2⟩
  have hbJ : b ∈ J := hsub' ⟨hlr'.1.trans hb, by dsimp [b]; linarith [hlr'.2]⟩
  exact ⟨a, b, ⟨ha.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hb⟩,
    ⟨ha.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hb⟩,
    hcJ.ordConnected.out haJ hbJ⟩

theorem exists_smooth_timeDependentFlow_from_anchor_of_compact_confinement
    {J : Set ℝ} (hJ : IsOpen J) (hcJ : Convex ℝ J)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun tx : ℝ × M => (⟨tx.2, X tx.1 tx.2⟩ : TangentBundle (𝓡 n) M))
      (J ×ˢ univ))
    {s : ℝ} (hs : s ∈ J)
    (hconf : ∀ (x : M) (a b : ℝ), s ∈ Icc a b → Icc a b ⊆ J →
      ∃ K : Set M, IsCompact K ∧ ∀ (I : Set ℝ),
        IsOpen I → Convex ℝ I → s ∈ I → ∀ (γ : ℝ → M), γ s = x →
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I →
          (∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) γ t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) →
          ∀ t ∈ I ∩ Icc a b, γ t ∈ K) :
    ∃ Φ : ℝ × M → M, (∀ x, Φ (s, x) = x) ∧
      SmoothTimeDependentIntegralFamily X univ J Φ := by
  classical
  have hinterval (t : J) := exists_Ioo_containing_pair hJ hcJ hs t.property
  choose a b hsa hta hab using hinterval
  have hfamily (t : J) (x : M) :
      ∃ (V : Set M) (Φ : ℝ × M → M), IsOpen V ∧ x ∈ V ∧
        SmoothTimeDependentIntegralFamily X V (Ioo (a t) (b t)) Φ ∧
        ∀ y ∈ V, Φ (s, y) = y :=
    exists_smooth_local_timeDependentFlow_on_interval hJ hX (hsa t) (hab t) x
      (hconf x (a t) (b t) (Ioo_subset_Icc_self (hsa t)) (hab t))
  choose V Ψ hV hxV hΨ hiΨ using hfamily
  let Φ : ℝ × M → M := fun p => if ht : p.1 ∈ J then Ψ ⟨p.1, ht⟩ p.2 p else p.2
  have hX₁ := hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have he (t : J) (x : M) : EqOn Φ (Ψ t x) (Ioo (a t) (b t) ×ˢ V t x) := by
    rintro ⟨r, y⟩ ⟨hr, hy⟩
    have hrJ : r ∈ J := hab t (Ioo_subset_Icc_self hr)
    change (if h : r ∈ J then Ψ ⟨r, h⟩ y (r, y) else y) = Ψ t x (r, y)
    rw [dif_pos hrJ]
    exact timeDependent_integralCurve_eqOn (isOpen_Ioo.inter isOpen_Ioo)
      ((convex_Ioo (a ⟨r, hrJ⟩) (b ⟨r, hrJ⟩)).inter (convex_Ioo (a t) (b t))).isPreconnected
      (hX₁.mono (prod_mono (inter_subset_right.trans
        (Ioo_subset_Icc_self.trans (hab t))) subset_rfl))
      (fun u hu => (hΨ ⟨r, hrJ⟩ y).orbit y (hxV _ _) u hu.1)
      (fun u hu => (hΨ t x).orbit y hy u hu.2)
      ⟨hsa _, hsa _⟩ ((hiΨ _ _ y (hxV _ _)).trans (hiΨ t x y hy).symm)
      ⟨hta _, hr⟩
  refine ⟨Φ, ?_, ⟨?_, ?_⟩⟩
  · intro x
    change (if h : s ∈ J then Ψ ⟨s, h⟩ x (s, x) else x) = x
    rw [dif_pos hs]
    exact hiΨ _ _ x (hxV _ _)
  · rintro ⟨t, x⟩ ⟨ht, _⟩
    have hmem : (t, x) ∈ Ioo (a ⟨t, ht⟩) (b ⟨t, ht⟩) ×ˢ V ⟨t, ht⟩ x :=
      ⟨hta _, hxV _ _⟩
    have hev : Φ =ᶠ[𝓝 (t, x)] Ψ ⟨t, ht⟩ x :=
      Filter.Eventually.mono ((isOpen_Ioo.prod (hV _ _)).mem_nhds hmem)
        (fun _ hp => he _ _ hp)
    exact (((hΨ _ _).smooth.contMDiffAt
      ((isOpen_Ioo.prod (hV _ _)).mem_nhds hmem)).congr_of_eventuallyEq hev).contMDiffWithinAt
  · intro x _ t ht
    have hev : (fun r => Φ (r, x)) =ᶠ[𝓝 t] (fun r => Ψ ⟨t, ht⟩ x (r, x)) :=
      Filter.Eventually.mono (isOpen_Ioo.mem_nhds (hta ⟨t, ht⟩))
        (fun r hr => he _ _ ⟨hr, hxV _ _⟩)
    have heval : Φ (t, x) = Ψ ⟨t, ht⟩ x (t, x) := he _ _ ⟨hta _, hxV _ _⟩
    apply (((hΨ ⟨t, ht⟩ x).orbit x (hxV _ _) t (hta _)).congr_of_eventuallyEq hev).congr_mfderiv
    rw [heval]

theorem exists_smooth_global_timeDependentFlow_of_compact_confinement
    {J : Set ℝ} (hJ : IsOpen J) (hcJ : Convex ℝ J)
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun tx : ℝ × M => (⟨tx.2, X tx.1 tx.2⟩ : TangentBundle (𝓡 n) M))
      (J ×ˢ univ))
    (hconf : ∀ (s : ℝ), s ∈ J → ∀ (x : M) (a b : ℝ),
      s ∈ Icc a b → Icc a b ⊆ J → ∃ K : Set M, IsCompact K ∧ ∀ (I : Set ℝ),
        IsOpen I → Convex ℝ I → s ∈ I → ∀ (γ : ℝ → M), γ s = x →
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I →
          (∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) γ t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) →
          ∀ t ∈ I ∩ Icc a b, γ t ∈ K) :
    ∃ E : ℝ → ℝ → M → M,
      (∀ s ∈ J, ∀ x, E s s x = x) ∧
      (∀ s ∈ J, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
        (fun p : ℝ × M => E s p.1 p.2) (J ×ˢ univ)) ∧
      (∀ s ∈ J, ∀ x, ∀ t ∈ J, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => E s r x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (E s t x)))) ∧
      (∀ s ∈ J, ∀ t ∈ J, ∀ r ∈ J, ∀ x, E t r (E s t x) = E s r x) ∧
      (∀ s ∈ J, ∀ t ∈ J, Function.LeftInverse (E t s) (E s t) ∧
        Function.RightInverse (E t s) (E s t)) := by
  classical
  have hex (s : J) := exists_smooth_timeDependentFlow_from_anchor_of_compact_confinement
    hJ hcJ hX s.property (hconf s s.property)
  choose Φ hi hΦ using hex
  let E : ℝ → ℝ → M → M := fun s t x => if hs : s ∈ J then Φ ⟨s, hs⟩ (t, x) else x
  have hinit : ∀ s ∈ J, ∀ x, E s s x = x := by
    intro s hs x
    simpa only [E, dif_pos hs] using hi ⟨s, hs⟩ x
  have hsmooth : ∀ s ∈ J, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => E s p.1 p.2) (J ×ˢ univ) := by
    intro s hs
    simpa only [E, dif_pos hs] using (hΦ ⟨s, hs⟩).smooth
  have horbit : ∀ s ∈ J, ∀ x, ∀ t ∈ J, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n)
      (fun r => E s r x) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (E s t x))) := by
    intro s hs x t ht
    have hE : E s = fun r y => Φ ⟨s, hs⟩ (r, y) := by
      funext r y
      exact dif_pos hs
    rw [hE]
    exact (hΦ ⟨s, hs⟩).orbit x (mem_univ x) t ht
  have hcomp : ∀ s ∈ J, ∀ t ∈ J, ∀ r ∈ J, ∀ x, E t r (E s t x) = E s r x := by
    intro s hs t ht r hr x
    exact timeDependent_integralCurve_eqOn hJ hcJ.isPreconnected
      (hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
      (horbit t ht (E s t x)) (horbit s hs x) ht (hinit t ht _) hr
  refine ⟨E, hinit, hsmooth, horbit, hcomp, ?_⟩
  intro s hs t ht
  exact ⟨fun x => (hcomp s hs t ht s hs x).trans (hinit s hs x),
    fun x => (hcomp t ht s hs t ht x).trans (hinit t ht x)⟩

end Poincare.Manifold

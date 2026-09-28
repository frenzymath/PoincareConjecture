import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Flow.Complete.Continuation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {X : (x : M) → TangentSpace (𝓡 n) x}

theorem exists_smooth_localFlow_on_arbitrary_interval
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X))
    (hconf : ∀ (x : M) (A : ℝ), 0 < A → ∃ K : Set M, IsCompact K ∧
      ∀ a, 0 < a → a ≤ A → ∀ γ : ℝ → M, γ 0 = x →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-a) a) →
        IsMIntegralCurveOn (I := 𝓡 n) γ X (Ioo (-a) a) →
        ∀ t ∈ Ioo (-a) a, γ t ∈ K)
    (x : M) (A : ℝ) :
    ∃ (V : Set M) (Φ : ℝ × M → M), IsOpen V ∧ x ∈ V ∧
      SmoothIntegralFamily X V (Ioo (-A) A) Φ ∧ ∀ y ∈ V, Φ (0, y) = y := by
  let S : Set ℝ := {a | 0 < a ∧ ∃ (V : Set M) (Φ : ℝ × M → M),
    IsOpen V ∧ x ∈ V ∧ SmoothIntegralFamily X V (Ioo (-a) a) Φ ∧
      ∀ y ∈ V, Φ (0, y) = y}
  obtain ⟨V₀, ε, Φ₀, hV₀, hxV₀, hε, hs₀, hi₀, hd₀⟩ := exists_smooth_localFlow hX x
  have hεS : ε ∈ S := ⟨hε, V₀, Φ₀, hV₀, hxV₀, ⟨hs₀, hd₀⟩, hi₀⟩
  have hSne : S.Nonempty := ⟨ε, hεS⟩
  have hunbounded : ¬ BddAbove S := by
    intro hbounded
    let B := sSup S
    have hεB : ε ≤ B := le_csSup hbounded hεS
    have hB : 0 < B := hε.trans_le hεB
    obtain ⟨K, hK, hconfK⟩ := hconf x (B + 1) (by linarith)
    obtain ⟨δ₀, hδ₀, hlocal₀⟩ := exists_uniform_smooth_localFlows hX hK
    let δ := min δ₀ B
    have hδ : 0 < δ := lt_min hδ₀ hB
    have hδB : δ ≤ B := min_le_right _ _
    have hlocal : ∀ y ∈ K, ∃ (W : Set M) (Ψ : ℝ × M → M),
        IsOpen W ∧ y ∈ W ∧ SmoothIntegralFamily X W (Ioo (-δ) δ) Ψ ∧
          ∀ z ∈ W, Ψ (0, z) = z := by
      intro y hy
      obtain ⟨W, Ψ, hW, hyW, hΨ, hi⟩ := hlocal₀ y hy
      exact ⟨W, Ψ, hW, hyW, hΨ.mono subset_rfl
        (Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)), hi⟩
    obtain ⟨a, haS, hnear⟩ := Real.add_neg_lt_sSup hSne (ε := -(δ / 2)) (by linarith)
    have haB : a ≤ B := le_csSup hbounded haS
    obtain ⟨ha, V, Φ, hV, hxV, hΦ, hiΦ⟩ := haS
    let s := B - δ / 2
    let R := B + δ / 2
    have hs : 0 < s := by dsimp [s]; linarith
    have hsa : s < a := by simpa only [s, sub_eq_add_neg] using hnear
    have hsI : s ∈ Ioo (-a) a := ⟨by linarith, hsa⟩
    have hnsI : -s ∈ Ioo (-a) a := ⟨by linarith, by linarith⟩
    have hcurveK : ∀ t ∈ Ioo (-a) a, Φ (t, x) ∈ K :=
      hconfK a ha (by linarith) (fun t => Φ (t, x)) (hiΦ x hxV)
        (hΦ.smooth_orbit hxV) (hΦ.orbit x hxV)
    obtain ⟨Wl, Ψl, hWl, hxWl, hΨl, hil⟩ := hlocal _ (hcurveK (-s) hnsI)
    obtain ⟨Wr, Ψr, hWr, hxWr, hΨr, hir⟩ := hlocal _ (hcurveK s hsI)
    let Vl := V ∩ (fun y => Φ (-s, y)) ⁻¹' Wl
    let Vr := V ∩ (fun y => Φ (s, y)) ⁻¹' Wr
    let W := Vl ∩ Vr
    obtain ⟨hVl, hleft⟩ := hΦ.restart hV hWl hnsI hΨl
    obtain ⟨hVr, hright⟩ := hΦ.restart hV hWr hsI hΨr
    have hW : IsOpen W := hVl.inter hVr
    have hxW : x ∈ W := ⟨⟨hxV, hxWl⟩, ⟨hxV, hxWr⟩⟩
    have hWV : W ⊆ V := fun _ hy => hy.1.1
    have hX₁ := hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
    obtain ⟨Θ, hΘ, heΘ, _⟩ := (hΦ.mono hWV subset_rfl).glue hX₁ hW
      (hleft.mono inter_subset_left subset_rfl)
      (show -s ∈ Ioo (-a) a ∩ Ioo (-s - δ) (-s + δ) from
        ⟨hnsI, ⟨by linarith, by linarith⟩⟩)
      (fun y hy => by simpa only [sub_self] using (hil _ hy.1.2).symm)
    have hsubL : Ioo (-R) a ⊆ Ioo (-a) a ∪ Ioo (-s - δ) (-s + δ) := by
      intro t ht
      by_cases hlo : -a < t
      · exact Or.inl ⟨hlo, ht.2⟩
      · right
        dsimp [R, s] at *
        constructor <;> linarith [ht.1, ht.2]
    have hsL : s ∈ Ioo (-R) a := ⟨by dsimp [R]; linarith, hsa⟩
    obtain ⟨Ξ, hΞ, heΞ, _⟩ := (hΘ.mono subset_rfl hsubL).glue hX₁ hW
      (hright.mono inter_subset_right subset_rfl)
      (show s ∈ Ioo (-R) a ∩ Ioo (s - δ) (s + δ) from
        ⟨hsL, ⟨by linarith, by linarith⟩⟩)
      (fun y hy => (heΘ ⟨hsI, hy⟩).trans (by
        simpa only [sub_self] using (hir _ hy.2.2).symm))
    have hsubR : Ioo (-R) R ⊆ Ioo (-R) a ∪ Ioo (s - δ) (s + δ) := by
      intro t ht
      by_cases hhi : t < a
      · exact Or.inl ⟨ht.1, hhi⟩
      · right
        dsimp [R, s] at *
        constructor <;> linarith [ht.1, ht.2]
    have hRS : R ∈ S := by
      refine ⟨by dsimp [R]; positivity, W, Ξ, hW, hxW, hΞ.mono subset_rfl hsubR, ?_⟩
      intro y hy
      exact (heΞ ⟨⟨by dsimp [R]; linarith, ha⟩, hy⟩).trans
        ((heΘ ⟨⟨by linarith, ha⟩, hy⟩).trans (hiΦ y (hWV hy)))
    have hRB := le_csSup hbounded hRS
    dsimp [R] at hRB
    linarith
  obtain ⟨a, haS, hAa⟩ := not_bddAbove_iff.mp hunbounded A
  obtain ⟨_, V, Φ, hV, hxV, hΦ, hi⟩ := haS
  exact ⟨V, Φ, hV, hxV, hΦ.mono subset_rfl
    (Ioo_subset_Ioo (neg_le_neg hAa.le) hAa.le), hi⟩

theorem exists_smooth_globalFlow_of_compact_confinement
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X))
    (hconf : ∀ (x : M) (A : ℝ), 0 < A → ∃ K : Set M, IsCompact K ∧
      ∀ a, 0 < a → a ≤ A → ∀ γ : ℝ → M, γ 0 = x →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-a) a) →
        IsMIntegralCurveOn (I := 𝓡 n) γ X (Ioo (-a) a) →
        ∀ t ∈ Ioo (-a) a, γ t ∈ K) :
    ∃ Φ : ℝ → M → M,
      (∀ x, Φ 0 x = x) ∧ (∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) X) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ) := by
  classical
  have hX₁ := hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hex (x : M) : ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve (I := 𝓡 n) γ X := by
    apply (exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hX₁ x).mpr
    intro A
    obtain ⟨V, Ψ, _, hxV, hΨ, hi⟩ := exists_smooth_localFlow_on_arbitrary_interval hX hconf x A
    exact ⟨fun t => Ψ (t, x), hi x hxV, hΨ.orbit x hxV⟩
  choose γ hi hγ using hex
  let Φ : ℝ → M → M := fun t x => γ x t
  refine ⟨Φ, hi, hγ, ?_, ?_⟩
  · intro s t x
    have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hX₁
      ((hγ x).comp_add t) (hγ (γ x t)) (by simp only [Function.comp_apply, zero_add, hi])
    exact congrFun he s
  · rintro ⟨t, x⟩
    let A := |t| + 1
    have hA : 0 < A := by dsimp [A]; positivity
    have htA : t ∈ Ioo (-A) A := abs_lt.mp (by dsimp [A]; linarith)
    obtain ⟨V, Ψ, hV, hxV, hΨ, hiΨ⟩ :=
      exists_smooth_localFlow_on_arbitrary_interval hX hconf x A
    have he : EqOn (Function.uncurry Φ) Ψ (Ioo (-A) A ×ˢ V) := by
      rintro ⟨r, y⟩ ⟨hr, hy⟩
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (show (0 : ℝ) ∈ Ioo (-A) A from ⟨by linarith, hA⟩) hX₁
        ((hγ y).isMIntegralCurveOn _) (hΨ.orbit y hy) ((hi y).trans (hiΨ y hy).symm) hr
    have hev : Function.uncurry Φ =ᶠ[𝓝 (t, x)] Ψ :=
      Filter.Eventually.mono ((isOpen_Ioo.prod hV).mem_nhds ⟨htA, hxV⟩) (fun _ hp => he hp)
    exact (hΨ.smooth.contMDiffAt ((isOpen_Ioo.prod hV).mem_nhds ⟨htA, hxV⟩)).congr_of_eventuallyEq hev

end Poincare.Manifold

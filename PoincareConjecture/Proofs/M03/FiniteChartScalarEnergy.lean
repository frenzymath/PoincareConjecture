import PoincareConjecture.Proofs.M03.CompactCoordinateChange










set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Topology BigOperators
open MeasureTheory Set

universe u

namespace PoincareConjecture.Proofs.M03

theorem exists_finite_chart_scalar_energy_bound
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (s : Finset M) (K L : M → Set (EuclideanSpace ℝ (Fin n)))
    (φ : M → EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : ∀ c ∈ s, IsCompact (K c))
    (hKt : ∀ c ∈ s, K c ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) c).target)
    (hL : ∀ c ∈ s, IsCompact (L c))
    (hLt : ∀ c ∈ s, L c ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) c).target)
    (hφ : ∀ c ∈ s, Continuous (φ c))
    (hφc : ∀ c ∈ s, HasCompactSupport (φ c))
    (hφt : ∀ c ∈ s, tsupport (φ c) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) c).target)
    (hφone : ∀ c ∈ s, EqOn (φ c) (fun _ => 1) (L c))
    (hcover : ∀ a ∈ s, ∀ x ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) a).symm '' K a,
      ∃ b ∈ s, x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) b).symm '' L b) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : M → ℝ, Continuous f → ∀ a ∈ s,
      (∫ z in K a, (f ((chartAt (EuclideanSpace ℝ (Fin n)) a).symm z)) ^ 2) ≤
        C * (∑ b ∈ s, ∫ z,
          (φ b z * f ((chartAt (EuclideanSpace ℝ (Fin n)) b).symm z)) ^ 2) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  classical
  let c (a : M) := chartAt (EuclideanSpace ℝ (Fin n)) a
  let X (a : M) : Set M := (c a).symm '' K a
  let Y (b : M) : Set M := (c b).symm '' L b
  let W (a b : M) : Set M := X a ∩ Y b
  let Q (a b : M) : Set (EuclideanSpace ℝ (Fin n)) := c b '' W a b
  let Z (a b : M) : Set (EuclideanSpace ℝ (Fin n)) := c a '' W a b
  let T (a b : M) := (c b).symm.trans (c a)
  have hXs (a : M) (ha : a ∈ s) : X a ⊆ (c a).source := by
    rintro x ⟨z, hz, rfl⟩
    exact (c a).map_target (hKt a ha hz)
  have hYs (b : M) (hb : b ∈ s) : Y b ⊆ (c b).source := by
    rintro x ⟨z, hz, rfl⟩
    exact (c b).map_target (hLt b hb hz)
  have hWc (a b : M) (ha : a ∈ s) (hb : b ∈ s) : IsCompact (W a b) :=
    ((hK a ha).image_of_continuousOn ((c a).continuousOn_symm.mono (hKt a ha))).inter
      ((hL b hb).image_of_continuousOn ((c b).continuousOn_symm.mono (hLt b hb)))
  have hQc (a b : M) (ha : a ∈ s) (hb : b ∈ s) : IsCompact (Q a b) :=
    (hWc a b ha hb).image_of_continuousOn
      ((c b).continuousOn.mono (fun _ hx => hYs b hb hx.2))
  have hZc (a b : M) (ha : a ∈ s) (hb : b ∈ s) : IsCompact (Z a b) :=
    (hWc a b ha hb).image_of_continuousOn
      ((c a).continuousOn.mono (fun _ hx => hXs a ha hx.1))
  have hQL (a b : M) (hb : b ∈ s) : Q a b ⊆ L b := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ := hx.2
    rw [← heq, (c b).right_inv (hLt b hb hy)]
    exact hy
  have hZK (a b : M) (ha : a ∈ s) : Z a b ⊆ K a := by
    rintro z ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ := hx.1
    rw [← heq, (c a).right_inv (hKt a ha hy)]
    exact hy
  have hT (a b : M) : ContDiffOn ℝ 1 (T a b) (T a b).source := by
    change ContDiffOn ℝ 1 (c a ∘ (c b).symm) (T a b).source
    have h := (contDiffOn_ext_coord_change (I := 𝓡 n) a b).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by simp)
    simpa only [ext_coord_change_source, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, image_id,
      Function.id_comp, Function.comp_id] using h
  have hQT (a b : M) (ha : a ∈ s) (hb : b ∈ s) : Q a b ⊆ (T a b).source := by
    rintro z ⟨x, hx, rfl⟩
    change c b x ∈ (c b).target ∧ (c b).symm (c b x) ∈ (c a).source
    refine ⟨(c b).map_source (hYs b hb hx.2), ?_⟩
    rw [(c b).left_inv (hYs b hb hx.2)]
    exact hXs a ha hx.1
  have hTZ (a b : M) (hb : b ∈ s) : T a b '' Q a b = Z a b := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      change c a x = c a ((c b).symm (c b x))
      rw [(c b).left_inv (hYs b hb hx.2)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨c b x, ⟨x, hx, rfl⟩, ?_⟩
      change c a ((c b).symm (c b x)) = c a x
      rw [(c b).left_inv (hYs b hb hx.2)]
  have hpair (a b : M) : ∃ D : ℝ, 0 ≤ D ∧ ∀ (_ha : a ∈ s) (_hb : b ∈ s),
      ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ContinuousOn g (Z a b) → (∀ y ∈ Z a b, 0 ≤ g y) →
      (∫ y in Z a b, g y) ≤ D * (∫ x in Q a b, g (T a b x)) := by
    by_cases ha : a ∈ s
    · by_cases hb : b ∈ s
      · obtain ⟨D, hD, hcomp⟩ := exists_compact_coordinate_change_integral_bound
          (T a b).open_source (hT a b) (T a b).injOn (hQc a b ha hb) (hQT a b ha hb)
        rw [hTZ a b hb] at hcomp
        exact ⟨D, hD, fun _ _ => hcomp⟩
      · exact ⟨0, le_rfl, fun _ hb' => (hb hb').elim⟩
    · exact ⟨0, le_rfl, fun ha' => (ha ha').elim⟩
  choose D hD0 hD using hpair
  let C : ℝ := ∑ a ∈ s, ∑ b ∈ s, D a b
  have hC : 0 ≤ C := Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hD0 a b))
  have hDC (a b : M) (ha : a ∈ s) (hb : b ∈ s) : D a b ≤ C :=
    (Finset.single_le_sum (fun j _ => hD0 a j) hb).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hD0 i j)) ha)
  refine ⟨C, hC, ?_⟩
  intro f hf a ha
  let g (b : M) (z : EuclideanSpace ℝ (Fin n)) : ℝ := (f ((c b).symm z)) ^ 2
  let F (b : M) (z : EuclideanSpace ℝ (Fin n)) : ℝ := (φ b z * f ((c b).symm z)) ^ 2
  let E (b : M) : ℝ := ∫ z, F b z
  have hg (b : M) : ContinuousOn (g b) (c b).target :=
    (hf.comp_continuousOn (c b).continuousOn_symm).pow 2
  have hg0 (b : M) (z : EuclideanSpace ℝ (Fin n)) : 0 ≤ g b z := sq_nonneg _
  have hFi (b : M) (hb : b ∈ s) : Integrable (F b) := by
    have hcont : Continuous (fun z => φ b z * f ((c b).symm z)) :=
      ((hφ b hb).continuousOn.mul
        (hf.comp_continuousOn (c b).continuousOn_symm)).continuous_of_tsupport_subset
          (c b).open_target (tsupport_mul_subset_left.trans (hφt b hb))
    have hFc : Continuous (F b) := hcont.pow 2
    have hFcompact : HasCompactSupport (F b) := by
      simpa only [F, Function.comp_def, Pi.mul_apply] using
        (((hφc b hb).mul_right (f' := fun z => f ((c b).symm z))).comp_left
          (g := fun y : ℝ => y ^ 2) (by simp))
    exact hFc.integrable_of_hasCompactSupport hFcompact
  have hE0 (b : M) : 0 ≤ E b := integral_nonneg (fun _ => sq_nonneg _)
  have hZi (b : M) (hb : b ∈ s) : IntegrableOn (g a) (Z a b) :=
    ContinuousOn.integrableOn_compact (hZc a b ha hb)
      ((hg a).mono ((hZK a b ha).trans (hKt a ha)))
  have hKi : IntegrableOn (g a) (K a) :=
    ContinuousOn.integrableOn_compact (hK a ha) ((hg a).mono (hKt a ha))
  have hcoverZ (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ K a) :
      ∃ b ∈ s, z ∈ Z a b := by
    obtain ⟨b, hb, hxb⟩ := hcover a ha ((c a).symm z) ⟨z, hz, rfl⟩
    exact ⟨b, hb, (c a).symm z, ⟨⟨z, hz, rfl⟩, hxb⟩, (c a).right_inv (hKt a ha hz)⟩
  have hcoverInt : (∫ z in K a, g a z) ≤ ∑ b ∈ s, ∫ z in Z a b, g a z := by
    have hpoint : ∀ z, (K a).indicator (g a) z ≤ ∑ b ∈ s, (Z a b).indicator (g a) z := by
      intro z
      have hnonneg (b : M) : 0 ≤ (Z a b).indicator (g a) z := by
        by_cases hz : z ∈ Z a b
        · simpa only [indicator_of_mem hz] using hg0 a z
        · rw [indicator_of_notMem hz]
      by_cases hz : z ∈ K a
      · obtain ⟨b, hb, hzb⟩ := hcoverZ z hz
        rw [indicator_of_mem hz]
        have h := Finset.single_le_sum (fun b _ => hnonneg b) hb
        simpa only [indicator_of_mem hzb] using h
      · rw [indicator_of_notMem hz]
        exact Finset.sum_nonneg (fun b _ => hnonneg b)
    have hiZ (b : M) (hb : b ∈ s) : Integrable ((Z a b).indicator (g a)) :=
      (hZi b hb).integrable_indicator (hZc a b ha hb).isClosed.measurableSet
    calc
      (∫ z in K a, g a z) = ∫ z, (K a).indicator (g a) z :=
        (integral_indicator (hK a ha).isClosed.measurableSet).symm
      _ ≤ ∫ z, ∑ b ∈ s, (Z a b).indicator (g a) z :=
        integral_mono (hKi.integrable_indicator (hK a ha).isClosed.measurableSet)
          (integrable_finsetSum s hiZ) hpoint
      _ = ∑ b ∈ s, ∫ z in Z a b, g a z := by
        rw [integral_finsetSum s hiZ]
        apply Finset.sum_congr rfl
        intro b hb
        exact integral_indicator (hZc a b ha hb).isClosed.measurableSet
  have hcompare (b : M) (hb : b ∈ s) : (∫ z in Z a b, g a z) ≤ D a b * E b := by
    have heq : EqOn (fun z => g a (T a b z)) (F b) (Q a b) := by
      rintro z ⟨x, hx, rfl⟩
      have hxb := hYs b hb hx.2
      have hxa := hXs a ha hx.1
      have hone := hφone b hb (hQL a b hb ⟨x, hx, rfl⟩)
      change (f ((c a).symm (c a ((c b).symm (c b x))))) ^ 2 =
        (φ b (c b x) * f ((c b).symm (c b x))) ^ 2
      rw [(c b).left_inv hxb, (c a).left_inv hxa, hone, one_mul]
    calc
      (∫ z in Z a b, g a z) ≤ D a b * (∫ z in Q a b, g a (T a b z)) :=
        hD a b ha hb (g a) ((hg a).mono ((hZK a b ha).trans (hKt a ha)))
          (fun z _ => hg0 a z)
      _ = D a b * (∫ z in Q a b, F b z) := by
        rw [setIntegral_congr_fun (hQc a b ha hb).isClosed.measurableSet heq]
      _ ≤ D a b * E b := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral (hFi b hb) (Filter.Eventually.of_forall (fun _ => sq_nonneg _)))
        (hD0 a b)
  change (∫ z in K a, g a z) ≤ C * ∑ b ∈ s, E b
  calc
    (∫ z in K a, g a z) ≤ ∑ b ∈ s, ∫ z in Z a b, g a z := hcoverInt
    _ ≤ ∑ b ∈ s, D a b * E b := Finset.sum_le_sum hcompare
    _ ≤ ∑ b ∈ s, C * E b := Finset.sum_le_sum (fun b hb =>
      mul_le_mul_of_nonneg_right (hDC a b ha hb) (hE0 b))
    _ = C * ∑ b ∈ s, E b := (Finset.mul_sum s (fun b => E b) C).symm

end PoincareConjecture.Proofs.M03

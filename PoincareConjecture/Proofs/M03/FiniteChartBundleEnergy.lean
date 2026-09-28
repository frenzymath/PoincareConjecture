import PoincareConjecture.Proofs.M03.CompactBundleCoordinates
import PoincareConjecture.Proofs.M03.CompactCoordinateChange










set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle MeasureTheory Set

universe u v w

namespace PoincareConjecture.Proofs.M03

theorem exists_finite_chart_bundle_energy_bound
    {n d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : M → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] [VectorBundle ℝ F E]
    (q : F ≃L[ℝ] EuclideanSpace ℝ (Fin d))
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
    (hbase : ∀ c ∈ s, (chartAt (EuclideanSpace ℝ (Fin n)) c).source ⊆
      (trivializationAt F E c).baseSet)
    (hcover : ∀ a ∈ s, ∀ x ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) a).symm '' K a,
      ∃ b ∈ s, x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) b).symm '' L b) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    let c := chartAt (EuclideanSpace ℝ (Fin n))
    let e := trivializationAt F E
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : (x : M) → E x,
      Continuous (fun x => TotalSpace.mk' F x (v x)) → ∀ a ∈ s,
      (∫ z in K a, ∑ i, (q ((e a) (TotalSpace.mk' F
        ((c a).symm z) (v ((c a).symm z)))).2 i) ^ 2) ≤
        C * (∑ b ∈ s, ∫ z, φ b z ^ 2 *
          ∑ i, (q ((e b) (TotalSpace.mk' F
            ((c b).symm z) (v ((c b).symm z)))).2 i) ^ 2) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  classical
  let c (a : M) := chartAt (EuclideanSpace ℝ (Fin n)) a
  let e (a : M) := trivializationAt F E a
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
  have hpair (a b : M) : ∃ J : ℝ, 0 ≤ J ∧ ∀ (_ha : a ∈ s) (_hb : b ∈ s),
      ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ContinuousOn g (Z a b) → (∀ y ∈ Z a b, 0 ≤ g y) →
      (∫ y in Z a b, g y) ≤ J * (∫ x in Q a b, g (T a b x)) := by
    by_cases ha : a ∈ s
    · by_cases hb : b ∈ s
      · obtain ⟨J, hJ, hcomp⟩ := exists_compact_coordinate_change_integral_bound
          (T a b).open_source (hT a b) (T a b).injOn (hQc a b ha hb) (hQT a b ha hb)
        rw [hTZ a b hb] at hcomp
        exact ⟨J, hJ, fun _ _ => hcomp⟩
      · exact ⟨0, le_rfl, fun _ hb' => (hb hb').elim⟩
    · exact ⟨0, le_rfl, fun ha' => (ha ha').elim⟩
  choose J hJ0 hJ using hpair
  let A : ℝ := ‖(q : F →L[ℝ] EuclideanSpace ℝ (Fin d))‖ ^ 2
  let B : ℝ := ‖(q.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] F)‖ ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  have hB : 0 ≤ B := sq_nonneg _
  have hq (u : F) : ‖q u‖ ^ 2 ≤ A * ‖u‖ ^ 2 := by
    calc
      ‖q u‖ ^ 2 ≤ (‖(q : F →L[ℝ] EuclideanSpace ℝ (Fin d))‖ * ‖u‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (q.toContinuousLinearMap.le_opNorm u) 2
      _ = A * ‖u‖ ^ 2 := mul_pow _ _ _
  have hqi (u : F) : ‖u‖ ^ 2 ≤ B * ‖q u‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _)
      (q.symm.toContinuousLinearMap.le_opNorm (q u)) 2
    simpa only [ContinuousLinearEquiv.coe_coe, q.symm_apply_apply, mul_pow] using h
  have hbundle (a b : M) : ∃ D : ℝ, 0 ≤ D ∧ ∀ (_ha : a ∈ s) (_hb : b ∈ s),
      ∀ x ∈ W a b, ∀ v : E x,
      ‖q ((e a) (TotalSpace.mk' F x v)).2‖ ^ 2 ≤
        D * ‖q ((e b) (TotalSpace.mk' F x v)).2‖ ^ 2 := by
    by_cases ha : a ∈ s
    · by_cases hb : b ∈ s
      · obtain ⟨D, hD0, hD⟩ := exists_compact_bundle_coordinate_bound
          (F := F) (E := E) a b (hWc a b ha hb)
          (fun x hx => hbase a ha (hXs a ha hx.1))
          (fun x hx => hbase b hb (hYs b hb hx.2))
        refine ⟨A * B * D, mul_nonneg (mul_nonneg hA hB) hD0, ?_⟩
        intro _ _ x hx v
        calc
          ‖q ((e a) (TotalSpace.mk' F x v)).2‖ ^ 2 ≤
              A * ‖((e a) (TotalSpace.mk' F x v)).2‖ ^ 2 := hq _
          _ ≤ A * (D * ‖((e b) (TotalSpace.mk' F x v)).2‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hD x hx v) hA
          _ ≤ A * (D * (B * ‖q ((e b) (TotalSpace.mk' F x v)).2‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hqi _) hD0) hA
          _ = (A * B * D) * ‖q ((e b) (TotalSpace.mk' F x v)).2‖ ^ 2 := by ring
      · exact ⟨0, le_rfl, fun _ hb' => (hb hb').elim⟩
    · exact ⟨0, le_rfl, fun ha' => (ha ha').elim⟩
  choose D hD0 hD using hbundle
  let C : ℝ := ∑ a ∈ s, ∑ b ∈ s, J a b * D a b
  have hJD0 (a b : M) : 0 ≤ J a b * D a b := mul_nonneg (hJ0 a b) (hD0 a b)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hJD0 a b))
  have hDC (a b : M) (ha : a ∈ s) (hb : b ∈ s) : J a b * D a b ≤ C :=
    (Finset.single_le_sum (fun j _ => hJD0 a j) hb).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hJD0 i j)) ha)
  refine ⟨C, hC, ?_⟩
  intro v hv a ha
  let g (b : M) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
    ‖q ((e b) (TotalSpace.mk' F ((c b).symm z) (v ((c b).symm z)))).2‖ ^ 2
  let H (b : M) (z : EuclideanSpace ℝ (Fin n)) : ℝ := φ b z ^ 2 * g b z
  let energy (b : M) : ℝ := ∫ z, H b z
  have hg (b : M) (hb : b ∈ s) : ContinuousOn (g b) (c b).target := by
    have he : ContinuousOn
        (fun z => (e b) (TotalSpace.mk' F ((c b).symm z) (v ((c b).symm z))))
        (c b).target :=
      (e b).continuousOn.comp (hv.comp_continuousOn (c b).continuousOn_symm)
        (fun z hz => (e b).mem_source.mpr (hbase b hb ((c b).map_target hz)))
    exact (q.continuous.comp_continuousOn he.snd).norm.pow 2
  have hg0 (b : M) (z : EuclideanSpace ℝ (Fin n)) : 0 ≤ g b z := sq_nonneg _
  have hH0 (b : M) (z : EuclideanSpace ℝ (Fin n)) : 0 ≤ H b z :=
    mul_nonneg (sq_nonneg _) (hg0 b z)
  have hHi (b : M) (hb : b ∈ s) : Integrable (H b) := by
    have hsupport : tsupport (H b) ⊆ tsupport (φ b) := by
      apply closure_mono
      intro z hz
      by_contra hzφ
      apply hz
      change φ b z ^ 2 * g b z = 0
      rw [Function.notMem_support.mp hzφ, zero_pow (by decide : 2 ≠ 0), zero_mul]
    have hHc : Continuous (H b) :=
      (((hφ b hb).continuousOn.pow 2).mul (hg b hb)).continuous_of_tsupport_subset
        (c b).open_target (hsupport.trans (hφt b hb))
    have hHcompact : HasCompactSupport (H b) :=
      (hφc b hb).of_isClosed_subset (isClosed_tsupport _) hsupport
    exact hHc.integrable_of_hasCompactSupport hHcompact
  have hE0 (b : M) : 0 ≤ energy b := integral_nonneg (hH0 b)
  have hZi (b : M) (hb : b ∈ s) : IntegrableOn (g a) (Z a b) :=
    ContinuousOn.integrableOn_compact (hZc a b ha hb)
      ((hg a ha).mono ((hZK a b ha).trans (hKt a ha)))
  have hKi : IntegrableOn (g a) (K a) :=
    ContinuousOn.integrableOn_compact (hK a ha) ((hg a ha).mono (hKt a ha))
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
  have hcompare (b : M) (hb : b ∈ s) :
      (∫ z in Z a b, g a z) ≤ (J a b * D a b) * energy b := by
    have hpoint : ∀ z ∈ Q a b, g a (T a b z) ≤ D a b * H b z := by
      rintro z ⟨x, hx, rfl⟩
      have hxb := hYs b hb hx.2
      have hxa := hXs a ha hx.1
      have hone := hφone b hb (hQL a b hb ⟨x, hx, rfl⟩)
      change ‖q ((e a) (TotalSpace.mk' F
          ((c a).symm (c a ((c b).symm (c b x))))
          (v ((c a).symm (c a ((c b).symm (c b x))))))).2‖ ^ 2 ≤
        D a b * (φ b (c b x) ^ 2 *
          ‖q ((e b) (TotalSpace.mk' F ((c b).symm (c b x))
            (v ((c b).symm (c b x))))).2‖ ^ 2)
      rw [(c b).left_inv hxb, (c a).left_inv hxa, hone, one_pow, one_mul]
      exact hD a b ha hb x hx (v x)
    have hcomp : ContinuousOn (fun z => g a (T a b z)) (Q a b) :=
      ((hg a ha).mono ((hZK a b ha).trans (hKt a ha))).comp
        ((hT a b).continuousOn.mono (hQT a b ha hb)) (fun z hz => by
          rw [← hTZ a b hb]
          exact mem_image_of_mem _ hz)
    have hcompI : IntegrableOn (fun z => g a (T a b z)) (Q a b) :=
      ContinuousOn.integrableOn_compact (hQc a b ha hb) hcomp
    calc
      (∫ z in Z a b, g a z) ≤ J a b * (∫ z in Q a b, g a (T a b z)) :=
        hJ a b ha hb (g a) ((hg a ha).mono ((hZK a b ha).trans (hKt a ha)))
          (fun z _ => hg0 a z)
      _ ≤ J a b * (∫ z in Q a b, D a b * H b z) :=
        mul_le_mul_of_nonneg_left
          (setIntegral_mono_on hcompI ((hHi b hb).integrableOn.const_mul _)
            (hQc a b ha hb).isClosed.measurableSet hpoint) (hJ0 a b)
      _ = (J a b * D a b) * (∫ z in Q a b, H b z) := by
        rw [integral_const_mul, mul_assoc]
      _ ≤ (J a b * D a b) * energy b := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral (hHi b hb) (Filter.Eventually.of_forall (hH0 b))) (hJD0 a b)
  have hresult : (∫ z in K a, g a z) ≤ C * ∑ b ∈ s, energy b := by
    calc
      (∫ z in K a, g a z) ≤ ∑ b ∈ s, ∫ z in Z a b, g a z := hcoverInt
      _ ≤ ∑ b ∈ s, (J a b * D a b) * energy b := Finset.sum_le_sum hcompare
      _ ≤ ∑ b ∈ s, C * energy b := Finset.sum_le_sum (fun b hb =>
        mul_le_mul_of_nonneg_right (hDC a b ha hb) (hE0 b))
      _ = C * ∑ b ∈ s, energy b := (Finset.mul_sum s (fun b => energy b) C).symm
  simpa only [g, H, energy, EuclideanSpace.real_norm_sq_eq] using hresult

end PoincareConjecture.Proofs.M03

import PoincareConjecture.Proofs.M03.FiniteChartBundleEnergy
import PoincareConjecture.Proofs.M03.FamilyBundleCoordinates
import PoincareConjecture.Proofs.M03.LocalCoordinateEnergy

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle MeasureTheory Set

universe u v w

namespace PoincareConjecture.Proofs.M03

theorem exists_finite_bundle_family_energy_bound
    {n d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : M → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] [VectorBundle ℝ F E]
    [ContMDiffVectorBundle ∞ F E (𝓡 n)]
    (q : F ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (s : Finset M) (φ : M → EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ∀ a ∈ s, Continuous (φ a))
    (hφc : ∀ a ∈ s, HasCompactSupport (φ a))
    (hφt : ∀ a ∈ s, tsupport (φ a) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) a).target)
    (hbase : ∀ a ∈ s, (chartAt (EuclideanSpace ℝ (Fin n)) a).source ⊆
      (trivializationAt F E a).baseSet)
    (hcover : ∀ x : M, ∃ a ∈ s,
      x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) a).source ∧
      φ a (chartAt (EuclideanSpace ℝ (Fin n)) a x) = 1) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    let c := chartAt (EuclideanSpace ℝ (Fin n))
    let e := trivializationAt F E
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : Set ℝ), IsCompact J →
      ∀ v : (t : ℝ) → (x : M) → E x,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, F)) ∞
        (fun p : ℝ × M => TotalSpace.mk' F p.2 (v p.1 p.2)) (J ×ˢ Set.univ) →
      let f : M → Fin d → ℝ × EuclideanSpace ℝ (Fin n) → ℝ :=
        fun a i p => q ((e a) (TotalSpace.mk' F
          ((c a).symm p.2) (v p.1 ((c a).symm p.2)))).2 i
      let energy : ℝ → ℝ :=
        fun t => ∑ a ∈ s, ∑ i, ∫ z, (φ a z * f a i (t, z)) ^ 2
      ContinuousOn energy J ∧
      (∀ t ∈ J, 0 ≤ energy t) ∧
      (∀ t ∈ J, energy t = 0 ↔ ∀ x : M, v t x = 0) ∧
      (∀ t ∈ interior J, HasDerivAt energy
        (∑ a ∈ s, ∑ i, ∫ z, 2 * φ a z ^ 2 * f a i (t, z) *
          fderiv ℝ (f a i) (t, z) (1, 0)) t) ∧
      (∀ t ∈ J, ∀ a ∈ s,
        (∫ z in tsupport (φ a), ∑ i, (f a i (t, z)) ^ 2) ≤ C * energy t) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  classical
  let c (a : M) := chartAt (EuclideanSpace ℝ (Fin n)) a
  let e := trivializationAt F E
  let L (a : M) : Set (EuclideanSpace ℝ (Fin n)) := {z | φ a z = 1}
  have hLs (a : M) : L a ⊆ tsupport (φ a) := by
    intro z hz
    apply subset_closure
    change φ a z ≠ 0
    rw [show φ a z = 1 from hz]
    exact one_ne_zero
  have hLc (a : M) (ha : a ∈ s) : IsCompact (L a) :=
    (hφc a ha).of_isClosed_subset (isClosed_eq (hφ a ha) continuous_const) (hLs a)
  obtain ⟨C, hC0, hC⟩ := exists_finite_chart_bundle_energy_bound q s
    (fun a => tsupport (φ a)) L φ hφc hφt hLc
    (fun a ha => (hLs a).trans (hφt a ha)) hφ hφc hφt
    (fun _ _ _ hz => hz) hbase (fun _ _ x _ => by
      obtain ⟨b, hb, hx, hone⟩ := hcover x
      exact ⟨b, hb, c b x, hone, (c b).left_inv hx⟩)
  refine ⟨C, hC0, ?_⟩
  intro J hJ v hv
  let f : M → Fin d → ℝ × EuclideanSpace ℝ (Fin n) → ℝ :=
    fun a i p => q ((e a) (TotalSpace.mk' F
      ((c a).symm p.2) (v p.1 ((c a).symm p.2)))).2 i
  let energy : ℝ → ℝ :=
    fun t => ∑ a ∈ s, ∑ i, ∫ z, (φ a z * f a i (t, z)) ^ 2
  have hf (a : M) (ha : a ∈ s) (i : Fin d) :
      ContDiffOn ℝ ∞ (f a i) (J ×ˢ (c a).target) :=
    by
      dsimp [f, c, e]
      convert (EuclideanSpace.proj i).contDiff.comp_contDiffOn
        (contDiffOn_family_bundle_coordinates q v hv a (hbase a ha)) using 1
      rfl
  have hslice (a : M) (ha : a ∈ s) (i : Fin d) (t : ℝ) (ht : t ∈ J) :
      ContinuousOn (fun z => f a i (t, z)) (c a).target :=
    (hf a ha i).continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => ⟨ht, hz⟩)
  have hnonneg (t : ℝ) (a : M) (i : Fin d) :
      0 ≤ ∫ z, (φ a z * f a i (t, z)) ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hintegrable (a : M) (ha : a ∈ s) (i : Fin d) (t : ℝ) (ht : t ∈ J) :
      Integrable (fun z => (φ a z * f a i (t, z)) ^ 2) := by
    have hweighted : Continuous (fun z => φ a z * f a i (t, z)) :=
      ((hφ a ha).continuousOn.mul (hslice a ha i t ht)).continuous_of_tsupport_subset
        (c a).open_target (tsupport_mul_subset_left.trans (hφt a ha))
    have hsupport : tsupport (fun z => (φ a z * f a i (t, z)) ^ 2) ⊆
        tsupport (φ a) := by
      apply closure_mono
      intro z hz
      by_contra hzφ
      apply hz
      change (φ a z * f a i (t, z)) ^ 2 = 0
      rw [Function.notMem_support.mp hzφ, zero_mul, zero_pow (by decide : 2 ≠ 0)]
    have hcompact : HasCompactSupport (fun z => (φ a z * f a i (t, z)) ^ 2) :=
      (hφc a ha).of_isClosed_subset (isClosed_tsupport _) hsupport
    apply (hweighted.pow 2).integrable_of_hasCompactSupport
    exact hcompact
  change ContinuousOn energy J ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact continuousOn_finsetSum s (fun a ha => continuousOn_finsetSum Finset.univ
      (fun i _ => continuousOn_local_coordinate_energy hJ (c a).open_target
        (hf a ha i).continuousOn (hφ a ha) (hφc a ha) (hφt a ha)))
  · intro t _
    exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun i _ => hnonneg t a i))
  · intro t ht
    constructor
    · intro hzero x
      have hsum (a : M) (ha : a ∈ s) :
          (∑ i, ∫ z, (φ a z * f a i (t, z)) ^ 2) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun a _ => Finset.sum_nonneg (fun i _ => hnonneg t a i))).mp hzero a ha
      have hcomponent (a : M) (ha : a ∈ s) (i : Fin d) :
          (∫ z, (φ a z * f a i (t, z)) ^ 2) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg t a i)).mp
          (hsum a ha) i (Finset.mem_univ i)
      obtain ⟨a, ha, hx, hone⟩ := hcover x
      have hqzero : q ((e a) (TotalSpace.mk' F x (v t x))).2 = 0 := by
        ext i
        have hval := (local_coordinate_energy_eq_zero_iff (c a).open_target
          (hslice a ha i t ht) (hφ a ha) (hφc a ha) (hφt a ha)).mp
          (hcomponent a ha i) (c a x)
        dsimp only [f] at hval
        rw [(c a).left_inv hx, hone, one_mul] at hval
        exact hval
      have hcoordzero := q.injective (hqzero.trans q.map_zero.symm)
      apply ((e a).linearEquivAt ℝ x (hbase a ha hx)).injective
      rw [map_zero]
      exact hcoordzero
    · intro hzero
      have hweighted (a : M) (ha : a ∈ s) (i : Fin d) (z : EuclideanSpace ℝ (Fin n)) :
          φ a z * f a i (t, z) = 0 := by
        by_cases hz : z ∈ tsupport (φ a)
        · have hx := hbase a ha ((c a).map_target (hφt a ha hz))
          have hezero : ((e a) (TotalSpace.mk' F ((c a).symm z) (0 : E ((c a).symm z)))).2 = 0 :=
            ((e a).linearEquivAt ℝ ((c a).symm z) hx).map_zero
          dsimp only [f]
          rw [hzero, hezero, q.map_zero]
          simp
        · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      apply Finset.sum_eq_zero
      intro a ha
      apply Finset.sum_eq_zero
      intro i _
      have hfun : (fun z => (φ a z * f a i (t, z)) ^ 2) = fun _ => 0 := by
        funext z
        rw [hweighted a ha i z, zero_pow (by decide : 2 ≠ 0)]
      rw [hfun, integral_zero]
  · intro t ht
    apply HasDerivAt.fun_sum
    intro a ha
    apply HasDerivAt.fun_sum
    intro i _
    exact hasDerivAt_local_coordinate_energy isOpen_interior (c a).open_target
      (((hf a ha i).mono (Set.prod_mono interior_subset subset_rfl)).of_le
        (show (1 : ℕ∞ω) ≤ ∞ by simp)) (hφ a ha) (hφc a ha) (hφt a ha) ht
  · intro t ht a ha
    have hsection : Continuous (fun x => TotalSpace.mk' F x (v t x)) :=
      hv.continuousOn.comp_continuous (.prodMk_right t) (fun x => ⟨ht, mem_univ x⟩)
    have hbound := hC (v t) hsection a ha
    change (∫ z in tsupport (φ a), ∑ i, (f a i (t, z)) ^ 2) ≤
      C * (∑ b ∈ s, ∫ z, φ b z ^ 2 * ∑ i, (f b i (t, z)) ^ 2) at hbound
    have henergy : (∑ b ∈ s, ∫ z, φ b z ^ 2 * ∑ i, (f b i (t, z)) ^ 2) = energy t := by
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∫ z, φ b z ^ 2 * ∑ i, (f b i (t, z)) ^ 2) =
            ∫ z, ∑ i, (φ b z * f b i (t, z)) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with z
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact (mul_pow _ _ _).symm
        _ = ∑ i, ∫ z, (φ b z * f b i (t, z)) ^ 2 :=
          integral_finsetSum _ (fun i _ => hintegrable b hb i t ht)
    rw [henergy] at hbound
    exact hbound

end PoincareConjecture.Proofs.M03

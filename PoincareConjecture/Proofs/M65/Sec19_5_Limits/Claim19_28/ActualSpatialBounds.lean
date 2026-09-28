import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.IntrinsicFiniteRanges










set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {a b : ℝ} {F : RicciFlow n M (Icc a b)}

set_option maxHeartbeats 1600000 in





theorem m65ActualIntrinsicSpatialBounds {κ : Type*}
    (hcompact : IsCompact (univ : Set M)) {circumference : κ → ℝ}
    (P : ∀ k, M62.CircleProductData F (circumference k))
    (c : ∀ k, ℝ → ℝ → (P k).charts.Point)
    (hc : ∀ k, M62ShrinkingCurve (P k).flow (c k))
    {r s : ℝ} (hrs : r ≤ s) (hsub : Icc r s ⊆ Ioo a b)
    (v₀ : κ → ℝ) (hinit : ∀ k x, curveSpeed (P k).flow (c k) r x = v₀ k)
    (hvzero : ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s →
      |curveSpeed (P k).flow (c k) t x| ≤ B)
    (hbound : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s →
      ((P k).flow.metric t).tangentNorm (c k x t)
        (m65IntrinsicTangentJet (P k).flow (c k) j t x) ≤ B) :
    ∃ (N : ℕ) (p : Fin N → M) (K : Fin N → Set M),
      (∀ i, IsCompact (K i)) ∧
      (∀ i, K i ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source) ∧
      (∀ y : M, ∃ i, y ∈ interior (K i)) ∧
      ∀ m : ℕ,
        (∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s →
          ‖iteratedFDeriv ℝ m (curveSpeed (P k).flow (c k) t) x‖ ≤ B) ∧
        ∀ i j, ∃ B : ℝ, 0 ≤ B ∧ ∀ k t x, t ∈ Icc r s → (c k x t).1 ∈ K i →
          ‖iteratedFDeriv ℝ m (m65IntrinsicChartField (P k) (c k) (p i) j t) x‖ ≤ B := by
  classical
  obtain ⟨N, p, K, hK, hKs, hcover⟩ := m65Exists_finite_chart_cores (n := n) hcompact
  let v : κ → ℝ × ℝ → ℝ := fun k z => curveSpeed (P k).flow (c k) z.1 z.2
  let α : κ → ℝ × ℝ → ℝ := fun k z =>
    -(m62TangentRicci (P k).flow (c k) z.1 z.2 +
      m62CurvatureSquared (P k).flow (c k) z.1 z.2)
  let S : Fin N → κ × Icc r s → Set ℝ := fun i k => {x | (c k.1 x k.2).1 ∈ K i}
  let f : Fin N → ℕ → κ × Icc r s → ℝ → EuclideanSpace ℝ (Fin n) × ℝ :=
    fun i j k => m65IntrinsicChartField (P k.1) (c k.1) (p i) j k.2
  have hv (k : κ) : ContDiffOn ℝ ∞ (v k) (Ioo a b ×ˢ univ) :=
    (M62.speed_joint_contDiffOn (P k).flow (c k) (hc k)).comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hz => ⟨mem_univ _, hz.1⟩)
  have hα (k : κ) : ContDiffOn ℝ ∞ (α k) (Ioo a b ×ˢ univ) :=
    (M62.normalization_coefficient_contDiffOn (P k).flow (c k) (hc k)).neg.comp
      (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hz => ⟨mem_univ _, hz.1⟩)
  have hf (i : Fin N) (j : ℕ) (k : κ × Icc r s) (x : ℝ) (hx : x ∈ S i k) :
      ContDiffAt ℝ ∞ (f i j k) x :=
    m65IntrinsicChartField_contDiffAt (P k.1) (c k.1) (hc k.1) (p i) j
      (hsub k.2.property) (hKs i hx)
  have hnear (i : Fin N) (k : κ × Icc r s) (x : ℝ) (hx : x ∈ S i k) :
      ∀ᶠ y in 𝓝 x, (c k.1 y k.2).1 ∈
        (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source := by
    let := (P k.1).charts.chartedSpace
    have hbase : Continuous (fun y => (c k.1 y k.2).1) :=
      continuous_fst.comp
        ((hc k.1).spatial_regular k.2 (Ioo_subset_Icc_self (hsub k.2.property))).continuous
    exact hbase.continuousAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) (p i)).open_source.mem_nhds (hKs i hx))
  have hrec (i : Fin N) (j : ℕ) (k : κ × Icc r s) (x : ℝ) (hx : x ∈ S i k) :
      deriv (f i j k) =ᶠ[𝓝 x] fun y => m65IntrinsicSpatialOperator F (p i) j
        (v k.1 (k.2, y), fun l : Fin (j + 2) => f i l k y) := by
    filter_upwards [hnear i k x hx] with y hy
    exact (m65IntrinsicChartField_hasDerivAt (P k.1) (c k.1) (hc k.1)
      (p i) j (hsub k.2.property) hy).deriv
  have hαeq (i : Fin N) (k : κ × Icc r s) (x : ℝ) (hx : x ∈ S i k) :
      (fun y => α k.1 (k.2, y)) =ᶠ[𝓝 x]
        fun y => m65IntrinsicSpeedCoefficient F (p i) (fun l : Fin 3 => f i l k y) := by
    filter_upwards [hnear i k x hx] with y hy
    exact (m65IntrinsicSpeedCoefficient_eq (P k.1) (c k.1) (p i)
      (hsub k.2.property) hy).symm
  have hRcompact (i : Fin N) (j : ℕ) :
      ∃ C : Set (ℝ × (Fin (j + 2) → EuclideanSpace ℝ (Fin n) × ℝ)), IsCompact C ∧
        C ⊆ m65IntrinsicSpatialDomain (a := a) (b := b) (p i) j ∧
        ∀ k x, x ∈ S i k → (v k.1 (k.2, x), fun l : Fin (j + 2) => f i l k x) ∈ C := by
    obtain ⟨C, hC, hCd, hCr⟩ := m65IntrinsicSpatialOperator_compact_range P c (p i)
      hsub (hK i) (hKs i) hbound hvzero j
    exact ⟨C, hC, hCd, fun k x hx => hCr k.1 k.2 x k.2.property hx⟩
  have hAcompact (i : Fin N) :
      ∃ C : Set (Fin 3 → EuclideanSpace ℝ (Fin n) × ℝ), IsCompact C ∧
        C ⊆ m65IntrinsicSpeedDomain (a := a) (b := b) (p i) ∧
        ∀ k x, x ∈ S i k → (fun l : Fin 3 => f i l k x) ∈ C := by
    obtain ⟨C, hC, hCd, hCr⟩ := m65IntrinsicChartField_compact_finiteRange P c (p i)
      hsub (hK i) (hKs i) hbound 3 (by norm_num)
    exact ⟨C, hC, hCd, fun k x hx => hCr k.1 k.2 x k.2.property hx⟩
  have hvb : ∃ B : ℝ, 0 ≤ B ∧ ∀ k : κ × Icc r s, ∀ x, |v k.1 (k.2, x)| ≤ B := by
    obtain ⟨B, hB, hb⟩ := hvzero
    exact ⟨B, hB, fun k x => hb k.1 k.2 x k.2.property⟩
  have hfb (i : Fin N) (j : ℕ) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ k x, x ∈ S i k → ‖f i j k x‖ ≤ B := by
    obtain ⟨B, hB, hb⟩ :=
      m65IntrinsicChartField_uniform_zero P c (p i) hsub (hK i) (hKs i) hbound j
    exact ⟨B, hB, fun k x hx => hb k.1 k.2 x k.2.property hx⟩
  have hjets := m65UniformSpatialJets_of_triangularRecurrences hrs hsub v α v₀ S f
    (fun i => m65IntrinsicSpatialOperator F (p i))
    (fun i => m65IntrinsicSpeedCoefficient F (p i))
    (fun i => m65IntrinsicSpatialDomain (a := a) (b := b) (p i))
    (fun i => m65IntrinsicSpeedDomain (a := a) (b := b) (p i))
    (fun i => m65IntrinsicSpatialDomain_isOpen (p i))
    (fun i => m65IntrinsicSpeedDomain_isOpen (p i))
    (fun i => m65IntrinsicSpatialOperator_contDiffOn (F := F) (p i))
    (fun i => m65IntrinsicSpeedCoefficient_contDiffOn (F := F) (p i))
    hRcompact hAcompact (fun k x => by
      obtain ⟨i, hi⟩ := hcover (c k.1 x k.2).1 (mem_univ _)
      exact ⟨i, show (c k.1 x k.2).1 ∈ K i from interior_subset hi⟩)
    hv hα hf (fun k t x ht => M62.hasDerivAt_speed (P k).flow (c k) (hc k) ht x)
    hinit hvb hfb hrec hαeq
  refine ⟨N, p, K, hK, hKs, fun y => hcover y (mem_univ y), ?_⟩
  intro m
  obtain ⟨hvm, hfm⟩ := hjets m
  constructor
  · obtain ⟨B, hB, hb⟩ := hvm
    exact ⟨B, hB, fun k t x ht => hb (k, ⟨t, ht⟩) x⟩
  · intro i j
    obtain ⟨B, hB, hb⟩ := hfm i j
    exact ⟨B, hB, fun k t x ht hx => hb (k, ⟨t, ht⟩) x hx⟩

end PoincareConjecture

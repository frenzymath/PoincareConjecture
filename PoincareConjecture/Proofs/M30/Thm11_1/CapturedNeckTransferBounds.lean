import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.FixedCylinderJets
import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.VaryingScalar
import PoincareConjecture.Proofs.M28.Mathlib.WithinConvergenceBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

universe u v w

namespace PoincareConjecture.M30.CapturedNeckTransfer

open PoincareConjecture.M28.tube PoincareConjecture.Proofs.M28.FiniteHessian
open PoincareConjecture.Proofs.M28.NeckTransfer

section Atlas

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {X : ℕ → Type u} [∀ k, TopologicalSpace (X k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X k)]
  [∀ k, IsManifold (𝓡 3) ∞ (X k)] {ι : Type w} [Finite ι]

set_option maxHeartbeats 800000 in

theorem exists_eventual_atlas_bounds
    (g : RiemannianMetric 3 M) (h : ∀ k, RiemannianMetric 3 (X k))
    (e : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) M (X k) ∞)
    (q : ι → M) (L : ι → Set (EuclideanSpace ℝ (Fin 3)))
    (hL : ∀ i, IsCompact (L i))
    (htarget : ∀ i, L i ⊆ (extChartAt (𝓡 3) (q i)).target)
    (m : ℕ)
    (hjets : ∀ i r, r ≤ m → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r
        ((h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm)))
      (iteratedFDeriv ℝ r (g.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm))
      atTop (L i)) :
    ∃ c B : ℝ, 0 < c ∧ 1 ≤ B ∧ ∀ᶠ k in atTop, ∀ i x, x ∈ L i →
      (∀ v : EuclideanSpace ℝ (Fin 3), c * ‖v‖ ^ 2 ≤
        (h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm) x v v) ∧
      ∀ r ≤ m, ‖iteratedFDeriv ℝ r
        ((h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm)) x‖ ≤ B := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hsingle (i : ι) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ x ∈ L i, ∀ v : EuclideanSpace ℝ (Fin 3), c * ‖v‖ ^ 2 ≤
        (h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm) x v v := by
    let B0 := g.pullbackCoefficients (extChartAt (𝓡 3) (q i)).symm
    have hcontinuous : ContinuousOn B0 (L i) :=
      (g.contDiffOn_chartCoefficients (q i)).continuousOn.mono (htarget i)
    have hpos : ∀ x ∈ L i, ∀ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 →
        0 < B0 x v v := by
      intro x hx v hv
      have hAv : mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q i)).symm x v ≠ 0 := by
        intro hzero
        obtain ⟨A, hA⟩ := g.isInvertible_chartCoefficients (q i) (htarget i hx)
        apply hv
        apply A.injective
        change (A : EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) v = A 0
        rw [map_zero, hA]
        ext z
        change g.inner _
          (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q i)).symm x v)
          (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q i)).symm x z) = 0
        rw [hzero]
        simp +instances only [map_zero, zero_apply]
      exact g.pos _ _ hAv
    obtain ⟨c, hc, hlow⟩ := exists_uniform_bilinear_lower_bound (hL i) hcontinuous hpos
    have hzero : TendstoUniformlyOn
        (fun k => (h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm))
        B0 atTop (L i) :=
      (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → EuclideanSpace ℝ (Fin 3))).comp_tendstoUniformlyOn
          (hjets i 0 (Nat.zero_le m))
    refine ⟨c / 2, half_pos hc, ?_⟩
    filter_upwards [(Metric.tendstoUniformlyOn_iff
      (α := EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)).mp
        hzero (c / 2) (half_pos hc)]
      with k hk
    intro x hx v
    let B := (h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i)).symm) x
    have herr : ‖B - B0 x‖ ≤ c / 2 := by
      calc
        ‖B - B0 x‖ = dist (B0 x) B := (dist_eq_norm' (B0 x) B).symm
        _ ≤ c / 2 := (hk x hx).le
    have hval : B0 x v v - B v v ≤ ‖(B - B0 x) v v‖ := by
      calc
        B0 x v v - B v v ≤ |B0 x v v - B v v| := le_abs_self _
        _ = |B v v - B0 x v v| := abs_sub_comm _ _
        _ = ‖(B - B0 x) v v‖ := by rw [Real.norm_eq_abs]; rfl
    have hnorm := (B - B0 x).le_opNorm₂ v v
    have herror := mul_le_mul_of_nonneg_right herr (sq_nonneg ‖v‖)
    have hdiff : B0 x v v - B v v ≤ c / 2 * ‖v‖ ^ 2 :=
      hval.trans (hnorm.trans (by nlinarith only [herror]))
    change c / 2 * ‖v‖ ^ 2 ≤ B v v
    linarith only [hdiff, hlow x hx v]
  choose c hc hquad using hsingle
  have hsingleJet (i : ι × Fin (m + 1)) : ∃ B : ℝ, 1 ≤ B ∧
      ∀ᶠ k in atTop, ∀ x ∈ L i.1,
        ‖iteratedFDeriv ℝ i.2
          ((h k).pullbackCoefficients (e k ∘ (extChartAt (𝓡 3) (q i.1)).symm)) x‖ ≤ B := by
    apply (hjets i.1 i.2 (by omega)).exists_eventual_norm_bound (hL i.1)
    intro x hx
    have hcont := (g.contDiffOn_chartCoefficients (q i.1)).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) (q i.1)).mem_nhds (htarget i.1 hx))
    exact (hcont.continuousAt_iteratedFDeriv
      (by exact_mod_cast le_top)).continuousWithinAt
  choose B hB hjet using hsingleJet
  let lower : Option ι → ℝ := fun i => i.elim 1 c
  let c0 := Finset.univ.inf' Finset.univ_nonempty lower
  let B0 := 1 + ∑ i, B i
  have hc0 : 0 < c0 := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro i _
    cases i with
    | none => exact zero_lt_one
    | some i => exact hc i
  have hc_le (i : ι) : c0 ≤ c i := Finset.inf'_le lower (Finset.mem_univ (some i))
  have hBsum : 0 ≤ ∑ i, B i := Finset.sum_nonneg (fun i _ => (by linarith [hB i]))
  have hB0 : 1 ≤ B0 := by dsimp only [B0]; linarith
  have hB_le (i : ι × Fin (m + 1)) : B i ≤ B0 := by
    have hh : B i ≤ ∑ j, B j := Finset.single_le_sum
      (fun j _ => zero_le_one.trans (hB j)) (Finset.mem_univ i)
    dsimp only [B0]
    linarith
  refine ⟨c0, B0, hc0, hB0, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hquad, Filter.eventually_all.mpr hjet]
    with k hk hkj
  intro i x hx
  constructor
  · intro v
    exact (mul_le_mul_of_nonneg_right (hc_le i) (sq_nonneg ‖v‖)).trans (hk i x hx v)
  · intro r hr
    let j : ι × Fin (m + 1) := (i, ⟨r, Nat.lt_succ_of_le hr⟩)
    exact (hkj j x hx).trans (hB_le j)

end Atlas

section Source

variable {ι : Type w} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]
  [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X i)]
  [∀ i, IsManifold (𝓡 3) ∞ (X i)] {h : ∀ i, RiemannianMetric 3 (X i)}

theorem source_coefficient_jets
    (N : ∀ i, EpsilonNeck (h i)) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1)
    (heps : ∀ i, (N i).epsilon = epsilon) {B : ℝ}
    (hscale : ∀ i, (N i).scale ^ 2 ≤ B)
    (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (hs : ∀ i, s i ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (m : ℕ) (hm : m ≤ ⌊epsilon⁻¹⌋₊) :
    HasUniformJetBoundsAt m
      (fun i => (h i).pullbackCoefficients (cylinderNeckChart (N i) (q i) (s i)))
      (fun _ => 0) := by
  have hj := hasUniformJetBoundsAt_cylinderNeckCoefficients
    N hepsilon hsmall heps m hm q s hs
  have hc (i : ι) : ContDiffAt ℝ ∞ (cylinderNeckCoefficients (N i) (q i) (s i)) 0 := by
    apply (contDiffOn_cylinderNeckCoefficients (N i) (q i) (s i)).contDiffAt
    apply (isOpen_cylinderNeckChartDomain (N i) (q i) (s i)).mem_nhds
    apply zero_mem_cylinderNeckChartDomain
    simpa only [heps] using hs i
  have hcb (i : ι) : ‖(N i).scale ^ 2‖ ≤ B := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hscale i
  apply (hj.smul_family hc (fun i => (N i).scale ^ 2) hcb).congr_germ
  intro i
  filter_upwards [] with x
  exact (cylinderNeckCoefficients_unscale (N i) (q i) (s i) x).symm

end Source

end PoincareConjecture.M30.CapturedNeckTransfer

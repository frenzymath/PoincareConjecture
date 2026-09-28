import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusLiminf
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedMetric
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64ObservedWeakAnnulus_weightedEnergy_attained
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) {c0 c1 : ℝ → M}
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v) {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (A0 : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    ∃ r ∈ Icc lo hi, ∃ L : M64ObservedWeakAnnulus (n := n) e c0 c1,
      ∀ s ∈ Icc lo hi, ∀ A : M64ObservedWeakAnnulus (n := n) e c0 c1,
        L.weightedEnergy B r ≤ A.weightedEnergy B s := by
  classical
  let T : Set ℝ := range (fun P : Icc lo hi × M64ObservedWeakAnnulus (n := n) e c0 c1 =>
    P.2.weightedEnergy B P.1)
  have hne : T.Nonempty := ⟨A0.weightedEnergy B lo, (⟨lo, le_rfl, hlohi⟩, A0), rfl⟩
  have hlower : BddBelow T := by
    refine ⟨0, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact P.2.weightedEnergy_nonneg B hpos (hlo.le.trans P.1.property.1)
  obtain ⟨u, hanti, hlim, hu⟩ := exists_seq_tendsto_sInf hne hlower
  change ∀ j, ∃ P : Icc lo hi × M64ObservedWeakAnnulus (n := n) e c0 c1,
    P.2.weightedEnergy B P.1 = u j at hu
  choose P hP using hu
  let r : ℕ → ℝ := fun j => (P j).1
  let A := fun j => (P j).2
  have hr (j : ℕ) : r j ∈ Icc lo hi := (P j).1.property
  have hA (j : ℕ) : (A j).weightedEnergy B (r j) = u j := hP j
  let D := max lo⁻¹ hi
  have hD : 0 ≤ D := (inv_nonneg.mpr hlo.le).trans (le_max_left _ _)
  have hcols (j : ℕ) (i : Fin 2) : ‖(A j).column i‖ ^ 2 ≤ 2 * C * D * u 0 := by
    calc
      _ ≤ 2 * C * (A j).energy B :=
        (A j).column_norm_sq_le_energy B hB hei.isEmbedding hb hpos hC hcoercive i
      _ ≤ 2 * C * (D * (A j).weightedEnergy B (r j)) :=
        mul_le_mul_of_nonneg_left
          ((A j).energy_le_weightedEnergy_of_mem B hB hei.isEmbedding hb hpos hlo (hr j))
          (by positivity)
      _ = (2 * C * D) * u j := by rw [hA j]; ring
      _ ≤ (2 * C * D) * u 0 :=
        mul_le_mul_of_nonneg_left (hanti (Nat.zero_le j)) (by positivity)
  obtain ⟨r0, hr0, k, hk, hrlim⟩ := isCompact_Icc.tendsto_subseq hr
  obtain ⟨l, L, hl, -, hweak, htarget⟩ :=
    m64ObservedWeakAnnulus_subsequence e he hei hread (fun j => A (k j))
      (fun j i => hcols (k j) i)
  have hrllim : Tendsto (fun j => r (k (l j))) atTop (𝓝 r0) :=
    hrlim.comp hl.tendsto_atTop
  have hlsc := m64ObservedWeakAnnulus_weightedEnergy_le_liminf hei.isEmbedding B hB
    hK hb hpos hsymm hlo hr0 (fun j => r (k (l j))) (fun j => hr (k (l j))) hrllim
    (fun j => A (k (l j))) L (fun j i => hcols (k (l j)) i) hweak htarget
  have henergy : Tendsto (fun j => (A (k (l j))).weightedEnergy B (r (k (l j))))
      atTop (𝓝 (sInf T)) := by
    simpa only [hA, Function.comp_def] using hlim.comp (hk.comp hl).tendsto_atTop
  rw [henergy.liminf_eq] at hlsc
  refine ⟨r0, hr0, L, fun s hs A => hlsc.trans (csInf_le hlower ?_)⟩
  exact ⟨(⟨s, hs⟩, A), rfl⟩

theorem m64ObservedWeakAnnulus_exists_modulus_minimizer
    (g : RiemannianMetric n M) (e : M → E)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) {c0 c1 : ℝ → M}
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (A0 : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    ∃ (B : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ), r ∈ Icc lo hi ∧
      ∃ L : M64ObservedWeakAnnulus (n := n) e c0 c1,
        Continuous B ∧ (∀ q v, 0 ≤ B q v v) ∧ (∀ q v w, B q v w = B q w v) ∧
        (∀ (f : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 f → ∀ p i j,
          B (f p) (fderiv ℝ (e ∘ f) p (EuclideanSpace.basisFun (Fin 2) ℝ i))
            (fderiv ℝ (e ∘ f) p (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
              m60AreaGram g f p i j) ∧
        ∀ s ∈ Icc lo hi, ∀ A : M64ObservedWeakAnnulus (n := n) e c0 c1,
          L.weightedEnergy B r ≤ A.weightedEnergy B s := by
  obtain ⟨B, K, hB, hK, hb, hpos, hsymm, hgram⟩ :=
    m64ChartReadable_observed_metric g e he hread
  obtain ⟨C, hC, hcoercive⟩ := m64ObservedMetric_tangent_coercivity g e he B hgram
  obtain ⟨r, hr, L, hL⟩ := m64ObservedWeakAnnulus_weightedEnergy_attained e he hei hread
    B hB hK hb hpos hsymm hC hcoercive hlo hlohi A0
  exact ⟨B, r, hr, L, hB, hpos, hsymm, hgram, hL⟩

end PoincareConjecture

import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeWeakPhaseCompactness
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.FreeEnergyLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem weightedEnergy_attained
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e)
    (R : E →L[ℝ] LoopPlane) (c0 c1 : ℝ → M) (hc0 : Continuous c0) (hc1 : Continuous c1)
    (H0 H1 : ℝ ≃o ℝ) {frequency D : ℝ} (hf : frequency ≠ 0)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (A0 : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 frequency D) :
    ∃ r ∈ Icc lo hi,
      ∃ L : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 frequency D,
        ∀ s ∈ Icc lo hi,
          ∀ A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 frequency D,
            L.annulus.weightedEnergy B r ≤ A.annulus.weightedEnergy B s := by
  classical
  let X := M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 frequency D
  let T : Set ℝ := range (fun P : Icc lo hi × X => P.2.annulus.weightedEnergy B P.1)
  have hne : T.Nonempty :=
    ⟨A0.annulus.weightedEnergy B lo, (⟨lo, le_rfl, hlohi⟩, A0), rfl⟩
  have hlower : BddBelow T := by
    refine ⟨0, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact P.2.annulus.weightedEnergy_nonneg B hpos (hlo.le.trans P.1.property.1)
  obtain ⟨u, hanti, hlim, hu⟩ := exists_seq_tendsto_sInf hne hlower
  change ∀ j, ∃ P : Icc lo hi × X, P.2.annulus.weightedEnergy B P.1 = u j at hu
  choose P hP using hu
  let r := fun j : ℕ => ((P j).1 : ℝ)
  let A := fun j => (P j).2
  have hr (j : ℕ) : r j ∈ Icc lo hi := (P j).1.property
  have hA (j : ℕ) : (A j).annulus.weightedEnergy B (r j) = u j := hP j
  let Cmodulus := max lo⁻¹ hi
  have hCmodulus : 0 ≤ Cmodulus := (inv_nonneg.mpr hlo.le).trans (le_max_left _ _)
  have hcols (j : ℕ) (i : Fin 2) :
      ‖(A j).annulus.column i‖ ^ 2 ≤ 2 * C * Cmodulus * u 0 := by
    calc
      _ ≤ 2 * C * (A j).annulus.energy B :=
        (A j).annulus.column_norm_sq_le_energy B hB hei.isEmbedding hb hpos hC hcoercive i
      _ ≤ 2 * C * (Cmodulus * (A j).annulus.weightedEnergy B (r j)) :=
        mul_le_mul_of_nonneg_left
          ((A j).annulus.energy_le_weightedEnergy_of_mem B hB hei.isEmbedding hb hpos hlo (hr j))
          (by positivity)
      _ = (2 * C * Cmodulus) * u j := by rw [hA]; ring
      _ ≤ (2 * C * Cmodulus) * u 0 :=
        mul_le_mul_of_nonneg_left (hanti (Nat.zero_le j)) (by positivity)
  obtain ⟨r0, hr0, k, hk, hrlim⟩ := isCompact_Icc.tendsto_subseq hr
  obtain ⟨l, L, hl, -, hweak, htarget, -, -, -, -, -, -⟩ :=
    bounded_columns_subsequence e he hei hread R c0 c1 hc0 hc1 H0 H1 hf hH0 hH1
      (fun j => A (k j)) (fun j i => hcols (k j) i)
  have hrlim' : Tendsto (fun j => r (k (l j))) atTop (𝓝 r0) := hrlim.comp hl.tendsto_atTop
  have hlsc := M64.varying_trace_weightedEnergy_le_liminf hei.isEmbedding B hB hK hb hpos hsymm
    hlo hr0 (fun j => r (k (l j))) (fun j => hr (k (l j))) hrlim'
    (fun j => (A (k (l j))).annulus) L.annulus (fun j i => hcols (k (l j)) i) hweak htarget
  have henergy : Tendsto (fun j => (A (k (l j))).annulus.weightedEnergy B (r (k (l j))))
      atTop (𝓝 (sInf T)) := by
    simpa only [hA, Function.comp_def] using hlim.comp (hk.comp hl).tendsto_atTop
  rw [henergy.liminf_eq] at hlsc
  refine ⟨r0, hr0, L, fun s hs Q => hlsc.trans (csInf_le hlower ?_)⟩
  exact ⟨(⟨s, hs⟩, Q), rfl⟩

end PoincareConjecture.M64FreeWeakPhaseAnnulus

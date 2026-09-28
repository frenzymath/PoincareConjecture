import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakClassEnergyLiminf
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



theorem m64ObservedWeakAnnulus_energy_attained
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) {c0 c1 : ℝ → M}
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) (hsymm : ∀ q v w, B q v w = B q w v)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v) (A0 : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    ∃ L : M64ObservedWeakAnnulus (n := n) e c0 c1,
      ∀ A : M64ObservedWeakAnnulus (n := n) e c0 c1, L.energy B ≤ A.energy B := by
  classical
  let T : Set ℝ := range (fun A : M64ObservedWeakAnnulus (n := n) e c0 c1 => A.energy B)
  have hne : T.Nonempty := ⟨A0.energy B, A0, rfl⟩
  have hlo : BddBelow T := by
    refine ⟨0, ?_⟩
    rintro _ ⟨A, rfl⟩
    exact A.energy_nonneg B hpos
  obtain ⟨u, hanti, hlim, hu⟩ := exists_seq_tendsto_sInf hne hlo
  change ∀ j, ∃ A : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy B = u j at hu
  choose A hA using hu
  have hcols (j : ℕ) (i : Fin 2) : ‖(A j).column i‖ ^ 2 ≤ 2 * C * u 0 := by
    calc
      _ ≤ 2 * C * (A j).energy B :=
        (A j).column_norm_sq_le_energy B hB hei.isEmbedding hb hpos hC hcoercive i
      _ = 2 * C * u j := by rw [hA j]
      _ ≤ 2 * C * u 0 := mul_le_mul_of_nonneg_left (hanti (Nat.zero_le j)) (by positivity)
  obtain ⟨k, L, hk, -, hweak, htarget⟩ :=
    m64ObservedWeakAnnulus_subsequence e he hei hread A hcols
  have hlsc := m64ObservedWeakAnnulus_energy_le_liminf hei.isEmbedding B hB hK hb hpos
    hsymm (fun j => A (k j)) L (fun j i => hcols (k j) i) hweak htarget
  have henergy : Tendsto (fun j => (A (k j)).energy B) atTop (𝓝 (sInf T)) := by
    simpa only [hA, Function.comp_def] using hlim.comp hk.tendsto_atTop
  rw [henergy.liminf_eq] at hlsc
  exact ⟨L, fun A => hlsc.trans (csInf_le hlo ⟨A, rfl⟩)⟩



theorem m64ObservedWeakAnnulus_exists_minimizer
    (g : RiemannianMetric n M) (e : M → E)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) {c0 c1 : ℝ → M}
    (A0 : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    ∃ (B : M → E →L[ℝ] E →L[ℝ] ℝ) (L : M64ObservedWeakAnnulus (n := n) e c0 c1),
      Continuous B ∧ (∀ q v, 0 ≤ B q v v) ∧ (∀ q v w, B q v w = B q w v) ∧
      (∀ (f : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 f → ∀ p i j,
        B (f p) (fderiv ℝ (e ∘ f) p (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ (e ∘ f) p (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
            m60AreaGram g f p i j) ∧
      ∀ A : M64ObservedWeakAnnulus (n := n) e c0 c1, L.energy B ≤ A.energy B := by
  obtain ⟨B, K, hB, hK, hb, hpos, hsymm, hgram⟩ :=
    m64ChartReadable_observed_metric g e he hread
  obtain ⟨C, hC, hcoercive⟩ := m64ObservedMetric_tangent_coercivity g e he B hgram
  obtain ⟨L, hL⟩ := m64ObservedWeakAnnulus_energy_attained e he hei hread B hB hK hb hpos
    hsymm hC hcoercive A0
  exact ⟨B, L, hB, hpos, hsymm, hgram, hL⟩

end PoincareConjecture

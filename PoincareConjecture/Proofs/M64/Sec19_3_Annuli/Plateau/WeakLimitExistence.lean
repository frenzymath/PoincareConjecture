import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.IntrinsicEnergyCompactness
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakColumnTangency












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S



theorem m64Annulus_exists_intrinsic_weak_limit
    (g : RiemannianMetric n M)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    {L : ℝ} (hE : Tendsto (fun j => ∫ p in S, m60EnergyDensity g (f j) p) atTop (𝓝 L))
    (c0 c1 : ℝ → M)
    (h0 : ∀ j x, f j (annulusPoint x 0) = c0 x)
    (h1 : ∀ j x, f j (annulusPoint x 1) = c1 x) :
    ∃ (m : ℕ) (e : M → EuclideanSpace ℝ (Fin m))
      (B : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
      (K : ℝ) (v : LoopPlane → M)
      (u : Lp (EuclideanSpace ℝ (Fin m)) 2 mu)
      (V : Fin 2 → Lp (EuclideanSpace ℝ (Fin m)) 2 mu),
      ContMDiff (𝓡 n) (𝓡 m) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := n) e ∧
      Continuous B ∧ 0 ≤ K ∧ (∀ q, ‖B q‖ ≤ K) ∧
      (∀ q w, 0 ≤ B q w w) ∧ (∀ q w z, B q w z = B q z w) ∧
      (∀ (a : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 a → ∀ p i j,
        B (a p) (fderiv ℝ (e ∘ a) p (EuclideanSpace.basisFun (Fin 2) ℝ i))
          (fderiv ℝ (e ∘ a) p (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
            m60AreaGram g a p i j) ∧
      AEStronglyMeasurable (B ∘ v) mu ∧ (∀ᵐ p ∂mu, e (v p) = u p) ∧
      (∀ i, ∀ᵐ p ∂mu, V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (v p))) ∧
      (∀ i (phi : LoopPlane → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ S →
        (∫ p in S, phi p • V i p) =
          -(∫ p in S, fderiv ℝ phi p (EuclideanSpace.basisFun (Fin 2) ℝ i) • u p)) ∧
      (∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi →
        (∫ p in S, phi p • V 1 p) +
          (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • u p) =
          ∫ x in Icc (0 : ℝ) curvePeriod,
            phi (annulusPoint x 1) • e (c1 x) - phi (annulusPoint x 0) • e (c0 x)) ∧
      (∫ p in S, (B (v p) (V 0 p) (V 0 p) + B (v p) (V 1 p) (V 1 p)) / 2) ≤ L := by
  obtain ⟨m, e, he, hei, hread⟩ := M60.suCompactObservation_exists (n := n) (M := M)
  have he1 : ContMDiff (𝓡 n) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨C, hC⟩ := hE.cauchySeq.isBounded_range.exists_norm_le
  have hbound (j : ℕ) : (∫ p in S, m60EnergyDensity g (f j) p) ≤ C :=
    (le_abs_self _).trans (hC _ (mem_range_self j))
  obtain ⟨B, K, k, v, u, V, hU, hV, hB, hK, hb, hpos, hsymm, hgram,
      hk, -, hweak, hev, htest, htrace, henergy⟩ :=
    m64Annulus_intrinsic_sobolev_subsequence g e he1 hei hread f hf hbound c0 c1 h0 h1
  have hlim : ∀ᵐ p ∂mu, Tendsto (fun j => f (k j) p) atTop (𝓝 (v p)) :=
    hev.mono fun _ hp => hp.2
  have hmeas : AEStronglyMeasurable (B ∘ v) mu := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun j => (hB.comp (hf (k j)).continuous).aestronglyMeasurable)
    filter_upwards [hlim] with p hp
    exact (hB.tendsto _).comp hp
  refine ⟨m, e, B, K, v, u, V, he, hei, hread, hB, hK, hb, hpos, hsymm, hgram,
    hmeas, hev.mono (fun _ hp => hp.1), ?_, htest, htrace, ?_⟩
  · intro i
    exact m64Annulus_observed_weak_column_tangent e he1 hread
      (fun j => f (k j)) (fun j => hf (k j)) v i (fun j => hV j i) (V i) (hweak i) hlim
  · have hsub : Tendsto (fun j => ∫ p in S, m60EnergyDensity g (f (k j)) p) atTop (𝓝 L) :=
      hE.comp hk.tendsto_atTop
    rwa [hsub.liminf_eq] at henergy

end PoincareConjecture

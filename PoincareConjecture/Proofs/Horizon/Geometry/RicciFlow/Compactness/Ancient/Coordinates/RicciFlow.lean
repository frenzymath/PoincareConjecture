import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.TimeGluing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.LocalFlows
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]



theorem exists_ancientRicciFlow_on_coordinate_limit
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {T : ℝ} {J : ℕ → Set ℝ} (Fseq : ∀ k, RicciFlow n (M k) (J k))
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (i : ι) (e : ∀ k, Piece U i → M k)
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k))
    (g : ℝ → CanonicalMetric U hU i)
    (hg : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      RiemannianMetric.IsSmoothFamilyOn g (Iio T))
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hcoeff : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ t ∈ Iio T, ∀ (x : Piece U i) v w, (g t).inner x v w = B (t, x) v w)
    (hjet : ∀ m K, IsCompact K → K ⊆ Iio T ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((Fseq k).metric p.1).pullbackCoefficients (chartParametrization U hU (e k)) p.2))
      (iteratedFDeriv ℝ m B) atTop K) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∃ F : RicciFlow n (Piece U i) (Iio T), F.metric = g := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  apply RicciFlow.exists_ancient_of_local_metric_realizations g hg
  intro t ht
  let a := t - 1
  let b := (t + T) / 2
  have ha : a < t := by dsimp [a]; linarith
  have htb : t < b := by dsimp [b]; linarith
  have hb : b < T := by dsimp [b]; linarith
  have hwin : Ioo a b ⊆ Iio T := fun s hs ↦ hs.2.trans hb
  have hne : (Ioo a b).Nontrivial := by
    refine ⟨t, ⟨ha, htb⟩, (t + b) / 2, ⟨?_, ?_⟩, ?_⟩ <;> linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (htime a b hb)
  let Ftail (k : ℕ) : RicciFlow n (M (k + N)) (Ioo a b) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow (Fseq (k + N))
      (fun _ hs ↦ hN (k + N) (by omega) (Ioo_subset_Icc_self hs))
      ordConnected_Ioo hne
  refine ⟨Ioo a b, isOpen_Ioo, ⟨ha, htb⟩, ?_⟩
  apply exists_ricciFlow_on_coordinate_limit U hU isOpen_Ioo Ftail i
    (fun k ↦ e (k + N)) (fun k ↦ he (k + N)) g
    (hg.mono (prod_mono hwin (Subset.refl _))) B
    (fun s hs ↦ hcoeff s (hwin hs))
  intro m K hK hKU
  have hconv := hjet m K hK (hKU.trans (prod_mono hwin (Subset.refl _)))
  intro V hV
  exact (tendsto_add_atTop_nat N).eventually (hconv V hV)

end PoincareConjecture.ChartDistance

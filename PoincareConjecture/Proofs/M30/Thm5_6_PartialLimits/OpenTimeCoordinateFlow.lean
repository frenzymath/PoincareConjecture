import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.LocalFlows
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Gluing Poincare.Analysis.Calculus
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M30

theorem exists_coordinate_flow_of_expanding_time_domains
    {ι : Type u} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : ℕ → Type v} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {W : Set ℝ} (hW : IsOpen W) (hWord : Set.OrdConnected W)
    (hWne : W.Nontrivial)
    {J : ℕ → Set ℝ} (Fseq : ∀ k, RicciFlow n (M k) (J k))
    (htime : ∀ a b : ℝ, Icc a b ⊆ W →
      ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (i : ι) (e : ∀ k, Piece U i → M k)
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ∀ k, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e k))
    (g : ℝ → Poincare.Gluing.CanonicalMetric U hU i)
    (hg : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
        (I := 𝓡 n) (n := ∞)
      RiemannianMetric.IsSmoothFamilyOn g W)
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hcoeff : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
        (I := 𝓡 n) (n := ∞)
      ∀ t ∈ W, ∀ (x : Piece U i) v w, (g t).inner x v w = B (t, x) v w)
    (hjet : ∀ m K, IsCompact K → K ⊆ W ×ˢ U i → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((Fseq k).metric p.1).pullbackCoefficients
            (ChartDistance.chartParametrization U hU (e k)) p.2))
      (iteratedFDeriv ℝ m B) atTop K) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 n) (n := ∞)
    ∃ F : RicciFlow n (Piece U i) W, F.metric = g := by
  classical
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  have hlocal : ∀ t ∈ W, ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
      ∃ F : RicciFlow n (Piece U i) V, F.metric = g := by
    intro t ht
    obtain ⟨a, b, _, habnhds, habW⟩ :=
      exists_Icc_mem_subset_of_mem_nhds (hW.mem_nhds ht)
    have htab : t ∈ Ioo a b := Icc_mem_nhds_iff.mp habnhds
    have hwin : Ioo a b ⊆ W := Ioo_subset_Icc_self.trans habW
    have hne : (Ioo a b).Nontrivial := by
      refine ⟨t, htab, (t + b) / 2, ⟨?_, ?_⟩, ?_⟩ <;> rcases htab with ⟨ha, hb⟩ <;>
        linarith
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htime a b habW)
    let Ftail (k : ℕ) : RicciFlow n (M (k + N)) (Ioo a b) :=
      Poincare.Geometry.RicciFlow.Harnack.restrictFlow (Fseq (k + N))
        (fun _ hs ↦ hN (k + N) (by omega) (Ioo_subset_Icc_self hs))
        ordConnected_Ioo hne
    refine ⟨Ioo a b, isOpen_Ioo, htab, ?_⟩
    apply ChartDistance.exists_ricciFlow_on_coordinate_limit U hU isOpen_Ioo Ftail i
      (fun k ↦ e (k + N)) (fun k ↦ he (k + N)) g
      (hg.mono (prod_mono hwin (Subset.refl _))) B
      (fun s hs ↦ hcoeff s (hwin hs))
    intro m K hK hKU
    have hconv := hjet m K hK (hKU.trans (prod_mono hwin (Subset.refl _)))
    intro V hV
    exact (tendsto_add_atTop_nat N).eventually (hconv V hV)
  obtain ⟨t0, ht0⟩ := hWne.nonempty
  let time : ℝ → ℝ := fun t ↦ if t ∈ W then t else t0
  have htimeW (t : ℝ) : time t ∈ W := by
    dsimp [time]
    split_ifs with ht
    · exact ht
    · exact ht0
  choose V hV htV G hG using fun t ↦ hlocal (time t) (htimeW t)
  let g' : ℝ → RiemannianMetric n (Piece U i) := fun t ↦ (G t).metric t
  have hgg : g' = g := by
    funext t
    exact congrFun (hG t) t
  refine ⟨{
    metric := g'
    connection := fun t ↦ (G t).connection t
    interval := hWord
    nontrivial := hWne
    smooth := by simpa only [hgg] using hg
    equation := ?_ }, hgg⟩
  intro t ht x v w
  have hmem : t ∈ V t := by
    simpa only [time, if_pos ht] using htV t
  have hd := ((G t).equation t hmem x v w).hasDerivAt ((hV t).mem_nhds hmem)
  apply HasDerivAt.hasDerivWithinAt
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall fun s ↦ by
    change ((G s).metric s).inner x v w = ((G t).metric s).inner x v w
    rw [hG s, hG t]

end PoincareConjecture.M30

import PoincareConjecture.Proofs.M47.LimitFiniteEndpointExtraction









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance finiteEndpointOldDualAdd :
    NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteEndpointOldDualSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteEndpointOldBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteEndpointOldBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace

private theorem eq_of_sharp_comparison (B B0 : V)
    (hsymm : ∀ v w, B v w = B w v) (hsymm0 : ∀ v w, B0 v w = B0 w v)
    (hcompare : ∀ v, ∀ δ : ℝ, 0 < δ → δ < 1 →
      (1 - δ) * B0 v v ≤ B v v ∧ B v v ≤ (1 + δ) * B0 v v) : B = B0 := by
  have hdiag (v : E) : B v v = B0 v v := by
    have hsmall (e : ℝ) (he : 0 < e) :
        B v v ≤ B0 v v + e ∧ B0 v v ≤ B v v + e := by
      let δ := min (1 / 2) (e / (|B0 v v| + 1))
      have hδ : 0 < δ := by dsimp [δ]; positivity
      have hδlt : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
      have hprod : δ * (|B0 v v| + 1) ≤ e :=
        (le_div_iff₀ (by positivity : 0 < |B0 v v| + 1)).mp (min_le_right _ _)
      have herror : δ * B0 v v ≤ e :=
        (mul_le_mul_of_nonneg_left (by linarith [le_abs_self (B0 v v)]) hδ.le).trans hprod
      obtain ⟨hl, hu⟩ := hcompare v δ hδ hδlt
      constructor <;> nlinarith
    exact le_antisymm (le_of_forall_pos_le_add fun e he => (hsmall e he).1)
      (le_of_forall_pos_le_add fun e he => (hsmall e he).2)
  ext v w
  have hsum := hdiag (v + w)
  simp only [map_add, add_apply] at hsum
  rw [hsymm w v, hsymm0 w v] at hsum
  linarith [hdiag v, hdiag w]

private theorem coefficient_symm
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (φ : E → M) (z v w : E) :
    g.pullbackCoefficients φ z v w = g.pullbackCoefficients φ z w v :=
  g.symm _ _ _

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance finiteEndpointOldTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance finiteEndpointOldCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteEndpointOldManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

variable (j : ℕ)

local notation "U" => TopologicalSpace.Opens.mk
  (G.exhaustion.space j) (G.exhaustion.space_open j)



theorem limitFinite_endpoint_old_metric
    (σ : ℕ → ℕ) (hσ : StrictMono σ) {t : ℝ} (ht : t ∈ blowupBackwardInterval H)
    (g : ℕ → RiemannianMetric 3 U)
    (hread : ∀ᶠ k : ℕ in atTop,
      ∃ htk : t ∈ Icc (-G.exhaustion.time (σ k)) 0,
        ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
          (g k).inner x v w = (G.embedding (σ k)).pullbackInner t htk x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) x w))
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞) (z : E) (B : V)
    (hconv : ∀ v w, Tendsto (fun k => (g k).pullbackCoefficients Φ z v w)
      atTop (𝓝 (B v w))) :
    B = ((G.limit.flow.metric t).pullbackOfLocalDiffeomorph
      (Subtype.val : U → G.limit.sliceCarrier.carrier)
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U)).pullbackCoefficients Φ z := by
  let g0 := (G.limit.flow.metric t).pullbackOfLocalDiffeomorph
    (Subtype.val : U → G.limit.sliceCarrier.carrier)
    (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U)
  let B0 := g0.pullbackCoefficients Φ z
  have hsymm (v w : E) : B v w = B w v := by
    apply tendsto_nhds_unique (hconv v w)
    have heq : (fun k => (g k).pullbackCoefficients Φ z v w) =
        fun k => (g k).pullbackCoefficients Φ z w v := by
      funext k
      exact (g k).symm _ _ _
    rw [heq]
    exact hconv w v
  have hsymm0 (v w : E) : B0 v w = B0 w v := coefficient_symm g0 Φ z v w
  apply eq_of_sharp_comparison B B0 hsymm hsymm0
  intro v δ hδ hδlt
  have htail := hσ.tendsto_atTop.eventually
    (limitNoncollapse_generalized_compact_inner_comparison G
      (isCompact_singleton (x := (Φ z).val)) t ht hδ hδlt)
  have hbounds : ∀ᶠ k in atTop,
      (1 - δ) * B0 v v ≤ (g k).pullbackCoefficients Φ z v v ∧
        (g k).pullbackCoefficients Φ z v v ≤ (1 + δ) * B0 v v := by
    filter_upwards [htail, hread] with k hk hr
    obtain ⟨htk, hr⟩ := hr
    have h := hk.2.2 (Φ z).val (mem_singleton _)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → G.limit.sliceCarrier.carrier) (Φ z)
        (mfderiv (𝓡 3) (𝓡 3) Φ z v)) htk
    rw [← hr (Φ z) (mfderiv (𝓡 3) (𝓡 3) Φ z v)
      (mfderiv (𝓡 3) (𝓡 3) Φ z v)] at h
    exact h
  exact ⟨ge_of_tendsto (hconv v v) (hbounds.mono fun _ h => h.1),
    le_of_tendsto (hconv v v) (hbounds.mono fun _ h => h.2)⟩

end PoincareConjecture.M47

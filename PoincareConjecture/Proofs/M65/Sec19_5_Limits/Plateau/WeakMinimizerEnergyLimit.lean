import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerExtraction
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Coefficients
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.WeakEnergy












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory InnerProductSpace
open scoped Topology InnerProductSpace Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {N : ℕ}

private theorem m65WeakMetric_symm (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (p : M)
    (v w : EuclideanSpace ℝ (Fin N)) :
    m65EmbeddingMetric g e p v w = m65EmbeddingMetric g e p w v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (TangentSpace (𝓡 3) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) p
  have : CompleteSpace (TangentSpace (𝓡 3) p) := FiniteDimensional.complete ℝ _
  unfold m65EmbeddingMetric
  exact M65Interior.ambientMetric_symmetric _ v w

set_option maxHeartbeats 1600000 in






theorem m65WeakDisk_energy_le_of_limit (g : RiemannianMetric 3 M)
    {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (F : ℕ → M65WeakDisk e γ) (G : M65WeakDisk e γ)
    (hu : Tendsto (fun n => (F n).embeddedValue) atTop (𝓝 G.embeddedValue))
    {D E : ℝ} (hd : ∀ n i, ‖(F n).derivative i‖ ≤ D)
    (hweak : ∀ i v, Tendsto (fun n => ⟪(F n).derivative i, v⟫_ℝ) atTop
      (𝓝 ⟪G.derivative i, v⟫_ℝ))
    (henergy : Tendsto (fun n => (F n).energy g) atTop (𝓝 E)) : G.energy g ≤ E := by
  let V := EuclideanSpace ℝ (Fin N)
  let mu : Measure LoopPlane := volume.restrict loopDiskSet
  let L := Lp V 2 mu
  let : TopologicalSpace.PseudoMetrizableSpace M := hemb.toIsInducing.pseudoMetrizableSpace
  let J : StrongDual ℝ V →L[ℝ] V :=
    (toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let A (p : M) : V →L[ℝ] V := J.comp (m65EmbeddingMetric g e p)
  have hA : Continuous A :=
    continuous_const.clm_comp (m65EmbeddingMetric_contMDiff g e he hinj).continuous
  have hAinner (p : M) (v w : V) : ⟪A p v, w⟫_ℝ = m65EmbeddingMetric g e p v w := by
    exact toDual_symm_apply
  obtain ⟨C0, hC0⟩ := compact.exists_bound_of_continuousOn hA.continuousOn
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hAC (p : M) : ‖A p‖ ≤ C := (hC0 p (mem_univ p)).trans (le_max_left _ _)
  have hmeas (Q : M65WeakDisk e γ) : AEStronglyMeasurable (fun z => A (Q.value z)) mu :=
    hA.comp_aestronglyMeasurable (hemb.aestronglyMeasurable_comp_iff.mp
      ((Lp.memLp Q.embeddedValue).1.congr Q.embeddedValue_ae))
  let T (Q : M65WeakDisk e γ) : L →L[ℝ] L :=
    Lp.coefficientL2 (fun z => A (Q.value z)) (hmeas Q) C (ae_of_all _ fun z => hAC _)
  have hT (Q : M65WeakDisk e γ) (v : L) :
      T Q v =ᵐ[mu] fun z => A (Q.value z) (v z) :=
    Lp.coefficientL2_ae _ _ _ _ v
  have hp (Q : M65WeakDisk e γ) (u v : L) :
      (fun z => ⟪u z, (T Q v) z⟫_ℝ) =ᵐ[mu]
        fun z => m65EmbeddingMetric g e (Q.value z) (v z) (u z) := by
    filter_upwards [hT Q v] with z hz
    rw [hz, real_inner_comm, hAinner]
  have hpair (Q : M65WeakDisk e γ) (u v : L) :
      ⟪u, T Q v⟫_ℝ = ∫ z, m65EmbeddingMetric g e (Q.value z) (v z) (u z) ∂mu := by
    rw [L2.inner_def]
    exact integral_congr_ae (hp Q u v)
  have hint (Q : M65WeakDisk e γ) (u v : L) :
      Integrable (fun z => m65EmbeddingMetric g e (Q.value z) (v z) (u z)) mu :=
    (L2.integrable_inner u (T Q v)).congr (hp Q u v)
  have hpos (Q : M65WeakDisk e γ) (v : L) : 0 ≤ ⟪v, T Q v⟫_ℝ := by
    rw [hpair]
    exact integral_nonneg fun z => m65EmbeddingMetric_nonneg g e _ _
  have hsymm (Q : M65WeakDisk e γ) (u v : L) : ⟪u, T Q v⟫_ℝ = ⟪v, T Q u⟫_ℝ := by
    rw [hpair, hpair]
    exact integral_congr_ae (ae_of_all _ fun z => m65WeakMetric_symm g e _ _ _)
  have hE (Q : M65WeakDisk e γ) :
      Q.energy g = (1 / 2 : ℝ) * ∑ i, ⟪Q.derivative i, T Q (Q.derivative i)⟫_ℝ := by
    change (∫ z, (1 / 2 : ℝ) *
      ∑ i, m65EmbeddingMetric g e (Q.value z) (Q.derivative i z) (Q.derivative i z) ∂mu) = _
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hint Q _ _]
    simp only [hpair]
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  have hpoint : ∀ᵐ z ∂mu, Tendsto (fun n => (F (σ n)).value z) atTop (𝓝 (G.value z)) := by
    filter_upwards [hae, ae_all_iff.mpr (fun n => (F n).embeddedValue_ae),
      G.embeddedValue_ae] with z hz hn h0
    apply hemb.tendsto_nhds_iff.mpr
    simpa only [Function.comp_def, hn, h0] using hz
  have hcoef : ∀ᵐ z ∂mu, Tendsto (fun n => A ((F (σ n)).value z)) atTop
      (𝓝 (A (G.value z))) := by
    filter_upwards [hpoint] with z hz
    exact (hA.tendsto _).comp hz
  have hstrong (v : L) : Tendsto (fun n => T (F (σ n)) v) atTop (𝓝 (T G v)) :=
    Lp.tendsto_coefficientL2_apply (fun n => hmeas (F (σ n))) (hmeas G) hC
      (fun n => ae_of_all _ fun z => hAC _) (ae_of_all _ fun z => hAC _) hcoef v
  let low (n : ℕ) (i : Fin 2) : ℝ :=
    2 * ⟪(F (σ n)).derivative i, T (F (σ n)) (G.derivative i)⟫_ℝ -
      ⟪G.derivative i, T (F (σ n)) (G.derivative i)⟫_ℝ
  have hlow (i : Fin 2) : Tendsto (fun n => low n i) atTop
      (𝓝 ⟪G.derivative i, T G (G.derivative i)⟫_ℝ) := by
    have hcross := tendsto_inner_of_bounded_weak_of_tendsto
      (Eventually.of_forall fun n => hd (σ n) i)
      (fun v => (hweak i v).comp hσ.tendsto_atTop) (hstrong (G.derivative i))
    have hfixed : Tendsto (fun n => ⟪G.derivative i, T (F (σ n)) (G.derivative i)⟫_ℝ)
        atTop (𝓝 ⟪G.derivative i, T G (G.derivative i)⟫_ℝ) :=
      (tendsto_const_nhds (x := G.derivative i)).inner (hstrong (G.derivative i))
    have hl := ((tendsto_const_nhds (x := (2 : ℝ))).mul hcross).sub hfixed
    have heq : 2 * ⟪G.derivative i, T G (G.derivative i)⟫_ℝ -
        ⟪G.derivative i, T G (G.derivative i)⟫_ℝ =
        ⟪G.derivative i, T G (G.derivative i)⟫_ℝ := by ring
    rw [heq] at hl
    exact hl
  have hle (n : ℕ) : (1 / 2 : ℝ) * ∑ i, low n i ≤ (F (σ n)).energy g := by
    rw [hE]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro i _
    have hh := hpos (F (σ n)) ((F (σ n)).derivative i - G.derivative i)
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right] at hh
    rw [hsymm (F (σ n)) (G.derivative i) ((F (σ n)).derivative i)] at hh
    dsimp only [low]
    linarith
  have hl := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul
    (tendsto_finsetSum Finset.univ (fun i _ => hlow i))
  rw [← hE G] at hl
  exact le_of_tendsto_of_tendsto hl (henergy.comp hσ.tendsto_atTop)
    (Eventually.of_forall hle)

end PoincareConjecture

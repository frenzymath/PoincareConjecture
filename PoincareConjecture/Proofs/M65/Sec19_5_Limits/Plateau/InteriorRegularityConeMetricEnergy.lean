import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityConeEnergy
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEnergy

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture.M65Interior

theorem coneDisk_metricEnergy_le {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ p (w : EuclideanSpace ℝ (Fin N)), m65EmbeddingMetric g e p w w ≤ C * ‖w‖ ^ 2)
    (P : EuclideanSpace ℝ (Fin 3) → M)
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    {r ρ K : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hv : ContinuousOn v (Icc (-Real.pi) Real.pi))
    (hg : ContDiffOn ℝ 1 (e ∘ P) (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (-Real.pi) Real.pi) (closedBall 0 ρ))
    (hd : MemLp d 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hD : ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) ρ, ‖fderiv ℝ (e ∘ P) y‖ ≤ K)
    (x : LoopPlane) :
    IntegrableOn (m65EmbeddedEnergyDensity g e (coneDiskMap P r v0 v x)
      (coneDiskField (e ∘ P) r v0 v d x)) (closedBall x r) ∧
    (∫ z in closedBall x r,
      m65EmbeddedEnergyDensity g e (coneDiskMap P r v0 v x)
        (coneDiskField (e ∘ P) r v0 v d x) z) ≤
      (C * K ^ 2 / 4) * ∫ θ in Icc (-Real.pi) Real.pi, (‖v θ - v0‖ ^ 2 + ‖d θ‖ ^ 2) := by
  let q := coneDiskMap P r v0 v x
  let D := coneDiskField (e ∘ P) r v0 v d x
  have hL := coneDisk_memLp hr hρ hK hv hg h0 hvb hd hD x
  have hE : IntegrableOn (m65EmbeddedEnergyDensity g e q D) (closedBall x r) :=
    m65EmbeddedEnergyDensity_integrable g e he hinj hemb compact hL.1.1 hL.2
  have hS : IntegrableOn (fun z => ∑ i : Fin 2, ‖D i z‖ ^ 2) (closedBall x r) := by
    apply integrable_finsetSum
    intro i _
    exact (memLp_two_iff_integrable_sq_norm (hL.2 i).1).mp (hL.2 i)
  have hpoint (z : LoopPlane) :
      m65EmbeddedEnergyDensity g e q D z ≤ (C / 2) * ∑ i : Fin 2, ‖D i z‖ ^ 2 := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound (q z) (D i z))
    rw [← Finset.mul_sum] at h
    unfold m65EmbeddedEnergyDensity
    nlinarith only [h]
  refine ⟨hE, ?_⟩
  calc
    _ ≤ ∫ z in closedBall x r, (C / 2) * ∑ i : Fin 2, ‖D i z‖ ^ 2 :=
      integral_mono_ae hE (hS.const_mul (C / 2)) (ae_of_all _ hpoint)
    _ = (C / 2) * ∫ z in closedBall x r, ∑ i : Fin 2, ‖D i z‖ ^ 2 := integral_const_mul _ _
    _ ≤ (C / 2) * ((K ^ 2 / 2) *
        ∫ θ in Icc (-Real.pi) Real.pi, (‖v θ - v0‖ ^ 2 + ‖d θ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (coneDisk_derivativeEnergy_le hr hρ hK hv hg h0 hvb hd hD x) (by positivity)
    _ = _ := by ring

end PoincareConjecture.M65Interior

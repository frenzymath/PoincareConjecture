import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakLimitTarget
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.StrongLimit

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

theorem m64Annulus_observed_sobolev_subsequence {m : ℕ}
    (g : RiemannianMetric n M) (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    {C : ℝ} (hC : ∀ j, (∫ p in interior m64AnnulusDomain,
      m60EnergyDensity g (f j) p) ≤ C) :
    ∃ (k : ℕ → ℕ)
      (u : Lp (EuclideanSpace ℝ (Fin m)) 2 (volume.restrict (interior m64AnnulusDomain)))
      (V : Fin 2 → Lp (EuclideanSpace ℝ (Fin m)) 2
        (volume.restrict (interior m64AnnulusDomain)))
      (hU : ∀ j, MemLp (e ∘ f (k j)) 2 (volume.restrict (interior m64AnnulusDomain)))
      (hV : ∀ j i, MemLp (fun p => fderiv ℝ (e ∘ f (k j)) p
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2
          (volume.restrict (interior m64AnnulusDomain))),
      StrictMono k ∧ Tendsto (fun j => (hU j).toLp (e ∘ f (k j))) atTop (𝓝 u) ∧
      (∀ i, WeakConverges (fun j => (hV j i).toLp
        (fun p => fderiv ℝ (e ∘ f (k j)) p (EuclideanSpace.basisFun (Fin 2) ℝ i))) (V i)) ∧
      (∀ i (phi : LoopPlane → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ interior m64AnnulusDomain →
        (∫ p in interior m64AnnulusDomain, phi p • V i p) =
          -(∫ p in interior m64AnnulusDomain,
            fderiv ℝ phi p (EuclideanSpace.basisFun (Fin 2) ℝ i) • u p)) ∧
      (∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain),
        Tendsto (fun j => e (f (k j) p)) atTop (𝓝 (u p)) ∧ u p ∈ range e) ∧
      (∑ i, ‖V i‖ ^ 2) ≤ liminf (fun j => ∑ i,
        ‖(hV j i).toLp (fun p => fderiv ℝ (e ∘ f (k j)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ i))‖ ^ 2) atTop := by
  let S := interior m64AnnulusDomain
  let E := EuclideanSpace ℝ (Fin m)
  obtain ⟨hU0, z, k, hk, hz, htarget⟩ := m64Annulus_observed_target_subsequence g e he f hf hC
  obtain ⟨hU1, hV1, u, V, l, hl, hu, hV, htest, hliminf⟩ :=
    m64Annulus_observed_weak_subsequence g e he (fun j => f (k j))
      (fun j => hf (k j)) (fun j => hC (k j))
  have hmu : volume.restrict S ≤ (1 : ℝ≥0∞) • volume := by
    simpa only [one_smul] using (Measure.restrict_le_self : volume.restrict S ≤ volume)
  let R : Lp E 2 (volume : Measure LoopPlane) →L[ℝ] Lp E 2 (volume.restrict S) :=
    Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hmu
  have hRcoe (w : Lp E 2 (volume : Measure LoopPlane)) : R w =ᵐ[volume.restrict S] w :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hmu w
  have hRmap (j : ℕ) : R ((hU0 (k j)).toLp (S.indicator (e ∘ f (k j)))) =
      (hU1 j).toLp (e ∘ f (k j)) := by
    apply Lp.ext
    filter_upwards [hRcoe ((hU0 (k j)).toLp (S.indicator (e ∘ f (k j)))),
      ae_restrict_of_ae (hU0 (k j)).coeFn_toLp, (hU1 j).coeFn_toLp,
      ae_restrict_mem isOpen_interior.measurableSet] with p hp hp0 hp1 hpS
    rw [hp, hp0, hp1]
    exact indicator_of_mem hpS _
  have hstrong : Tendsto (fun j => (hU1 j).toLp (e ∘ f (k j))) atTop (𝓝 (R z)) := by
    have hh := (R.continuous.tendsto z).comp hz
    exact hh.congr' (Eventually.of_forall hRmap)
  have heq : u = R z := eq_of_strong_and_weak_limit (hstrong.comp hl.tendsto_atTop) hu
  have hstrongu : Tendsto (fun j => (hU1 (l j)).toLp (e ∘ f (k (l j)))) atTop (𝓝 u) := by
    rw [heq]
    exact hstrong.comp hl.tendsto_atTop
  have hurep : u =ᵐ[volume.restrict S] z := by rw [heq]; exact hRcoe z
  refine ⟨k ∘ l, u, V, (fun j => hU1 (l j)), (fun j i => hV1 (l j) i),
    hk.comp hl, hstrongu, hV, htest, ?_, hliminf⟩
  filter_upwards [htarget, hurep] with p hp hpU
  rw [hpU]
  exact ⟨hp.1.comp hl.tendsto_atTop, hp.2⟩

end PoincareConjecture

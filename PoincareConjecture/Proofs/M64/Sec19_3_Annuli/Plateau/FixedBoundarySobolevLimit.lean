import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SobolevLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakBoundaryTrace

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]

theorem m64Annulus_fixed_boundary_sobolev_subsequence {m : ℕ}
    (g : RiemannianMetric n M) (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 e)
    (hei : IsClosedEmbedding e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    {C : ℝ} (hC : ∀ j, (∫ p in interior m64AnnulusDomain,
      m60EnergyDensity g (f j) p) ≤ C)
    (c0 c1 : ℝ → M)
    (h0 : ∀ j x, f j (annulusPoint x 0) = c0 x)
    (h1 : ∀ j x, f j (annulusPoint x 1) = c1 x) :
    ∃ (k : ℕ → ℕ) (v : LoopPlane → M)
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
      (∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain),
        e (v p) = u p ∧ Tendsto (fun j => f (k j) p) atTop (𝓝 (v p))) ∧
      (∀ i (phi : LoopPlane → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ interior m64AnnulusDomain →
        (∫ p in interior m64AnnulusDomain, phi p • V i p) =
          -(∫ p in interior m64AnnulusDomain,
            fderiv ℝ phi p (EuclideanSpace.basisFun (Fin 2) ℝ i) • u p)) ∧
      (∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi →
        (∫ p in interior m64AnnulusDomain, phi p • V 1 p) +
          (∫ p in interior m64AnnulusDomain,
            fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • u p) =
          ∫ x in Icc (0 : ℝ) curvePeriod,
            phi (annulusPoint x 1) • e (c1 x) - phi (annulusPoint x 0) • e (c0 x)) ∧
      (∑ i, ‖V i‖ ^ 2) ≤ liminf (fun j => ∑ i,
        ‖(hV j i).toLp (fun p => fderiv ℝ (e ∘ f (k j)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ i))‖ ^ 2) atTop := by
  classical
  obtain ⟨k, u, V, hU, hV, hk, hstrong, hweak, htest, htarget, hliminf⟩ :=
    m64Annulus_observed_sobolev_subsequence g e he f hf hC
  let v : LoopPlane → M := fun p =>
    if hp : u p ∈ range e then Classical.choose hp else f 0 0
  have hev : ∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain),
      e (v p) = u p ∧ Tendsto (fun j => f (k j) p) atTop (𝓝 (v p)) := by
    filter_upwards [htarget] with p hp
    have hpv : e (v p) = u p := by
      dsimp only [v]
      rw [dif_pos hp.2]
      exact Classical.choose_spec hp.2
    refine ⟨hpv, hei.isEmbedding.tendsto_nhds_iff.mpr ?_⟩
    rw [hpv]
    exact hp.1
  refine ⟨k, v, u, V, hU, hV, hk, hstrong, hweak, hev, htest, ?_, hliminf⟩
  intro phi hphi
  have huweak : WeakConverges (fun j => (hU j).toLp (e ∘ f (k j))) u :=
    fun L => L.continuous.tendsto u |>.comp hstrong
  have hV1 (j : ℕ) : MemLp (fun p => fderiv ℝ (e ∘ f (k j)) p
      (EuclideanSpace.single (1 : Fin 2) 1)) 2
      (volume.restrict (interior m64AnnulusDomain)) := by
    simpa only [EuclideanSpace.basisFun_apply] using hV j 1
  have hvweak : WeakConverges (fun j => (hV1 j).toLp (fun p =>
      fderiv ℝ (e ∘ f (k j)) p (EuclideanSpace.single (1 : Fin 2) 1))) (V 1) := by
    simpa only [EuclideanSpace.basisFun_apply] using hweak 1
  exact m64Annulus_weak_fixed_boundary_identity (fun j => e ∘ f (k j))
    (fun j => contMDiff_iff_contDiff.mp (he.comp (hf (k j)))) hU hV1 huweak hvweak
    (e ∘ c0) (e ∘ c1) (fun j x => congrArg e (h0 (k j) x))
    (fun j x => congrArg e (h1 (k j) x)) phi hphi

end PoincareConjecture

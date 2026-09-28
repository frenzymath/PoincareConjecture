import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerBoundaryMeasure
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEnergy
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Complex.Basic












set_option autoImplicit false

noncomputable section

open Set MeasureTheory Complex
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture




def M65WeakCircleParameter (β : C(LoopCircle, LoopCircle)) : Prop :=
  β ∈ closure (range (fun h : LoopCircle ≃ₜ LoopCircle =>
    (⟨h, h.continuous⟩ : C(LoopCircle, LoopCircle))))




def m65DiskCoordinateL2 {N : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet))
    (j : Fin N) : Lp ℝ 2 (volume.restrict loopDiskSet) :=
  ((Lp.memLp u).eval_piLp j).toLp (fun z => u z j)



theorem m65DiskCoordinateL2_coe {N : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet))
    (j : Fin N) : m65DiskCoordinateL2 u j =ᵐ[volume.restrict loopDiskSet]
      fun z => u z j := ((Lp.memLp u).eval_piLp j).coeFn_toLp






structure M65WeakDisk {M : Type u} {N : ℕ}
    (e : M → EuclideanSpace ℝ (Fin N)) (γ : LoopCircle → M) where
  value : LoopPlane → M
  embeddedValue : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet)
  embeddedValue_ae : embeddedValue =ᵐ[volume.restrict loopDiskSet] fun z => e (value z)
  derivative : Fin 2 → Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet)
  parameter : C(LoopCircle, LoopCircle)
  weakly_monotone : M65WeakCircleParameter parameter
  boundary : Fin N → Lp ℝ 2 m65CircleBoundaryMeasure
  boundary_ae : ∀ j, m65CircleBoundaryPullback (boundary j) =ᵐ[
      volume.restrict (Icc (-Real.pi) Real.pi)]
    fun t => e (γ (parameter ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩)) j
  weak_trace : ∀ j, M65DiskWeakTrace (m65DiskCoordinateL2 embeddedValue j)
    (fun i => m65DiskCoordinateL2 (derivative i) j) (m65CircleBoundaryPullback (boundary j))

namespace M65WeakDisk

variable {M : Type u} {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}




def Normalized (F : M65WeakDisk e γ) (a b c : LoopCircle) : Prop :=
  let p : LoopCircle := ⟨orthonormalBasisOneI.repr 1, by simp⟩
  let n : LoopCircle := ⟨orthonormalBasisOneI.repr (-1), by simp⟩
  let ip : LoopCircle := ⟨orthonormalBasisOneI.repr I, by simp⟩
  let im : LoopCircle := ⟨orthonormalBasisOneI.repr (-I), by simp⟩
  F.parameter p = a ∧ F.parameter n = b ∧ (F.parameter ip = c ∨ F.parameter im = c)

variable [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]




def energy (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M) : ℝ :=
  ∫ z in loopDiskSet, m65EmbeddedEnergyDensity g e F.value (fun i z => F.derivative i z) z




def MinimizesNormalizedEnergy (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M)
    (a b c : LoopCircle) : Prop :=
  F.Normalized a b c ∧ ∀ G : M65WeakDisk e γ, G.Normalized a b c → F.energy g ≤ G.energy g




def MinimizesEnergy (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M) : Prop :=
  ∀ G : M65WeakDisk e γ, F.energy g ≤ G.energy g





theorem energy_integrable (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M)) :
    IntegrableOn (m65EmbeddedEnergyDensity g e F.value (fun i z => F.derivative i z))
      loopDiskSet volume :=
  m65EmbeddedEnergyDensity_integrable g e he hinj hemb compact
    ((Lp.memLp F.embeddedValue).1.congr F.embeddedValue_ae) (fun i => Lp.memLp (F.derivative i))

end M65WeakDisk

end PoincareConjecture

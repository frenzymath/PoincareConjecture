import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Weak.MinimizerBoundaryMeasure
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.InteriorRegularityEnergy
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Complex.Basic

/-!
# The genuine global weak Plateau class

The admissible boundary parameter varies over the uniform closure of
actual circle homeomorphisms. The literal Green identity connects that
continuous boundary to the actual interior L2 values and derivatives.
Only the three pin values are fixed in the normalized minimum.
Source: Morrey ICM 1950, pp. 183-185, for Morgan--Tian Lemma 19.2,
printed pp. 437-438; M65 derivation 32.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Complex
open scoped Topology Manifold ContDiff

universe u

namespace PoincareMT

/-- Weak monotonicity means an actual uniform limit of circle
homeomorphisms. The compact-open topology is uniform convergence on
the compact circle. Source: Morrey ICM pp. 183-185, derivation 32. -/
def M65WeakCircleParameter (β : C(LoopCircle, LoopCircle)) : Prop :=
  β ∈ closure (range (fun h : LoopCircle ≃ₜ LoopCircle =>
    (⟨h, h.continuous⟩ : C(LoopCircle, LoopCircle))))

/-- The actual scalar coordinate class of a vector disk L2 class.
Source: Morrey ICM pp. 183-185, MT Lemma 19.2, pp. 437-438;
derivation 32, actual weak class. -/
def m65DiskCoordinateL2 {N : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet))
    (j : Fin N) : Lp ℝ 2 (volume.restrict loopDiskSet) :=
  ((Lp.memLp u).eval_piLp j).toLp (fun z => u z j)

/-- The coordinate class represents the actual coordinate almost
everywhere. Source: Morrey ICM pp. 183-185, derivation 32. -/
theorem m65DiskCoordinateL2_coe {N : ℕ}
    (u : Lp (EuclideanSpace ℝ (Fin N)) 2 (volume.restrict loopDiskSet))
    (j : Fin N) : m65DiskCoordinateL2 u j =ᵐ[volume.restrict loopDiskSet]
      fun z => u z j := ((Lp.memLp u).eval_piLp j).coeFn_toLp

/-- Actual target-valued W1,2 disks with variable weakly monotone trace.
The same coordinate Green identities fix both the true weak derivatives
and the prescribed Sobolev boundary. No regular representative or
minimality is assumed. Source: Morrey ICM pp. 183-185, MT Lemma 19.2,
pp. 437-438; derivation 32. -/
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

/-- The normalized class fixes only three boundary values, retaining
both actual choices of the third domain pin. Source: Morrey ICM
pp. 183-185, MT Lemma 19.2, pp. 437-438; derivation 32. -/
def Normalized (F : M65WeakDisk e γ) (a b c : LoopCircle) : Prop :=
  let p : LoopCircle := ⟨orthonormalBasisOneI.repr 1, by simp⟩
  let n : LoopCircle := ⟨orthonormalBasisOneI.repr (-1), by simp⟩
  let ip : LoopCircle := ⟨orthonormalBasisOneI.repr I, by simp⟩
  let im : LoopCircle := ⟨orthonormalBasisOneI.repr (-I), by simp⟩
  F.parameter p = a ∧ F.parameter n = b ∧ (F.parameter ip = c ∨ F.parameter im = c)

variable [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The literal metric half-energy of the same target representative
and actual weak derivative classes. Source: Morrey ICM pp. 183-185,
MT Lemma 19.2, pp. 437-438; derivation 32. -/
def energy (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M) : ℝ :=
  ∫ z in loopDiskSet, m65EmbeddedEnergyDensity g e F.value (fun i z => F.derivative i z) z

/-- The normalized minimum compares all actual weak competitors and
allows their whole boundary parameters to vary subject only to the
three pins. Source: Morrey ICM pp. 183-185, derivations 32 and 39. -/
def MinimizesNormalizedEnergy (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M)
    (a b c : LoopCircle) : Prop :=
  F.Normalized a b c ∧ ∀ G : M65WeakDisk e γ, G.Normalized a b c → F.energy g ≤ G.energy g

/-- The unpinned minimum compares every genuine weakly monotone trace;
deriving it from normalization requires actual conformal transport.
Source: Morrey ICM pp. 183-185, derivations 32 and 39. -/
def MinimizesEnergy (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M) : Prop :=
  ∀ G : M65WeakDisk e γ, F.energy g ≤ G.energy g

/-- All admissible weak disks have genuinely integrable energy under
the actual compact smooth embedding hypotheses. This is derived from
their real L2 fields and the shared metric producer. Source: Morrey
ICM pp. 183-185, MT Lemma 19.2, pp. 437-438; derivation 32. -/
theorem energy_integrable (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M)) :
    IntegrableOn (m65EmbeddedEnergyDensity g e F.value (fun i z => F.derivative i z))
      loopDiskSet volume :=
  m65EmbeddedEnergyDensity_integrable g e he hinj hemb compact
    ((Lp.memLp F.embeddedValue).1.congr F.embeddedValue_ae) (fun i => Lp.memLp (F.derivative i))

end M65WeakDisk

end PoincareMT

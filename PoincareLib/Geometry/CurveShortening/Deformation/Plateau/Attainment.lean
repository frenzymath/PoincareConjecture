import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.AttainmentIdentities

/-!
# The five-input Plateau attainment assembly

Each input is the literal analytic endpoint of its owner. Smoothness,
regularity and embeddedness of the boundary are hypotheses of those
producers. The conditional assembly below constructs the frozen actual
Lipschitz disk and proves its area equals the filling infimum.
Source: MT Lemma 19.2, printed p. 438; M65 derivation 41.
-/

set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {N : ℕ} (g : RiemannianMetric 3 M) (connection : LeviCivitaData g)
  (e : M → EuclideanSpace ℝ (Fin N)) (γ : C1FreeLoopSpace (M := M))
  (a b c : LoopCircle)

/-- The normalized minimum is over the actual weakly monotone class;
its energy bound is against the frozen Lipschitz filling infimum.
Source: Morrey ICM pp. 183-185, MT 19.2, p. 438; derivation 41. -/
def M65PlateauWeakMinimizerInput : Prop :=
  ∃ F : M65WeakDisk e (γ : LoopCircle → M),
    F.MinimizesNormalizedEnergy g a b c ∧ F.energy g ≤ fillingArea g γ

/-- Inner variations produce actual weak conformality. The proved
M65WeakDisk.energy_eq_area then supplies literal E = A.
Source: Morrey ICM pp. 183-185, MT 19.2, p. 438; derivation 39. -/
def M65PlateauConformalityInput : Prop :=
  ∀ F : M65WeakDisk e (γ : LoopCircle → M),
    F.MinimizesNormalizedEnergy g a b c → F.Conformal g

/-- The actual weak minimum has a smooth harmonic representative with
its original weak values and derivatives. Source: Morrey ICM pp. 183-185,
MT 19.2, p. 438; derivations 38 and 41. -/
def M65PlateauInteriorRegularityInput : Prop :=
  ∀ F : M65WeakDisk e (γ : LoopCircle → M),
    F.MinimizesNormalizedEnergy g a b c →
      ∃ f : LoopPlane → M, M65InteriorDiskRepresentative connection F f

/-- Boundary regularity extends the same representative and keeps its
original weakly monotone trace. The within-C1 conclusion is verbatim the
minimal disk record's boundary_regular field; strictness is separate.
Source: Heinz 1970, pp. 99-105, MT 19.2, p. 438; derivations 35 and 41. -/
def M65PlateauBoundaryRegularityInput : Prop :=
  ∀ F : M65WeakDisk e (γ : LoopCircle → M),
    F.MinimizesNormalizedEnergy g a b c → F.Conformal g →
      ∀ q : LoopPlane → M, M65InteriorDiskRepresentative connection F q →
        ∃ f : LoopPlane → M, EqOn f q (ball (0 : LoopPlane) 1) ∧
          M65InteriorDiskRepresentative connection F f ∧
          ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet ∧
          ∀ z : LoopCircle, f z = γ (F.parameter z)

/-- The shared half-disk expansion and unique continuation give strict
trace and finite actual closed-disk branches. Neither is assumed by the
weak minimum or boundary regularity input. Source: Heinz 1970, pp. 99-105,
MT 19.2, p. 438; derivation 41 and the shared Hartman-Wintner endpoint. -/
def M65PlateauStrictTraceInput : Prop :=
  ∀ F : M65WeakDisk e (γ : LoopCircle → M),
    F.MinimizesNormalizedEnergy g a b c → F.Conformal g →
      ∀ f : LoopPlane → M, M65InteriorDiskRepresentative connection F f →
        ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet →
          (∀ z : LoopCircle, f z = γ (F.parameter z)) →
            ∃ β : LoopCircle ≃ₜ LoopCircle, (∀ z, β z = F.parameter z) ∧
              {z : LoopPlane | z ∈ loopDiskSet ∧
                mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z = 0}.Finite

/-- The five literal analytic inputs construct the actual least-area
Lipschitz disk with all fields consumed by Lemma 19.4. This conditional
assembly becomes Plateau existence only after its five inputs are
proved. Source: MT 19.2, p. 438; derivation 41. -/
theorem m65Plateau_attainment_of_five_inputs
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (weak_minimizer : M65PlateauWeakMinimizerInput g e γ a b c)
    (conformality : M65PlateauConformalityInput g e γ a b c)
    (interior_regularity : M65PlateauInteriorRegularityInput g connection e γ a b c)
    (boundary_regularity : M65PlateauBoundaryRegularityInput g connection e γ a b c)
    (strict_trace : M65PlateauStrictTraceInput g connection e γ a b c) :
    Nonempty (M65MinimalDisk g connection γ) := by
  obtain ⟨F, hmin, henergy⟩ := weak_minimizer
  have hconf := conformality F hmin
  obtain ⟨q, hq⟩ := interior_regularity F hmin
  obtain ⟨f, _hext, hf, hboundary, htrace⟩ := boundary_regularity F hmin hconf q hq
  obtain ⟨β, hβ, hbranches⟩ := strict_trace F hmin hconf f hf hboundary htrace
  have hb (z : LoopCircle) : f z = γ (β z) := by rw [hβ z]; exact htrace z
  let D := m65Attainment_spanningDisk g γ f hboundary β hb
  have harea : D.area = F.area g := m65Attainment_area_eq F he hinj hf
  have hE : D.area = F.energy g := harea.trans (F.energy_eq_area g hconf).symm
  have hbelow : BddBelow (range (fun D' : LipschitzSpanningDisk g γ => D'.area)) := by
    refine ⟨0, ?_⟩
    rintro t ⟨D', rfl⟩
    exact D'.area_nonnegative
  have hinf : fillingArea g γ ≤ D.area := csInf_le hbelow (mem_range_self D)
  exact ⟨{
    disk := D
    area_eq := le_antisymm (hE.trans_le henergy) hinf
    interior_smooth := hf.smooth
    weakly_conformal := m65Attainment_conformal F he hinj hf hconf
    harmonic := hf.harmonic
    boundary_regular := hboundary
    finite_branches := hbranches
  }⟩

end PoincareMT

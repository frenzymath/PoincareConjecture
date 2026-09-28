import PoincareConjecture.Proofs.M59.Mathlib.FiniteChartApproximation
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.SmoothFamilies
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.CubeCircleDomain

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareConjecture

variable {M : Type u} [MetricSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m59_cube_loop_approximation (n : Nat)
    (F : C((Fin n → I) × LoopCircle, M)) (p : M)
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ G : C((Fin n → I), C1FreeLoopSpace (M := M)),
      (∀ v z, dist (G v z) (F (v, z)) < epsilon) ∧
      ∀ v, (∀ z, F (v, z) = p) → G v = constantC1Loop p := by
  classical
  let : LocallyCompactSpace (m59CubeCircleDomain n) :=
    (m59CubeCircleDomain n).isOpen.locallyCompactSpace
  let f := F.comp (m59CubeCircleRetraction n)
  have hS : IsCompact (range (m59CubeCircleInclusion n)) :=
    isCompact_range (m59CubeCircleInclusion n).continuous
  obtain ⟨g, _, herr, hfix, hsmooth⟩ := Proofs.M59.exists_compact_manifold_approximation
    𝓘(ℝ, (Fin n → ℝ) × LoopPlane) (𝓡 3) f f.continuous hS p he
  let T := Proofs.M59.openMapExtension (m59CubeCircleDomain n) g p
  let a : (Fin n → I) → (Fin n → ℝ) := fun v i => (v i : ℝ)
  have ha : Continuous a := continuous_pi fun i =>
    continuous_subtype_val.comp (continuous_apply i)
  have hT (v : Fin n → I) (z : LoopCircle) :
      ContMDiffAt 𝓘(ℝ, (Fin n → ℝ) × LoopPlane) (𝓡 3) 1 T (a v, z.val) :=
    (Proofs.M59.contMDiffAt_openMapExtension (m59CubeCircleDomain n) g p
      (m59CubeCircleInclusion n (v, z))
      (hsmooth _ (mem_range_self (v, z)))).of_le (by simp)
  let G0 : (Fin n → I) → C1FreeLoopSpace (M := M) :=
    fun v => m59SmoothFamilyLoop T (a v) (hT v)
  have hG0 : Continuous G0 := continuous_m59SmoothFamilyLoop T a ha hT
  have hvalues (v : Fin n → I) (z : LoopCircle) :
      G0 v z = g (m59CubeCircleInclusion n (v, z)) :=
    (m59SmoothFamilyLoop_apply T (a v) (hT v) z).trans
      (Proofs.M59.openMapExtension_apply (m59CubeCircleDomain n) g p
        (m59CubeCircleInclusion n (v, z)))
  have hf (v : Fin n → I) (z : LoopCircle) :
      f (m59CubeCircleInclusion n (v, z)) = F (v, z) := by
    change F (m59CubeCircleRetraction n (m59CubeCircleInclusion n (v, z))) = F (v, z)
    rw [m59CubeCircleRetraction_inclusion]
  let G : (Fin n → I) → C1FreeLoopSpace (M := M) := fun v =>
    if ∀ z, F (v, z) = p then constantC1Loop p else G0 v
  have hGG0 (v : Fin n → I) (z : LoopCircle) : G v z = G0 v z := by
    dsimp only [G]
    split_ifs with h
    · exact ((hvalues v z).trans (hfix _ ((hf v z).trans (h z)))).symm
    · rfl
  refine ⟨⟨G, continuous_of_loop_values_eq hG0 hGG0⟩, ?_, ?_⟩
  · intro v z
    change dist (G v z) (F (v, z)) < epsilon
    rw [hGG0, hvalues, ← hf]
    exact herr _
  · intro v hv
    exact if_pos hv

end PoincareConjecture

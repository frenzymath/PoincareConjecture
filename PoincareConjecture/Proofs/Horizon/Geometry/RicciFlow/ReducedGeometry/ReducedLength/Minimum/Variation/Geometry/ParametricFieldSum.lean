import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.Algebra.Support










set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "P" => ModelWithCorners.prod (𝓘(ℝ, ℝ)) (𝓡 n)

set_option backward.isDefEq.respectTransparency false in
theorem parametricField_lift_smooth
    (X : ℝ → (x : M) → TangentSpace (𝓡 n) x) (D : Set (ℝ × M))
    (hX : ContMDiffOn P ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × M ↦ (⟨z.2, X z.1 z.2⟩ : TangentBundle (𝓡 n) M)) D) :
    ContMDiffOn P ((P).prod (𝓘(ℝ, ℝ × V))) ∞
      (fun z : ℝ × M ↦ (⟨z, (0, X z.1 z.2)⟩ : TangentBundle P (ℝ × M))) D := by
  have htime : ContMDiff P ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) ∞
      (fun z : ℝ × M ↦ (⟨z.1, (0 : ℝ)⟩ : TangentBundle (𝓘(ℝ, ℝ)) ℝ)) :=
    (Bundle.contMDiff_zeroSection (IB := 𝓘(ℝ, ℝ)) (F := ℝ) (𝕜 := ℝ)
      (E := (TangentSpace (𝓘(ℝ, ℝ)) : ℝ → Type _))).comp contMDiff_fst
  exact contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn
    (htime.contMDiffOn.prodMk hX)

set_option backward.isDefEq.respectTransparency false in
theorem weightedParametricField_smooth {ι : Type*} [Fintype ι]
    (ρ : ι → ℝ → ℝ) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (U : ι → Set ℝ) (O : ι → Set M) (hU : ∀ i, IsOpen (U i)) (hO : ∀ i, IsOpen (O i))
    (X : ι → ℝ → (x : M) → TangentSpace (𝓡 n) x)
    (hX : ∀ i, ContMDiffOn P ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × M ↦ (⟨z.2, X i z.1 z.2⟩ : TangentBundle (𝓡 n) M)) (U i ×ˢ O i)) :
    ContMDiffOn P ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × M ↦
        (⟨z.2, ∑ i, ρ i z.1 • X i z.1 z.2⟩ : TangentBundle (𝓡 n) M))
      (⋂ i, ((tsupport (ρ i))ᶜ ×ˢ Set.univ) ∪ (U i ×ˢ O i)) := by
  classical
  let D : Set (ℝ × M) := ⋂ i, ((tsupport (ρ i))ᶜ ×ˢ Set.univ) ∪ (U i ×ˢ O i)
  let A : ι → (z : ℝ × M) → TangentSpace P z := fun i z ↦ (0, X i z.1 z.2)
  have hAi (i : ι) : ContMDiffOn P ((P).prod (𝓘(ℝ, ℝ × V))) ∞
      (fun z : ℝ × M ↦ (⟨z, ρ i z.1 • A i z⟩ : TangentBundle P (ℝ × M))) D := by
    intro z hz
    have hz' := Set.mem_iInter.mp hz i
    rcases hz' with hz0 | hzU
    · have hN : IsOpen ((tsupport (ρ i))ᶜ ×ˢ (Set.univ : Set M)) :=
        (isClosed_tsupport (ρ i)).isOpen_compl.prod isOpen_univ
      apply (Bundle.contMDiffAt_zeroSection (IB := P) (F := ℝ × V)
        (E := TangentSpace P) (n := ∞) (x := z)).congr_of_eventuallyEq
          (f₁ := fun w : ℝ × M ↦ (⟨w, ρ i w.1 • A i w⟩ : TangentBundle P (ℝ × M))) ?_
        |>.contMDiffWithinAt
      filter_upwards [hN.mem_nhds hz0] with w hw
      have hzero : ρ i w.1 = 0 := by
        by_contra hn
        exact hw.1 (subset_tsupport (ρ i) (Function.mem_support.mpr hn))
      simp [hzero, Bundle.zeroSection]
    · have hs := ((hρ i).contMDiff.comp contMDiff_fst).contMDiffOn.smul_section
        (parametricField_lift_smooth (X i) (U i ×ˢ O i) (hX i))
      exact (hs.contMDiffAt ((hU i).prod (hO i) |>.mem_nhds hzU)).contMDiffWithinAt
  have hsum : ContMDiffOn P ((P).prod (𝓘(ℝ, ℝ × V))) ∞
      (fun z : ℝ × M ↦
        (⟨z, ∑ i, ρ i z.1 • A i z⟩ : TangentBundle P (ℝ × M))) D :=
    ContMDiffOn.sum_section (fun i _ ↦ hAi i)
  have hproj : ContMDiff ((P).prod (𝓘(ℝ, ℝ × V))) ((𝓡 n).prod (𝓡 n)) ∞
      (tangentMap P (𝓡 n) (@Prod.snd ℝ M)) :=
    (contMDiff_snd (n := ∞)).contMDiff_tangentMap (by simp)
  have h := hproj.comp_contMDiffOn hsum
  apply h.congr
  intro z hz
  change (⟨z.2, ∑ i, ρ i z.1 • X i z.1 z.2⟩ : TangentBundle (𝓡 n) M) =
    tangentMap P (𝓡 n) (@Prod.snd ℝ M) ⟨z, ∑ i, ρ i z.1 • A i z⟩
  rw [tangentMap_prodSnd]
  apply congrArg (fun v : TangentSpace (𝓡 n) z.2 ↦
    (⟨z.2, v⟩ : TangentBundle (𝓡 n) M))
  change (∑ i, ρ i z.1 • X i z.1 z.2) = (∑ i, ρ i z.1 • A i z).2
  calc
    _ = ∑ i, (ContinuousLinearMap.snd ℝ ℝ V) (ρ i z.1 • A i z) := rfl
    _ = _ := (map_sum (ContinuousLinearMap.snd ℝ ℝ V) _ _).symm

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

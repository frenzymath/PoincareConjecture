import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.exists_rescaled_product (P : OriginalDiskProduct e R j)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1) :
    ∃ Q : OriginalDiskProduct e R j, ∀ x : V2 × ℝ, Q.map x = P.map (x.1, δ * x.2) := by
  let r : (V2 × ℝ) →ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      (δ • (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)
  have hrmap : MapsTo r (D ×ˢ I) (D ×ˢ I) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    change -1 ≤ δ * x.2 ∧ δ * x.2 ≤ 1
    have hlo := mul_le_mul_of_nonneg_left hx.2.1 hδ.le
    have hhi := mul_le_mul_of_nonneg_left hx.2.2 hδ.le
    constructor <;> nlinarith
  have hri : Function.Injective r := by
    intro x y hxy
    have hfirst := congrArg (fun z : V2 × ℝ => z.1) hxy
    have hsecond := congrArg (fun z : V2 × ℝ => z.2) hxy
    exact Prod.ext hfirst (mul_left_cancel₀ hδ.ne' hsecond)
  have hball := (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod
    (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  have hr : FinitePiecewiseAffineOn r K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine r⟩
  let f : V2 × ℝ → X := P.map ∘ r
  have hf : PolyhedralPLInCharts e f (D ×ˢ I) := by
    have h := P.polyhedral.comp_finitePiecewiseAffineOn K hK hr
      (fun x hx => hrmap (hKs.subset hx))
    exact hKs ▸ h
  have hfi : InjOn f (D ×ˢ I) := fun x hx y hy hxy =>
    hri (P.injective (hrmap hx) (hrmap hy) hxy)
  let : CompactSpace (D ×ˢ I : Set (V2 × ℝ)) :=
    isCompact_iff_compactSpace.mp ((isCompact_closedBall (0 : V2) 1).prod isCompact_Icc)
  let Q : OriginalDiskProduct e R j := {
    map := f
    polyhedral := hf
    injective := hfi
    embedding := hf.continuousOn.domRestrict.isClosedEmbedding
      (fun x y hxy => Subtype.ext (hfi x.property y.property hxy))
    inside := P.inside.comp hrmap
    central := by
      intro z hz
      change P.map (z, δ * 0) = j z
      rw [mul_zero]
      exact P.central z hz
    proper := fun x hx => P.proper (r x) (hrmap hx) }
  exact ⟨Q, fun _ => rfl⟩

end PoincareConjecture.M76

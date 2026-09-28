import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskProduct
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

namespace OriginalDiskProduct


def slice (P : OriginalDiskProduct e R j) (t : ℝ) : V2 → X := fun z => P.map (z, t)



theorem polyhedral_slice (P : OriginalDiskProduct e R j) {t : ℝ} (ht : t ∈ I) :
    PolyhedralPLInCharts e (P.slice t) D := by
  let a : V2 →ᴬ[ℝ] E :=
    (ContinuousAffineMap.id ℝ V2).prod (ContinuousAffineMap.const ℝ V2 t)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKD, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  have ha : FinitePiecewiseAffineOn a K.space :=
    ⟨K, hK, rfl, K.affineOnFaces_affine a⟩
  have h := P.polyhedral.comp_finitePiecewiseAffineOn K hK ha
    (fun z hz => show a z ∈ D ×ˢ I from ⟨hKD.subset hz, ht⟩)
  exact hKD ▸ h



theorem embedding_slice (P : OriginalDiskProduct e R j) {t : ℝ} (ht : t ∈ I) :
    Topology.IsEmbedding (fun z : D => P.slice t z) := by
  have hinc : Topology.IsEmbedding (fun z : D => ((z : V2), t)) :=
    (isEmbedding_prodMkLeft t).comp Topology.IsEmbedding.subtypeVal
  have hsource := hinc.codRestrict (D ×ˢ I) (fun z => ⟨z.property, ht⟩)
  exact P.embedding.isEmbedding.comp hsource


theorem slice_inside (P : OriginalDiskProduct e R j) {t : ℝ} (ht : t ∈ I) :
    MapsTo (P.slice t) D R := fun _ hz => P.inside ⟨hz, ht⟩


theorem slice_proper (P : OriginalDiskProduct e R j) {t : ℝ} (ht : t ∈ I) (z : D) :
    P.slice t z ∈ frontier R ↔ (z : V2) ∈ Q := P.proper _ ⟨z.property, ht⟩



theorem slice_image (P : OriginalDiskProduct e R j) (t : ℝ) :
    P.slice t '' D = P.map '' (D ×ˢ ({t} : Set ℝ)) := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨(z, t), ⟨hz, rfl⟩, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    have ht : z.2 = t := hz.2
    refine ⟨z.1, hz.1, ?_⟩
    change P.map (z.1, t) = P.map z
    rw [← ht]


theorem disjoint_slice_images (P : OriginalDiskProduct e R j)
    {t u : ℝ} (ht : t ∈ I) (hu : u ∈ I) (htu : t ≠ u) :
    Disjoint (P.slice t '' D) (P.slice u '' D) := by
  apply disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
  have heq := P.injective (show (w, u) ∈ D ×ˢ I from ⟨hw, hu⟩)
    (show (z, t) ∈ D ×ˢ I from ⟨hz, ht⟩) hwz
  exact htu (congrArg (fun x : E => x.2) heq).symm

end OriginalDiskProduct
end PoincareConjecture.M76

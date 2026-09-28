import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedSphereSubregion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedSphereFiniteCarrier
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveFiberRestriction

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere

theorem PLDomain.exists_finitePL_punctured_subregion_model
    {X E ι κ ν : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite κ] [Finite ν]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X} {M : Set E}
    (hD : PLDomain e D) (hDc : IsConnected D) (hDR : D ⊆ R)
    (A r : κ → Set V4) (hA : ∀ i, IsFinitePLBallPair V3 (A i) (r i))
    (hAS : ∀ i, A i ⊆ Sphere)
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hAo : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (A i \ r i)))
    (f : X → E)
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (G : R ≃ₜ M) (hG : ∀ x : R, (G x : E) = f x)
    (C : M ≃ₜ (Sphere \ ⋃ i, A i \ r i : Set V4)) (hC : C.IsFinitePL)
    (hmark : ∀ x : R, (x : X) ∈ frontier R ↔ (C (G x) : V4) ∈ ⋃ i, r i)
    (S : ν → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier D = ⋃ i, S i) :
    let T := fun i => (fun x : R => (C (G x) : V4)) ''
      ((Subtype.val : R → X) ⁻¹' S i)
    ∃ B : ν → Set V4,
      (∀ i, IsFinitePLBallPair V3 (B i) (T i) ∧ B i ⊆ Sphere ∧
        IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (B i \ T i))) ∧
      Pairwise (fun i j => Disjoint (B i) (B j)) ∧
      ∃ (u : D ≃ₜ (f '' D)) (H : (f '' D) ≃ₜ (Sphere \ ⋃ i, B i \ T i : Set V4)),
        H.IsFinitePL ∧ (∀ x : D, (u x : E) = f x) ∧
        (∀ x : D, (H (u x) : V4) = C (G ⟨x,hDR x.property⟩)) ∧
        (∀ i (x : D), (x : X) ∈ S i ↔ (H (u x) : V4) ∈ T i) ∧
        ∀ x : D, (x : X) ∈ frontier D ↔ (H (u x) : V4) ∈ ⋃ i, T i := by
  classical
  let T := fun i => (fun x : R => (C (G x) : V4)) ''
    ((Subtype.val : R → X) ⁻¹' S i)
  obtain ⟨B,hB,hBdis,_,hBP,_⟩ := hD.exists_punctured_subregion_model
    hDc hDR A r hA hAS hAdis hAo f hf G hG C hC hmark S sS hSdis hfront
  let P := Sphere \ ⋃ i, B i \ T i
  have hMDM : f '' D ⊆ M := by
    rintro _ ⟨x,hx,rfl⟩
    exact hG ⟨x,hDR hx⟩ ▸ (G ⟨x,hDR hx⟩).property
  have hDmark (x : R) : (x : X) ∈ D ↔ (G x : E) ∈ f '' D := by
    constructor
    · exact fun hx => ⟨x,hx,(hG x).symm⟩
    · rintro ⟨y,hy,hyx⟩
      have heq : (⟨y,hDR hy⟩ : R) = x :=
        G.injective (Subtype.ext ((hG ⟨y,hDR hy⟩).trans hyx))
      exact congrArg Subtype.val heq ▸ hy
  let u := G.restrictSubsets hDR hMDM hDmark
  have hu (x : D) : (u x : E) = f x := hG ⟨x,hDR x.property⟩
  have hPQ : P ⊆ Sphere \ ⋃ i, A i \ r i := by
    intro z hz
    obtain ⟨x,_,hxz⟩ := hBP.symm.subset hz
    exact hxz ▸ (C (G x)).property
  have hmem (x : M) : (x : E) ∈ f '' D ↔ (C x : V4) ∈ P := by
    constructor
    · rintro ⟨y,hy,hyx⟩
      apply hBP.subset
      refine ⟨⟨y,hDR hy⟩,hy,?_⟩
      exact congrArg (fun z : M => (C z : V4))
        (Subtype.ext ((hG ⟨y,hDR hy⟩).trans hyx))
    · intro hx
      obtain ⟨y,hy,hyx⟩ := hBP.symm.subset hx
      have heq : G y = x := C.injective (Subtype.ext hyx)
      exact ⟨y,hy,(hG y).symm.trans (congrArg Subtype.val heq)⟩
  obtain ⟨K,hK,hKs⟩ := Geometry.CubicalThreeSphere.exists_finite_punctured_sphere_carrier
    B T (fun i => (hB i).1) (fun i => (hB i).2.1) hBdis (fun i => (hB i).2.2)
  let H := C.restrictSubsets hMDM hPQ hmem
  have hH : H.IsFinitePL := hC.restrictSubsets_of_target hMDM hPQ hmem K hK hKs
  have hval (x : D) : (H (u x) : V4) = C (G ⟨x,hDR x.property⟩) := rfl
  have hrim (i) (x : D) : (x : X) ∈ S i ↔ (H (u x) : V4) ∈ T i := by
    rw [hval]
    constructor
    · exact fun hx => ⟨⟨x,hDR x.property⟩,hx,rfl⟩
    · rintro ⟨y,hy,hyx⟩
      have heq : y = (⟨x,hDR x.property⟩ : R) :=
        G.injective (C.injective (Subtype.ext hyx))
      exact congrArg Subtype.val heq ▸ hy
  refine ⟨B,hB,hBdis,u,H,hH,hu,hval,hrim,?_⟩
  intro x
  rw [hfront]
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i,(hrim i x).mp hi⟩
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i,(hrim i x).mpr hi⟩

end PoincareConjecture.M76

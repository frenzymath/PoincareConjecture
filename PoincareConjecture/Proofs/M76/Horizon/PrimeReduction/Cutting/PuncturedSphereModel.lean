import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalDiskPuncturedComponents









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere

variable {X E ι : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def HasPuncturedSphereModel (e : ι → OpenPartialHomeomorph X V3)
    (f : X → E) (R : Set X) : Prop :=
  (∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target) ∧
  ∃ (n : ℕ) (A r : Fin n → Set V4) (M : Set E)
    (G : R ≃ₜ M) (C : M ≃ₜ (Sphere \ ⋃ i, A i \ r i : Set V4)),
    (∀ i, IsFinitePLBallPair V3 (A i) (r i) ∧ A i ⊆ Sphere ∧
      IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (A i \ r i))) ∧
    Pairwise (fun i j => Disjoint (A i) (A j)) ∧
    (∀ x : R, (G x : E) = f x) ∧ C.IsFinitePL ∧
    ∀ x : R, (x : X) ∈ frontier R ↔ (C (G x) : V4) ∈ ⋃ i, r i

def HasNoPuncturedSphereComponents (e : ι → OpenPartialHomeomorph X V3)
    (f : X → E) (Q : Set X) : Prop :=
  ∀ x ∈ Q, ¬ HasPuncturedSphereModel e f (connectedComponentIn Q x)

theorem HasPuncturedSphereModel.of_marked_model
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R : Set X} {M : Set E}
    {κ : Type*} [Finite κ]
    (A r : κ → Set V4) (hA : ∀ i, IsFinitePLBallPair V3 (A i) (r i))
    (hAS : ∀ i, A i ⊆ Sphere)
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hAo : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (A i \ r i)))
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (G : R ≃ₜ M) (hG : ∀ x : R, (G x : E) = f x)
    (C : M ≃ₜ (Sphere \ ⋃ i, A i \ r i : Set V4)) (hC : C.IsFinitePL)
    (hmark : ∀ x : R, (x : X) ∈ frontier R ↔ (C (G x) : V4) ∈ ⋃ i, r i) :
    HasPuncturedSphereModel e f R := by
  classical
  letI := Fintype.ofFinite κ
  let l := Fintype.equivFin κ
  have hreindex (s : κ → Set V4) : (⋃ i : Fin (Fintype.card κ), s (l.symm i)) = ⋃ i, s i := by
    apply Subset.antisymm
    · exact iUnion_subset (fun i => subset_iUnion s (l.symm i))
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨l i, by simpa using hi⟩
  have htarget : (Sphere \ ⋃ i, A i \ r i : Set V4) =
      Sphere \ ⋃ i : Fin (Fintype.card κ), A (l.symm i) \ r (l.symm i) := by
    rw [hreindex (fun i => A i \ r i)]
  let C' := (Homeomorph.setCongr (rfl : M = M)).trans (C.trans (Homeomorph.setCongr htarget))
  refine ⟨hf, Fintype.card κ, A ∘ l.symm, r ∘ l.symm, M, G, C',
    (fun i => ⟨hA _, hAS _, hAo _⟩),
    (fun i j hij => hAdis (l.symm.injective.ne hij)), hG, hC.setCongr rfl htarget, ?_⟩
  intro x
  change (x : X) ∈ frontier R ↔ (C (G x) : V4) ∈ ⋃ i, r (l.symm i)
  rw [hreindex r]
  exact hmark x

theorem HasPuncturedSphereModel.cap_components [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    {R : Set X} {j : (Fin 2 → ℝ) → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier)
    (a : Bool → X) (ha : ∀ b, a b ∈ P.capDisk b)
    (hmodel : HasPuncturedSphereModel e f (connectedComponentIn R (a false)))
    {ν : Type*} [Finite ν] (S : ν → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier P.cutCarrier = ⋃ i, S i) :
    Disjoint (connectedComponentIn P.cutCarrier (a false))
      (connectedComponentIn P.cutCarrier (a true)) ∧
      ∀ b, HasPuncturedSphereModel e f (connectedComponentIn P.cutCarrier (a b)) := by
  obtain ⟨hf, n, A, r, M, G, C, hA, hAdis, hG, hC, hmark⟩ := hmodel
  obtain ⟨hdis, _, hmodels⟩ := P.exists_punctured_cap_component_models hR hopen hPL a ha
    A r (fun i => (hA i).1) (fun i => (hA i).2.1) hAdis (fun i => (hA i).2.2)
    f hf G hG C hC hmark S sS hSdis hfront
  refine ⟨hdis, ?_⟩
  intro b
  obtain ⟨B, hB, hBdis, u, H, hH, hu, _, hboundary⟩ := hmodels b
  exact HasPuncturedSphereModel.of_marked_model B _
    (fun i => (hB i).1) (fun i => (hB i).2.1) hBdis (fun i => (hB i).2.2)
    hf u hu H hH hboundary

theorem OriginalDiskProduct.not_hasPuncturedSphereModel_of_self_attachment [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    {R : Set X} {j : (Fin 2 → ℝ) → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier) {a b : X}
    (ha : a ∈ P.capDisk false) (hb : b ∈ P.capDisk true)
    (hsame : b ∈ connectedComponentIn P.cutCarrier a) :
    ¬ HasPuncturedSphereModel e f (connectedComponentIn R a) := by
  rintro ⟨_, n, A, r, M, G, C, hA, hAdis, _, _, _⟩
  exact P.not_homeomorph_punctured_sphere_of_cap_component_self_attachment hR hopen hPL
    ha hb hsame A r (fun i => (hA i).1) (fun i => (hA i).2.1) hAdis
    (fun i => (hA i).2.2) ⟨G.trans C⟩

theorem OriginalDiskProduct.not_hasPuncturedSphereModel_of_cap_component [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    {R : Set X} {j : (Fin 2 → ℝ) → X}
    (P : OriginalDiskProduct e R j) (hR : IsCompact R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip))
    (hPL : PLDomain e P.cutCarrier)
    (a : Bool → X) (ha : ∀ b, a b ∈ P.capDisk b)
    {ν : Type*} [Finite ν] (S : ν → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier P.cutCarrier = ⋃ i, S i)
    (b : Bool) (hno : ¬ HasPuncturedSphereModel e f (connectedComponentIn P.cutCarrier (a b))) :
    ¬ HasPuncturedSphereModel e f (connectedComponentIn R (a false)) := by
  intro hm
  exact hno ((hm.cap_components P hR hopen hPL a ha S sS hSdis hfront).2 b)

end PoincareConjecture.M76

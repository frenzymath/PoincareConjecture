import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.OriginalNormalizedResolutionFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionSourceCopiesPL
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.OriginalResolution
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedImages
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedPairs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

theorem joinSourceCopies_exists_finitePL_extension
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A B : Set E} (hAB : Disjoint A B) (jA : A → F) (jB : B → F)
    (hA : ∃ J : E → F, FinitePiecewiseAffineOn J A ∧ ∀ x : A, J x = jA x)
    (hB : ∃ J : E → F, FinitePiecewiseAffineOn J B ∧ ∀ x : B, J x = jB x) :
    ∃ J : E → F, FinitePiecewiseAffineOn J (A ∪ B) ∧
      ∀ x : (A ∪ B : Set E), J x = joinSourceCopies hAB jA jB x := by
  classical
  obtain ⟨JA, hJA, hJAval⟩ := hA
  obtain ⟨JB, hJB, hJBval⟩ := hB
  let J : E → F := fun x ↦ if x ∈ A then JA x else JB x
  have hJA' : FinitePiecewiseAffineOn J A :=
    hJA.congr (fun x hx ↦ by simp [J, hx])
  have hJB' : FinitePiecewiseAffineOn J B := hJB.congr (fun x hx ↦ by
    have hxA : x ∉ A := fun ha ↦ disjoint_left.mp hAB ha hx
    simp [J, hxA])
  refine ⟨J, finitePiecewiseAffineOn_union hJA' hJB', ?_⟩
  intro x
  rcases x.property with hx | hx
  · rw [joinSourceCopies_left hAB jA jB x hx]
    simpa [J, hx] using hJAval ⟨x, hx⟩
  · rw [joinSourceCopies_right hAB jA jB x hx]
    have hxA : (x : E) ∉ A := fun ha ↦ disjoint_left.mp hAB ha hx
    simpa [J, hxA] using hJBval ⟨x, hx⟩

def HasRetainedComponentModel (U : Set V2) : Prop :=
  IsFinitePLBallPair ℝ U (U ∩ Q2) ∨
    ∃ (n : ℕ) (P : Polygon V2 (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = U ∧ Disjoint U Q2

theorem retained_interval_image
    {S U : Set V2} {j : S → V2}
    (hPL : ∃ J : V2 → V2, FinitePiecewiseAffineOn J S ∧ ∀ x : S, J x = j x)
    (hj : Function.Injective j) (hboundary : ∀ x : S, j x ∈ Q2 ↔ (x : V2) ∈ Q2)
    (hUS : U ⊆ S) (hU : IsFinitePLBallPair ℝ U (U ∩ Q2)) :
    IsFinitePLBallPair ℝ (j '' (Subtype.val ⁻¹' U))
      ((j '' (Subtype.val ⁻¹' U)) ∩ Q2) := by
  have hbd : j '' (Subtype.val ⁻¹' (U ∩ Q2)) =
      (j '' (Subtype.val ⁻¹' U)) ∩ Q2 := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hq⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, (hboundary x).mpr hq⟩
    · rintro ⟨⟨x, hx, rfl⟩, hq⟩
      exact ⟨x, ⟨hx, (hboundary x).mp hq⟩, rfl⟩
  exact hbd ▸ source_copy_image_ballPair hPL hj hU hUS

theorem retained_polygon_image
    {S U : Set V2} {j : S → V2}
    (hPL : ∃ J : V2 → V2, FinitePiecewiseAffineOn J S ∧ ∀ x : S, J x = j x)
    (hj : Function.Injective j) (hboundary : ∀ x : S, j x ∈ Q2 ↔ (x : V2) ∈ Q2)
    (hUS : U ⊆ S) {n : ℕ} (P : Polygon V2 (n + 3))
    (hPi : Function.Injective P) (hPe : P.HasSimplicialEdges)
    (hPU : P.boundary ℝ = U) (hdisj : Disjoint U Q2) :
    ∃ (m : ℕ) (R : Polygon V2 (m + 3)), Function.Injective R ∧
      R.HasSimplicialEdges ∧ R.boundary ℝ = j '' (Subtype.val ⁻¹' U) ∧
      Disjoint (j '' (Subtype.val ⁻¹' U)) Q2 := by
  obtain ⟨J, hJ, hJval⟩ := hPL
  have hJP : InjOn J (P.boundary ℝ) := by
    rw [hPU]
    intro x hx y hy heq
    exact congrArg Subtype.val (hj ((hJval ⟨x, hUS hx⟩).symm.trans
      (heq.trans (hJval ⟨y, hUS hy⟩))))
  obtain ⟨m, R, hRi, hRe, hRb⟩ := P.exists_polygon_finitePL_image hPe hPi hJ
    (hPU ▸ hUS) hJP
  have himage : J '' U = j '' (Subtype.val ⁻¹' U) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hUS hx⟩, hx, (hJval ⟨x, hUS hx⟩).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hJval x⟩
  refine ⟨m, R, hRi, hRe, hRb.trans (by rw [hPU, himage]), ?_⟩
  apply disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ hq
  exact disjoint_left.mp hdisj hx ((hboundary x).mp hq)

theorem retained_component_model_image
    {S U : Set V2} {j : S → V2}
    (hPL : ∃ J : V2 → V2, FinitePiecewiseAffineOn J S ∧ ∀ x : S, J x = j x)
    (hj : Function.Injective j) (hboundary : ∀ x : S, j x ∈ Q2 ↔ (x : V2) ∈ Q2)
    (hUS : U ⊆ S) (hU : HasRetainedComponentModel U) :
    HasRetainedComponentModel (j '' (Subtype.val ⁻¹' U)) := by
  rcases hU with hinterval | ⟨n, P, hPi, hPe, hPU, hdisj⟩
  · exact Or.inl (retained_interval_image hPL hj hboundary hUS hinterval)
  · exact Or.inr (retained_polygon_image hPL hj hboundary hUS P hPi hPe hPU hdisj)

namespace PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D2" => closedBall (0 : V2) 1

variable {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X F}
  {f : V2 → X} {Z : Set X} {base : Z} {G : Subgroup (FundamentalGroup Z base)}
  {c : Bool → P2 → V2} {τ : C3 → X}
  {D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4)}

theorem OriginalNormalizedResolutionPairData.retained_finitePL_extensions
    (P : OriginalNormalizedResolutionPairData e D) :
    (∃ J : V2 → V2, FinitePiecewiseAffineOn J (D.A ∪ D.C) ∧
      ∀ x : (D.A ∪ D.C : Set V2), J x = P.retainedUpperCopy x) ∧
    (∃ J : V2 → V2, FinitePiecewiseAffineOn J ((D.A ∪ D.M) ∪ D.C) ∧
      ∀ x : ((D.A ∪ D.M) ∪ D.C : Set V2), J x = P.retainedAlternateCopy x) := by
  obtain ⟨jA, _, jC, hA, _, hC, hAval, _, hCval⟩ :=
    P.sourceU.exists_finitePL_source_extensions
  obtain ⟨kA, _, kM, _, kC, hkA, _, hkM, _, hkC, hkAval, _, hkMval, _, hkCval⟩ :=
    P.sourceV.exists_finitePL_source_extensions
  exact ⟨joinSourceCopies_exists_finitePL_extension D.disjointAC _ _
      ⟨jA, hA, hAval⟩ ⟨jC, hC, hCval⟩,
    joinSourceCopies_exists_finitePL_extension
      (disjoint_union_left.mpr ⟨D.disjointAC, D.disjointMC⟩) _ _
      (joinSourceCopies_exists_finitePL_extension D.disjointAM _ _
        ⟨kA, hkA, hkAval⟩ ⟨kM, hkM, hkMval⟩) ⟨kC, hkC, hkCval⟩⟩

theorem OriginalNormalizedResolutionPairData.retained_component_models
    (P : OriginalNormalizedResolutionPairData e D)
    (hτ : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2) :
    (∀ U, U ⊆ D.A ∪ D.C → HasRetainedComponentModel U →
      HasRetainedComponentModel (P.retainedUpperCopy '' (Subtype.val ⁻¹' U))) ∧
    (∀ U, U ⊆ (D.A ∪ D.M) ∪ D.C → HasRetainedComponentModel U →
      HasRetainedComponentModel (P.retainedAlternateCopy '' (Subtype.val ⁻¹' U))) := by
  obtain ⟨factsU, factsV⟩ := P.retained_fibers hτ hfull h0 h1 hfZ
  obtain ⟨hPLU, hPLV⟩ := P.retained_finitePL_extensions
  exact ⟨fun _ hUS hU ↦ retained_component_model_image hPLU factsU.injective
      factsU.boundary hUS hU,
    fun _ hUS hU ↦ retained_component_model_image hPLV factsV.injective
      factsV.boundary hUS hU⟩

omit [TopologicalSpace X] in

theorem RetainedSquareMapFacts.component_model_partition
    {I : Type*} {g : V2 → X} {K : Set V2} {j : K → V2}
    (facts : RetainedSquareMapFacts f g K j)
    (hPL : ∃ J : V2 → V2, FinitePiecewiseAffineOn J K ∧ ∀ x : K, J x = j x)
    (U : I → Set V2) (mate : I → I)
    (partner : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hcover : ⋃ i, U i = doubleLocusOn f D2)
    (hcompact : ∀ i, IsCompact (U i)) (hconn : ∀ i, IsConnected (U i))
    (hpairwise : Pairwise (fun i k ↦ Disjoint (U i) (U k)))
    (hmodel : ∀ i, HasRetainedComponentModel (U i))
    (hpartner : ∀ x : doubleLocusOn f D2, f x = f (partner x))
    (hne : ∀ x : doubleLocusOn f D2, (x : V2) ≠ partner x)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (partner x : V2))
    (hmate : ∀ (i : I) (x : doubleLocusOn f D2),
      (x : V2) ∈ U i → (partner x : V2) ∈ U (mate i))
    (hwhole : ∀ i, U i ⊆ K ∨ Disjoint (U i) K) :
    let V (i : {i // U i ⊆ K ∧ U (mate i) ⊆ K}) :=
      j '' (Subtype.val ⁻¹' U i.val)
    (⋃ i, V i) = doubleLocusOn g D2 ∧
      (∀ i, HasRetainedComponentModel (V i)) ∧
      (∀ i, IsCompact (V i) ∧ IsConnected (V i)) ∧
      Pairwise (fun i k ↦ Disjoint (V i) (V k)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [show doubleLocusOn g D2 = _ from facts.double_locus,
      retained_double_locus_eq_paired_components U mate partner rfl hcover
        hpartner hne hunique hmate facts.old_subset hwhole]
    simp only [preimage_iUnion, image_iUnion]
  · intro i
    exact retained_component_model_image hPL facts.injective facts.boundary
      i.property.1 (hmodel i.val)
  · obtain ⟨hcompact', hdisj', _, _⟩ := retained_component_image_properties
      U (fun i ↦ U i ⊆ K ∧ U (mate i) ⊆ K) j facts.injective facts.continuous
      hcompact hconn hpairwise (fun _ h ↦ h.1) facts.boundary
    exact ⟨hcompact', hdisj'⟩

theorem OriginalNormalizedResolutionPairData.retained_component_partitions
    {I : Type*} (P : OriginalNormalizedResolutionPairData e D)
    (hci : ∀ i, InjOn (c i) source) (hcS : ∀ i, MapsTo (c i) source D2)
    (hcQ : ∀ i p, p ∈ source → (c i p ∈ Q2 ↔ p.1 = 0 ∨ p.1 = 1))
    (hdisj : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (hfull : D2 ∩ f ⁻¹' (τ '' tube) = (c false '' source) ∪ (c true '' source))
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfZ : ∀ x ∈ D2, f x ∈ Z ↔ x ∈ Q2)
    (U : I → Set V2) (mate : I → I)
    (partner : doubleLocusOn f D2 → doubleLocusOn f D2)
    (hcover : ⋃ i, U i = doubleLocusOn f D2)
    (hcompact : ∀ i, IsCompact (U i)) (hconn : ∀ i, IsConnected (U i))
    (hpairwise : Pairwise (fun i k ↦ Disjoint (U i) (U k)))
    (hmodel : ∀ i, HasRetainedComponentModel (U i))
    (hpartner : ∀ x : doubleLocusOn f D2, f x = f (partner x))
    (hne : ∀ x : doubleLocusOn f D2, (x : V2) ≠ partner x)
    (hunique : ∀ (x : doubleLocusOn f D2) (y : V2), y ∈ D2 →
      f x = f y → (x : V2) ≠ y → y = (partner x : V2))
    (hmate : ∀ (i : I) (x : doubleLocusOn f D2),
      (x : V2) ∈ U i → (partner x : V2) ∈ U (mate i))
    (a b : I) (ha : U a = c false '' arm 0) (hb : U b = c true '' arm 0) :
    let VU (i : {i // U i ⊆ D.A ∪ D.C ∧ U (mate i) ⊆ D.A ∪ D.C}) :=
      P.retainedUpperCopy '' (Subtype.val ⁻¹' U i.val)
    let VV (i : {i // U i ⊆ (D.A ∪ D.M) ∪ D.C ∧
        U (mate i) ⊆ (D.A ∪ D.M) ∪ D.C}) :=
      P.retainedAlternateCopy '' (Subtype.val ⁻¹' U i.val)
    ((⋃ i, VU i) = doubleLocusOn P.gU D2 ∧
      (∀ i, HasRetainedComponentModel (VU i)) ∧
      (∀ i, IsCompact (VU i) ∧ IsConnected (VU i)) ∧
      Pairwise (fun i k ↦ Disjoint (VU i) (VU k))) ∧
    ((⋃ i, VV i) = doubleLocusOn P.gV D2 ∧
      (∀ i, HasRetainedComponentModel (VV i)) ∧
      (∀ i, IsCompact (VV i) ∧ IsConnected (VV i)) ∧
      Pairwise (fun i k ↦ Disjoint (VV i) (VV k))) := by
  obtain ⟨hwholeU, hwholeV, _, _, _⟩ := D.whole_double_components
    hci hcS hcQ hdisj hτ hfull h0 h1 U a b hcover hconn hpairwise ha hb
  obtain ⟨factsU, factsV⟩ := P.retained_fibers hτ hfull h0 h1 hfZ
  obtain ⟨hPLU, hPLV⟩ := P.retained_finitePL_extensions
  exact ⟨factsU.component_model_partition hPLU U mate partner hcover
      hcompact hconn hpairwise hmodel hpartner hne hunique hmate hwholeU,
    factsV.component_model_partition hPLV U mate partner hcover
      hcompact hconn hpairwise hmodel hpartner hne hunique hmate hwholeV⟩

end PolygonalCrossingResolution
end PoincareConjecture.M76.Dehn

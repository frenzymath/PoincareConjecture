import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.UpperResolutionSources
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.AlternateResolutionSources
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages

/-!
# Finite PL representatives of the actual normalized source copies

Compose the recorded finite PL source homeomorphisms with the inverse of
the actual normalization. The resulting ambient representatives preserve
every source-copy value and transport finite PL component ball pairs with
their complete specified boundaries. See Dehn039, section 8, and Hudson
1969, pp. 15--19.
-/

set_option autoImplicit false

open Set Metric Geometry TriangleDiskModel

namespace PoincareMT.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)

/-- Compose a finite PL source identification with an existing ambient
representative after the literal inclusion of its image carrier. -/
theorem exists_finitePL_source_copy_comp
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set E} {U V : Set F} (n : S ≃ₜ U) (hn : n.IsFinitePL) (hUV : U ⊆ V)
    {j : V → G} (hj : ∃ J : F → G, FinitePiecewiseAffineOn J V ∧ ∀ x : V, J x = j x) :
    ∃ J : E → G, FinitePiecewiseAffineOn J S ∧
      ∀ x : S, J x = j ⟨n x, hUV (n x).property⟩ := by
  obtain ⟨f, hf, hfn⟩ := hn
  obtain ⟨J, hJ, hJval⟩ := hj
  have hmaps : MapsTo f S V := by
    intro x hx
    rw [← hfn ⟨x, hx⟩]
    exact hUV (n ⟨x, hx⟩).property
  refine ⟨J ∘ f, hJ.comp hf hmaps, ?_⟩
  intro x
  change J (f x) = j _
  rw [← hfn x]
  exact hJval ⟨n x, hUV (n x).property⟩

/-- All three upper source copies have actual finite PL ambient representatives. -/
theorem UpperResolutionSources.exists_finitePL_source_extensions
    {EA EC X : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA]
    [NormedAddCommGroup EC] [NormedSpace ℝ EC]
    {SA : Set EA} {SC : Set EC} {Sstrip : Set P2}
    {pA : I01 → EA} {pC : I01 → EC} {pminus pplus : I01 → Sstrip}
    {fA : EA → X} {fS : P2 → X} {fC : EC → X} {g : V2 → X}
    (s : UpperResolutionSources SA SC Sstrip pA pC pminus pplus fA fS fC g) :
    ∃ (jA : EA → V2) (jS : P2 → V2) (jC : EC → V2),
      FinitePiecewiseAffineOn jA SA ∧ FinitePiecewiseAffineOn jS Sstrip ∧
      FinitePiecewiseAffineOn jC SC ∧
      (∀ x : SA, jA x = s.jA x) ∧ (∀ x : Sstrip, jS x = s.jS x) ∧
      (∀ x : SC, jC x = s.jC x) := by
  obtain ⟨H, hH, hHval⟩ := s.pl_H.symm
  have hbase : ∃ J : P2 → V2, FinitePiecewiseAffineOn J T ∧
      ∀ x : T, J x = (s.H.symm x : V2) := ⟨H, hH, fun x ↦ (hHval x).symm⟩
  have hm := exists_finitePL_source_copy_comp s.m s.pl_m subset_union_left hbase
  obtain ⟨jA, hjA, hjAval⟩ :=
    exists_finitePL_source_copy_comp s.nA s.pl_nA subset_union_left hm
  obtain ⟨jS, hjS, hjSval⟩ :=
    exists_finitePL_source_copy_comp s.nS s.pl_nS subset_union_right hm
  obtain ⟨jC, hjC, hjCval⟩ :=
    exists_finitePL_source_copy_comp s.nC s.pl_nC subset_union_right hbase
  exact ⟨jA, jS, jC, hjA, hjS, hjC, hjAval, hjSval, hjCval⟩

/-- All five alternate source copies have actual finite PL ambient representatives. -/
theorem AlternateResolutionSources.exists_finitePL_source_extensions
    {EA EM EC X : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [NormedAddCommGroup EC] [NormedSpace ℝ EC]
    {SA : Set EA} {SM : Set EM} {SC : Set EC} {Sstrip : Set P2}
    {pA : I01 → EA} {pL pR : I01 → EM} {pC : I01 → EC}
    {pminus pplus : I01 → Sstrip}
    {fA : EA → X} {fL : P2 → X} {fM : EM → X} {fR : P2 → X} {fC : EC → X}
    {g : V2 → X}
    (s : AlternateResolutionSources SA SM SC Sstrip pA pL pR pC pminus pplus
      fA fL fM fR fC g) :
    ∃ (jA : EA → V2) (jL : P2 → V2) (jM : EM → V2) (jR : P2 → V2) (jC : EC → V2),
      FinitePiecewiseAffineOn jA SA ∧ FinitePiecewiseAffineOn jL Sstrip ∧
      FinitePiecewiseAffineOn jM SM ∧ FinitePiecewiseAffineOn jR Sstrip ∧
      FinitePiecewiseAffineOn jC SC ∧
      (∀ x : SA, jA x = s.jA x) ∧ (∀ x : Sstrip, jL x = s.jL x) ∧
      (∀ x : SM, jM x = s.jM x) ∧ (∀ x : Sstrip, jR x = s.jR x) ∧
      (∀ x : SC, jC x = s.jC x) := by
  obtain ⟨H, hH, hHval⟩ := s.pl_H.symm
  have hbase : ∃ J : P2 → V2, FinitePiecewiseAffineOn J T ∧
      ∀ x : T, J x = (s.H.symm x : V2) := ⟨H, hH, fun x ↦ (hHval x).symm⟩
  have hmR := exists_finitePL_source_copy_comp s.mR s.pl_mR subset_union_left hbase
  have hAML := exists_finitePL_source_copy_comp s.nAML s.pl_nAML subset_union_left hmR
  have hmL := exists_finitePL_source_copy_comp s.mL s.pl_mL subset_union_left hAML
  obtain ⟨jA, hjA, hjAval⟩ :=
    exists_finitePL_source_copy_comp s.nA s.pl_nA subset_union_left hmL
  obtain ⟨jL, hjL, hjLval⟩ :=
    exists_finitePL_source_copy_comp s.nL s.pl_nL subset_union_right hmL
  obtain ⟨jM, hjM, hjMval⟩ :=
    exists_finitePL_source_copy_comp s.nM s.pl_nM subset_union_right hAML
  obtain ⟨jR, hjR, hjRval⟩ :=
    exists_finitePL_source_copy_comp s.nR s.pl_nR subset_union_right hmR
  obtain ⟨jC, hjC, hjCval⟩ :=
    exists_finitePL_source_copy_comp s.nC s.pl_nC subset_union_right hbase
  exact ⟨jA, jL, jM, jR, jC, hjA, hjL, hjM, hjR, hjC,
    hjAval, hjLval, hjMval, hjRval, hjCval⟩

/-- The ambient representative transports every old component ball pair
in its retained piece, with exactly the image of its specified boundary. -/
theorem source_copy_image_ballPair
    {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {S U B : Set E} {j : S → F}
    (hPL : ∃ J : E → F, FinitePiecewiseAffineOn J S ∧ ∀ x : S, J x = j x)
    (hj : Function.Injective j) (hU : IsFinitePLBallPair W U B) (hUS : U ⊆ S) :
    IsFinitePLBallPair W (j '' (Subtype.val ⁻¹' U)) (j '' (Subtype.val ⁻¹' B)) := by
  obtain ⟨J, hJ, hJval⟩ := hPL
  have hinj : InjOn J S := by
    intro x hx y hy heq
    apply congrArg Subtype.val (hj (show j ⟨x, hx⟩ = j ⟨y, hy⟩ from
      (hJval ⟨x, hx⟩).symm.trans (heq.trans (hJval ⟨y, hy⟩))))
  have himage {K : Set E} (hKS : K ⊆ S) : J '' K = j '' (Subtype.val ⁻¹' K) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hKS hx⟩, hx, (hJval ⟨x, hKS hx⟩).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hJval x⟩
  rw [← himage hUS, ← himage (hU.1.trans hUS)]
  exact hU.image_of_subset hJ hUS hinj

/-- Every finite PL interval component in either retained upper exterior
keeps its complete component boundary under the actual normalized copy. -/
theorem UpperResolutionSources.retained_ballPair_images
    {EA EC X : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [FiniteDimensional ℝ EA]
    [NormedAddCommGroup EC] [NormedSpace ℝ EC] [FiniteDimensional ℝ EC]
    {SA : Set EA} {SC : Set EC} {Sstrip : Set P2}
    {pA : I01 → EA} {pC : I01 → EC} {pminus pplus : I01 → Sstrip}
    {fA : EA → X} {fS : P2 → X} {fC : EC → X} {g : V2 → X}
    (s : UpperResolutionSources SA SC Sstrip pA pC pminus pplus fA fS fC g) :
    (∀ {U B : Set EA}, IsFinitePLBallPair ℝ U B → U ⊆ SA →
      IsFinitePLBallPair ℝ (s.jA '' (Subtype.val ⁻¹' U))
        (s.jA '' (Subtype.val ⁻¹' B))) ∧
    (∀ {U B : Set EC}, IsFinitePLBallPair ℝ U B → U ⊆ SC →
      IsFinitePLBallPair ℝ (s.jC '' (Subtype.val ⁻¹' U))
        (s.jC '' (Subtype.val ⁻¹' B))) := by
  obtain ⟨jA, _, jC, hjA, _, hjC, hAval, _, hCval⟩ := s.exists_finitePL_source_extensions
  exact ⟨fun hU hUS ↦ source_copy_image_ballPair ⟨jA, hjA, hAval⟩
    s.embeddings.1.injective hU hUS,
    fun hU hUS ↦ source_copy_image_ballPair ⟨jC, hjC, hCval⟩
      s.embeddings.2.2.injective hU hUS⟩

/-- Every finite PL interval component in any of the three retained
alternate exteriors keeps its complete boundary in the actual source copy. -/
theorem AlternateResolutionSources.retained_ballPair_images
    {EA EM EC X : Type*}
    [NormedAddCommGroup EA] [NormedSpace ℝ EA] [FiniteDimensional ℝ EA]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    [NormedAddCommGroup EC] [NormedSpace ℝ EC] [FiniteDimensional ℝ EC]
    {SA : Set EA} {SM : Set EM} {SC : Set EC} {Sstrip : Set P2}
    {pA : I01 → EA} {pL pR : I01 → EM} {pC : I01 → EC}
    {pminus pplus : I01 → Sstrip}
    {fA : EA → X} {fL : P2 → X} {fM : EM → X} {fR : P2 → X} {fC : EC → X}
    {g : V2 → X}
    (s : AlternateResolutionSources SA SM SC Sstrip pA pL pR pC pminus pplus
      fA fL fM fR fC g) :
    (∀ {U B : Set EA}, IsFinitePLBallPair ℝ U B → U ⊆ SA →
      IsFinitePLBallPair ℝ (s.jA '' (Subtype.val ⁻¹' U))
        (s.jA '' (Subtype.val ⁻¹' B))) ∧
    (∀ {U B : Set EM}, IsFinitePLBallPair ℝ U B → U ⊆ SM →
      IsFinitePLBallPair ℝ (s.jM '' (Subtype.val ⁻¹' U))
        (s.jM '' (Subtype.val ⁻¹' B))) ∧
    (∀ {U B : Set EC}, IsFinitePLBallPair ℝ U B → U ⊆ SC →
      IsFinitePLBallPair ℝ (s.jC '' (Subtype.val ⁻¹' U))
        (s.jC '' (Subtype.val ⁻¹' B))) := by
  obtain ⟨jA, _, jM, _, jC, hjA, _, hjM, _, hjC, hAval, _, hMval, _, hCval⟩ :=
    s.exists_finitePL_source_extensions
  exact ⟨fun hU hUS ↦ source_copy_image_ballPair ⟨jA, hjA, hAval⟩
    s.embeddings.1.injective hU hUS,
    fun hU hUS ↦ source_copy_image_ballPair ⟨jM, hjM, hMval⟩
      s.embeddings.2.2.1.injective hU hUS,
    fun hU hUS ↦ source_copy_image_ballPair ⟨jC, hjC, hCval⟩
      s.embeddings.2.2.2.2.injective hU hUS⟩

end PoincareMT.M76.Dehn

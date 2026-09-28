import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MaximalExteriorCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.IrreducibleCappedExterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.SameSpaceExterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RetainedAtlasDomains
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.AtlasRange
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RetainedProtectedBall











set_option autoImplicit false
open Set Geometry Geometry.SeparatedSphereCaps
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.exists_original_irreducible_exterior_atlas
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)} (bD : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ∃ (charts : Set (OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3))
      (N : Set (LatticeHandleAmbient ι κ L)),
      let a := (Subtype.val : charts → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
      let R := latticeHandleDomain ι κ L
      IsOpen N ∧ D ∪ frontier R ⊆ N ∧
      IsPLIrreducible a (closure (R \ D)) ∧ PLDomain a R ∧
      Nonempty (HamiltonMarkedProtectedBall ι κ L a D) ∧
      ChartwisePLOn e a (ContinuousMap.id R) ((Subtype.val : R → LatticeHandleAmbient ι κ L) ⁻¹' N) ∧
      ChartwisePLOn a e (ContinuousMap.id R) ((Subtype.val : R → LatticeHandleAmbient ι κ L) ⁻¹' N) ∧
      ChartwisePLOn e a (ContinuousMap.id (univ : Set (LatticeHandleAmbient ι κ L)))
        ((Subtype.val : ↥(univ : Set (LatticeHandleAmbient ι κ L)) → LatticeHandleAmbient ι κ L) ⁻¹' N) ∧
      ChartwisePLOn a e (ContinuousMap.id (univ : Set (LatticeHandleAmbient ι κ L)))
        ((Subtype.val : ↥(univ : Set (LatticeHandleAmbient ι κ L)) → LatticeHandleAmbient ι κ L) ⁻¹' N) := by
  classical
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  obtain ⟨t₀,f,K,H,g,hf,hfi,hK,hH,hg,hgPL,ν,hν,c,hno,hmax,_⟩ :=
    bD.exists_maximal_exterior_sphere_cut L hdim hi he
  let := hν
  have hgi : InjOn (fun z => (g z : LatticeHandleAmbient ι κ L)) K.space := by
    intro x hx y hy hxy
    have heq : H.symm ⟨x,hx⟩ = H.symm ⟨y,hy⟩ :=
      Subtype.ext ((hg ⟨x,hx⟩).symm.trans (hxy.trans (hg ⟨y,hy⟩)))
    exact congrArg Subtype.val (H.symm.injective heq)
  have hreal : ∀ x ∈ E, f x ∈ K.space ∧ (g (f x) : LatticeHandleAmbient ι κ L) = x := by
    intro x hx
    have hh := hH ⟨x,hx⟩
    refine ⟨hh ▸ (H ⟨x,hx⟩).property,?_⟩
    rw [←hh,hg]
    exact congrArg Subtype.val (H.symm_apply_apply ⟨x,hx⟩)
  obtain ⟨cut,_,_,_,_,P,hP,hEP,heP,τ,hτ,F,W,heB,hBfront,_,hFouter,hW,
    hcontactOuter,_,_,_,hDW,hFc,hF,_,hcap,hcontact,hdis,
    atlas,_,ha,hrep,hI,hDc,_,_,_⟩ :=
    bD.exists_irreducible_capped_exterior_from_cut L hdim hi he c K
      (fun z => (g z : LatticeHandleAmbient ι κ L)) hgPL hgi hreal hno hmax
      isOpen_univ (fun _ => subset_univ _)
  let := hτ
  let phi : LatticeHandleAmbient ι κ L → ((τ → ℝ × V3) × ((ν × Bool) → ℝ)) := lift ∘ F
  have hphiPL i : LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target :=
    (hF i).prod_mk (locallyPiecewiseAffineOn_affine
      (ContinuousAffineMap.const ℝ V3 (0 : (ν × Bool) → ℝ)) (e i).open_target)
  have hphiInj : InjOn phi (P \ ⋃ i,cut.collar i) := by
    intro x hx y hy hxy
    exact hFouter hx hy (congrArg Prod.fst hxy)
  have hrep' (p : W) : ∃ (B : Set ((τ → ℝ × V3) × ((ν × Bool) → ℝ)))
      (a : ((τ → ℝ × V3) × ((ν × Bool) → ℝ)) → V3),
      FinitePiecewiseAffineOn a B ∧
      ∀ x ∈ (atlas p).source, (x : (τ → ℝ × V3) × ((ν × Bool) → ℝ)) ∈ B ∧ atlas p x = a x := by
    obtain ⟨B,a,a',ha,ha',hvalues,_,_⟩ := hrep p
    exact ⟨B,a,ha,hvalues⟩
  obtain ⟨Q,t,hQ,htdis,hO,hfront,hne,a,hret,hIa,_,_⟩ :=
    bD.exists_same_space_irreducible_exterior_from_caps L cut he hdim hi hP heP hEP heB hBfront phi
      (hFc.prodMk continuous_const) hphiPL hphiInj (fun i => cap i (F '' cut.ports i))
      (by simpa only [phi,image_comp] using hcap) hdis
      (by simpa only [phi,image_comp,inter_comm] using hcontactOuter)
      (by simpa only [phi,image_comp] using hW)
      (by simpa only [phi,image_comp] using hDW) atlas ha hrep'
      (by simpa only [phi,image_comp] using hI)
      (by simpa only [phi,image_comp] using hDc)
  have hint := (bD.closed_complement_geometry he hdim hi).2.2.2.2.1
  have hprotected : D ∪ frontier R ⊆ (⋃ i : t,Q i)ᶜ := by
    intro x hx hbad
    obtain ⟨i,hiQ⟩ := mem_iUnion.mp hbad
    have hxE := (hQ i).2.2.2 hiQ
    rw [hint] at hxE
    rcases hx with hx | hx
    · exact hxE.2 hx
    · exact hx.2 hxE.1
  obtain ⟨haR,hforward,hreverse,hambient,hambient'⟩ :=
    PLDomain.transfer_of_retained_charts e a he hIa.1 hO
      (fun _ hx => hprotected (Or.inr hx)) Sum.inl hret
  have hbnew : Nonempty (HamiltonMarkedProtectedBall ι κ L
      (Subtype.val : range a → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3) D) := by
    exact ⟨bD.of_retained_charts hO (fun _ hx => hprotected (Or.inl hx))
      (fun i => ⟨a (Sum.inl i),mem_range_self _⟩) hret⟩
  exact ⟨range a,(⋃ i : t,Q i)ᶜ,hO,hprotected,hIa.range,haR.range,hbnew,
    hforward.range_target,hreverse.range_source,hambient.range_target,hambient'.range_source⟩

end PoincareConjecture.M76

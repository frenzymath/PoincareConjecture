import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.PrescribedIrreducibleCappedDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.SameSpaceIrreducibleAtlas
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.AtlasRange

set_option autoImplicit false
open Set Geometry Geometry.SeparatedSphereCaps
namespace PoincareConjecture.M76
universe u v
local notation "V3" => (Fin 3 → ℝ)

theorem exists_boundary_relative_irreducible_lattice_atlas
    {ι : Type u} {κ : Type v} {α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hindex : Fintype.card ι ≤ 2)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    {D : Set (LatticeHandleAmbient ι κ L)} (bD : HamiltonMarkedProtectedBall ι κ L e D) :
    ∃ (charts : Set (OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3))
      (N : Set (LatticeHandleAmbient ι κ L)),
      let a := (Subtype.val : charts → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
      let R := latticeHandleDomain ι κ L
      IsOpen N ∧ frontier R ⊆ N ∧ (N ∩ interior R).Nonempty ∧
      IsPLIrreducible a R ∧
      ChartwisePLOn e a (ContinuousMap.id R) ((Subtype.val : R → LatticeHandleAmbient ι κ L) ⁻¹' N) ∧
      ChartwisePLOn a e (ContinuousMap.id R) ((Subtype.val : R → LatticeHandleAmbient ι κ L) ⁻¹' N) := by
  classical
  obtain ⟨t₀,f,K,H,g,hf,hfi,hK,hH,hg,hgPL,ν,hν,c,hno,hmax,_⟩ :=
    exists_maximal_lattice_handle_sphere_cut L hdim hindex he bD
  let := hν
  have hgi : InjOn (fun z => (g z : LatticeHandleAmbient ι κ L)) K.space := by
    intro x hx y hy hxy
    have heq : H.symm ⟨x,hx⟩ = H.symm ⟨y,hy⟩ :=
      Subtype.ext ((hg ⟨x,hx⟩).symm.trans (hxy.trans (hg ⟨y,hy⟩)))
    exact congrArg Subtype.val (H.symm.injective heq)
  have hreal : ∀ x ∈ latticeHandleDomain ι κ L,
      f x ∈ K.space ∧ (g (f x) : LatticeHandleAmbient ι κ L) = x := by
    intro x hx
    have hh := hH ⟨x,hx⟩
    refine ⟨hh ▸ (H ⟨x,hx⟩).property,?_⟩
    rw [←hh,hg]
    exact congrArg Subtype.val (H.symm_apply_apply ⟨x,hx⟩)
  obtain ⟨cut,_,_,_,_,P,hP,hRP,heP,τ,hτ,F,W,heB,hBfront,_,hFouter,hW,
    hcontactOuter,_,_,_,hDW,hFc,hF,_,hcap,hcontact,hdis,
    atlas,_,ha,hrep,hI,hDc,_,_,_⟩ :=
    exists_irreducible_capped_lattice_handle_from_cut L hdim hindex he c K
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
  obtain ⟨Q,t,hQ,htdis,hO,hfront,hne,a,hIa,hforward,hreverse⟩ :=
    cut.exists_same_space_irreducible_atlas L he hdim bD hP heP hRP heB hBfront phi
      (hFc.prodMk continuous_const) hphiPL hphiInj (fun i => cap i (F '' cut.ports i))
      (by simpa only [phi,image_comp] using hcap) hdis
      (by simpa only [phi,image_comp,inter_comm] using hcontactOuter)
      (by simpa only [phi,image_comp] using hW)
      (by simpa only [phi,image_comp] using hDW) atlas ha hrep'
      (by simpa only [phi,image_comp] using hI)
      (by simpa only [phi,image_comp] using hDc)
  exact ⟨range a,(⋃ i : t,Q i)ᶜ,hO,hfront,hne,hIa.range,hforward.range_target,hreverse.range_source⟩

end PoincareConjecture.M76

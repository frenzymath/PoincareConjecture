import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.PrescribedIrreducibleCappedDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.SameSpaceIrreducibleAtlas
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.AtlasRange
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.ProtectedResidualExterior









set_option autoImplicit false
open Set Geometry Geometry.SeparatedSphereCaps
namespace PoincareConjecture.M76
universe u v
local notation "V3" => (Fin 3 → ℝ)

theorem exists_protected_irreducible_lattice_atlas_from_cut
    {ι : Type u} {κ : Type v} {α E : Type*} {ν : Type (max u v)}
    [Fintype ι] [Fintype κ] [Fintype ν] [DecidableEq ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hindex : Fintype.card ι ≤ 2)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    {D : Set (LatticeHandleAmbient ι κ L)} (bD : HamiltonMarkedProtectedBall ι κ L e D)
    (hpos : 0 < Fintype.card ι)
    (c : MarkedSphereCut e (latticeHandleDomain ι κ L) ν)
    {f : LatticeHandleAmbient ι κ L → E} (K : SimplicialComplex ℝ E)
    (g : E → LatticeHandleAmbient ι κ L)
    (hgPL : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ latticeHandleDomain ι κ L, f x ∈ K.space ∧ g (f x) = x)
    (hno : HasNoPuncturedSphereComponents e f c.carrier)
    (hmax : ∀ (μ : Type (max u v)) [Fintype μ]
      (d : MarkedSphereCut e (latticeHandleDomain ι κ L) μ),
      HasNoPuncturedSphereComponents e f d.carrier → Fintype.card μ ≤ Fintype.card ν)
    (havoid : ∀ i, Disjoint (c.spheres i) D) :
    ∃ (charts : Set (OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3))
      (N : Set (LatticeHandleAmbient ι κ L)),
      let a := (Subtype.val : charts → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3)
      let R := latticeHandleDomain ι κ L
      IsOpen N ∧ D ∪ frontier R ⊆ N ∧
      IsPLIrreducible a R ∧
      ChartwisePLOn e a (ContinuousMap.id R) ((Subtype.val : R → LatticeHandleAmbient ι κ L) ⁻¹' N) ∧
      ChartwisePLOn a e (ContinuousMap.id R) ((Subtype.val : R → LatticeHandleAmbient ι κ L) ⁻¹' N) := by
  classical
  obtain ⟨cut,hcutS,_,hsupport,_,P,hP,hRP,heP,τ,hτ,F,W,heB,hBfront,_,hFouter,hW,
    hcontactOuter,_,_,_,hDW,hFc,hF,_,hcap,hcontact,hdis,
    atlas,_,ha,hrep,hI,hDc,_,_,_⟩ :=
    exists_irreducible_capped_lattice_handle_from_cut L hdim hindex he c K
      g hgPL hgi hreal hno hmax
      bD.ball.isCompact.isClosed.isOpen_compl
      (fun i x hx hd => disjoint_left.mp (havoid i) hx hd)
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
  have hprotected := bD.subset_residual_exterior hpos (fun i : t => Q i)
    (fun i => (hQ i).1.isClosed) (fun i => (hQ i).2.2.2)
    (fun i => by
      rw [(hQ i).2.1]
      apply disjoint_left.mpr
      intro x hxD hxPort
      have hxCl := cut.portClosure i hxPort
      have hxAll : x ∈ closure (⋃ j,cut.collar j) :=
        closure_mono (subset_iUnion _ i.val.1) hxCl
      exact hsupport hxAll hxD)
  exact ⟨range a,(⋃ i : t,Q i)ᶜ,hprotected.1,hprotected.2,
    hIa.range,hforward.range_target,hreverse.range_source⟩

end PoincareConjecture.M76

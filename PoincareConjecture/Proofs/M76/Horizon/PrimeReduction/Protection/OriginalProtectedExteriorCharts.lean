import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SphereCutPLDomain
import PoincareConjecture.Proofs.M76.PrimeReduction.PLDomainExterior
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.OriginalBallBoundarySphere








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.closed_complement_halfspace_off_rims
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    {x : LatticeHandleAmbient ι κ L}
    (hx : x ∈ frontier (closure (latticeHandleDomain ι κ L \ D)))
    (hxrim : x ∉ hamiltonMarkedProjection ι κ L ''
      (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3/2))) :
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3)
      (B : OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3),
      ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ y ∈ B.source, y ∈ closure (latticeHandleDomain ι κ L \ D) ↔
        0 ≤ ell (B y) := by
  classical
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  obtain ⟨hEc,hER,_,hED,hiE,hreg,hfront⟩ := b.closed_complement_geometry he hdim hi
  have hxE : x ∈ E := hEc.isClosed.frontier_subset hx
  have hDc := b.ball.isCompact.isClosed
  have hmark : D ∩ frontier R = hamiltonAttachingBlock ι κ L (3/2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hlocal (y) (hy : y ∈ interior R) : y ∈ E ↔ y ∉ interior D := by
    constructor
    · intro hyE
      have hsub : R \ D ⊆ (interior D)ᶜ :=
        fun _ hz hzD => hz.2 (interior_subset hzD)
      exact (closure_minimal hsub isOpen_interior.isClosed_compl) hyE
    · intro hyD
      have hcl : y ∈ closure Dᶜ := by rwa [closure_compl]
      have hsub : interior R ∩ Dᶜ ⊆ R \ D :=
        fun _ hz => ⟨interior_subset hz.1,hz.2⟩
      exact closure_mono hsub (isOpen_interior.inter_closure ⟨hy,hcl⟩)
  by_cases hxint : x ∈ interior R
  · have hxFD : x ∈ frontier D := by
      rcases hfront.subset hx with h | h
      · exact h.1
      · exact (h.2.2 hxint).elim
    obtain ⟨s⟩ := b.ball.nonempty_boundarySphere
    have hDdom : PLDomain e D := ⟨he.cover,he.compatible,hDc,by
      intro y hy
      exact s.exists_regular_boundary_halfspace_chart (A := ∅) hDc
        b.ball.closure_interior isClosed_empty he.compatible he.cover
        (by simp) hy (notMem_empty y)⟩
    obtain ⟨ell,v,B,hv,hxB,hzero,hBe,hhalf⟩ := hDdom.closed_exterior.halfspace x
      (hDdom.frontier_closed_exterior.symm ▸ hxFD)
    refine ⟨ell,v,B.restrOpen (interior R) isOpen_interior,hv,⟨hxB,hxint⟩,hzero,?_,?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right B (hBe i) isOpen_interior
    · intro y hy
      exact (hlocal y hy.2).trans (hhalf y hy.1)
  · have hxFR : x ∈ frontier R := ⟨he.closed.closure_eq ▸ hER hxE,hxint⟩
    have hxnotD : x ∉ D := by
      intro hxD
      have ht := hED.subset ⟨hxE,hxD⟩
      exact ht.2 ⟨hmark.subset ⟨hxD,hxFR⟩,hxrim⟩
    obtain ⟨ell,v,B,hv,hxB,hzero,hBe,hhalf⟩ := he.halfspace x hxFR
    refine ⟨ell,v,B.restrOpen Dᶜ hDc.isOpen_compl,hv,⟨hxB,hxnotD⟩,hzero,?_,?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right B (hBe i) hDc.isOpen_compl
    · intro y hy
      apply Iff.trans _ (hhalf y hy.1)
      exact ⟨fun h => hER h,fun h => subset_closure ⟨h,hy.2⟩⟩

end PoincareConjecture.M76

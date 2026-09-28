import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalLateralAnnulus
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.RelativeClosedExterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExteriorCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryCharts.AtlasAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.Mathlib.CompatibleSignedPairHalfspace
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeConvexChartSides
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeRegionClosure
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem HamiltonMarkedProtectedBall.plDomain_closed_complement
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    PLDomain e (closure (latticeHandleDomain ι κ L \ D)) := by
  classical
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  obtain ⟨hEc,hER,_,hED,hiE,hreg,hfront⟩ := b.closed_complement_geometry he hdim hi
  obtain ⟨p,hp,hpi,himage,hproper⟩ := b.exists_original_exterior_contact_annulus he hdim hi
  obtain ⟨K,hK,hKs⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8)
  have hpK : PolyhedralPLInCharts e p K.space := hKs.symm ▸ hp
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  have hemb : Topology.IsEmbedding (fun z : K.space => p z) := by
    apply (hpK.continuousOn.domRestrict.isClosedEmbedding ?_).isEmbedding
    intro z w h
    exact Subtype.ext (hpi (hKs.subset z.property) (hKs.subset w.property) h)
  have hpR : MapsTo p K.space R := by
    intro z hz
    exact hER (himage.subset ⟨z,hKs.subset hz,rfl⟩).1
  have hrel : frontier ((Subtype.val : R → _) ⁻¹' E) =
      (Subtype.val : R → _) ⁻¹' (E ∩ D) :=
    frontier_relative_closed_exterior b.ball.isCompact.isClosed b.subset_domain
      b.ball.closure_interior
  have hregRel := regular_closed_subtype_preimage hEc.isClosed hER hreg
  refine ⟨he.cover,he.compatible,hEc.isClosed,?_⟩
  intro x hx
  by_cases hxr : x ∈ hamiltonMarkedProjection ι κ L ''
      (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3/2))
  · have hmark : D ∩ frontier R = hamiltonAttachingBlock ι κ L (3/2) := by
      rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
      · omega
      · exact hm
    have hxmark : x ∈ D ∩ frontier R := hmark.symm.subset
      (image_mono (prod_mono subset_rfl sphere_subset_closedBall) hxr)
    have hxE : x ∈ E := hEc.isClosed.frontier_subset hx
    obtain ⟨z,hz,hzx⟩ := himage.symm.subset ⟨hxE,hxmark.1⟩
    let zK : K.space := ⟨z,hKs.symm.subset hz⟩
    obtain ⟨C,hzC,hCt,hCz,hCR,hCS,hCe⟩ :=
      Dehn.exists_original_planar_annulus_boundary_pair_chart he K hK hKs hpK hemb hpR
        (fun z hz => hproper z (hKs.subset hz)) zK (hzx.symm ▸ hxmark.2)
    have hxC : x ∈ C.source := hzx ▸ hzC
    have hCx : C x = 0 := hzx ▸ hCz
    have hxRel : (⟨x,hER hxE⟩ : R) ∈ frontier ((Subtype.val : R → _) ⁻¹' E) := by
      rw [hrel]
      exact ⟨hxE,hxmark.1⟩
    let M : Set C3 := {y | 0 ≤ y.1.1}
    let a : C3 →ₗ[ℝ] ℝ :=
      (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ P2 ℝ)
    have hcv : Convex ℝ (C.target ∩ M) := by
      apply Convex.inter _ ((convex_Ici (0 : ℝ)).linear_preimage a)
      rw [hCt,CoordinateHalfBoxes.box_eq_closedBall]
      exact (convex_closedBall (0 : C3) 1).interior
    have hCfront : ∀ y : R, (y : LatticeHandleAmbient ι κ L) ∈ C.source →
        (y ∈ frontier ((Subtype.val : R → _) ⁻¹' E) ↔ (C y).2 = 0) := by
      intro y hy
      rw [hrel]
      change (y : LatticeHandleAmbient ι κ L) ∈ E ∩ D ↔ _
      rw [←himage,←hKs]
      exact (hCS y hy).trans (and_iff_right ((hCR y hy).mp y.property))
    have hsign := relative_halfspace_of_convex_frontier_chart hER
      (hEc.isClosed.preimage continuous_subtype_val) hregRel hxRel C hxC
      (show C.IsImage R M from fun _ hy => (hCR _ hy).symm) hcv hCfront
    rcases hsign with hsign | hsign
    · apply exists_compatible_halfspace_of_signed_pair e C hxC hCx (fun i => (hCe i).1)
        1 (Or.inl rfl) (Or.inr ?_)
      intro y hy
      simpa only [one_mul] using (hsign y hy).trans ((hCR y hy).and Iff.rfl)
    · apply exists_compatible_halfspace_of_signed_pair e C hxC hCx (fun i => (hCe i).1)
        (-1) (Or.inr rfl) (Or.inr ?_)
      intro y hy
      simpa only [neg_one_mul,neg_nonneg] using (hsign y hy).trans ((hCR y hy).and Iff.rfl)
  · exact b.closed_complement_halfspace_off_rims he hdim hi hx hxr

end PoincareConjecture.M76

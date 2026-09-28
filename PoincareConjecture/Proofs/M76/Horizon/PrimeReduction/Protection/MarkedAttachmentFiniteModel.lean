import PoincareConjecture.Proofs.M76.PrimeReduction.FiniteDomainTriangulation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentEmbedding
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.SharedBoundaryConeUnion
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedApproximation

set_option autoImplicit false
open Set Geometry Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLBall.frontier_inter_eq_of_subset
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {D R : Set X}
    (b : ChartwisePLBall e D (frontier D)) (hDR : D ⊆ R) :
    frontier D ∩ frontier R = D ∩ frontier R := by
  apply Subset.antisymm
  · exact inter_subset_inter_left _ b.boundary_subset
  · rintro x ⟨hxD, hxR⟩
    refine ⟨?_, hxR⟩
    change x ∈ closure D ∧ x ∉ interior D
    refine ⟨subset_closure hxD, ?_⟩
    exact fun hx => hxR.2 (interior_mono hDR hx)

theorem HamiltonMarkedProtectedBall.exists_finite_marked_attaching_model
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L)) (hpos : 0 < Fintype.card ι) :
    ∃ (s : Finset (latticeHandleDomain ι κ L))
      (F : LatticeHandleAmbient ι κ L → (s → ℝ × V3))
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 3 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : latticeHandleDomain ι κ L ≃ₜ K.space)
      (J : SimplicialComplex ℝ (s → ℝ × V3))
      (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ J.space),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧
      (∀ i, A i ≤ K ∧ (A i).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A i).vertices) → t ∈ (A i).faces) ∧
      K.space = F '' latticeHandleDomain ι κ L ∧
      (A 0).space = F '' frontier (latticeHandleDomain ι κ L) ∧
      (A 1).space = F '' D ∧ (A 2).space = F '' frontier D ∧
      (∀ x, (H x : s → ℝ × V3) = F x) ∧
      (∀ x ∈ latticeHandleDomain ι κ L,
        ∃ (i : α) (V : Set (LatticeHandleAmbient ι κ L))
          (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
          IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V) ∧
      J = A 0 ⊓ A 2 ∧ J ≤ A 0 ∧ J ≤ A 2 ∧ J.faces.Finite ∧
      (∀ t ∈ K.faces, (∀ v ∈ t, v ∈ J.vertices) → t ∈ J.faces) ∧
      J.space = F '' (D ∩ frontier (latticeHandleDomain ι κ L)) ∧
      J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2) ∧
      (∀ x, (P x : s → ℝ × V3) = F (hamiltonMarkedProjection ι κ L x)) ∧
      ∀ x, (P x : s → ℝ × V3) ∈
          F '' (hamiltonMarkedProjection ι κ L ''
            (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))) ↔
        (x : (ι → ℝ) × (κ → ℝ)).2 ∈ sphere (0 : κ → ℝ) (3 / 2) := by
  classical
  let R := latticeHandleDomain ι κ L
  obtain ⟨s, F, K, A, H, hFc, hF, hK, hA, hKs, hA0, hA1, hA2, hH, _, hproj⟩ :=
    exists_protected_finite_domain_triangulation
      (isCompact_latticeHandleDomain ι κ L) he b.subset_domain b.ball
  have hinj : InjOn F R := by
    intro x hx y hy hxy
    have hh : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
      ((hH ⟨x, hx⟩).trans (hxy.trans (hH ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective hh)
  have hmark : D ∩ frontier R = hamiltonAttachingBlock ι κ L (3 / 2) := by
    rcases b.position with ⟨hzero, _⟩ | ⟨_, _, _, _, _, hmark⟩
    · omega
    · exact hmark
  let J := A 0 ⊓ A 2
  have hJs : J.space = F '' (D ∩ frontier R) := by
    rw [K.space_inf_eq_inter_of_le (A 0) (A 2) (hA 0).1 (hA 2).1, hA0, hA2]
    apply Subset.antisymm
    · rintro z ⟨⟨x, hx, rfl⟩, y, hy, hyx⟩
      have hyR := b.subset_domain (b.ball.boundary_subset hy)
      have hyx' : y = x := hinj hyR (he.closed.frontier_subset hx) hyx
      exact ⟨x, ⟨b.ball.boundary_subset (hyx' ▸ hy), hx⟩, rfl⟩
    · rintro z ⟨x, hx, rfl⟩
      have hxd := (b.ball.frontier_inter_eq_of_subset b.subset_domain).symm.subset hx
      exact ⟨⟨x, hx.2, rfl⟩, x, hxd.1, rfl⟩
  have hJmark : J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2) := by
    rw [hJs, hmark]
  obtain ⟨P0, hP0, hP0rim⟩ := b.exists_marked_attaching_homeomorph hpos
  let f : hamiltonAttachingBlock ι κ L (3 / 2) → J.space :=
    fun x => ⟨F x, hJmark.symm.subset ⟨x, x.property, rfl⟩⟩
  have : CompactSpace
      (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) :=
    isCompact_iff_compactSpace.mp
      ((isCompact_sphere _ _).prod (isCompact_closedBall _ _))
  have : CompactSpace (hamiltonAttachingBlock ι κ L (3 / 2)) :=
    P0.compactSpace
  have hf : Continuous f := (hFc.comp continuous_subtype_val).subtype_mk _
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hinj (b.subset_domain (hmark.symm.subset x.property).1)
      (b.subset_domain (hmark.symm.subset y.property).1) (congrArg Subtype.val hxy)
  have hfs : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, rfl⟩ := hJmark.subset hz
    exact ⟨⟨x, hx⟩, rfl⟩
  let Q := (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorphOfSurjective hfs
  let P := P0.trans Q
  have hP (x) : (P x : s → ℝ × V3) = F (hamiltonMarkedProjection ι κ L x) := by
    change F (P0 x) = _
    rw [hP0]
  refine ⟨s, F, K, A, H, J, P, hFc, hF, hK, hA, hKs, hA0, hA1, hA2,
    hH, hproj, rfl, inf_le_left, inf_le_right,
    hK.subset (le_trans inf_le_left (hA 0).1), ?_, hJs, hJmark, hP, ?_⟩
  · intro t ht htv
    exact ⟨(hA 0).2.2 t ht (fun v hv => (htv v hv).1),
      (hA 2).2.2 t ht (fun v hv => (htv v hv).2)⟩
  · intro x
    rw [hP]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, hzx⟩
      have hzpatch : z ∈ sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2) :=
        ⟨hz.1, sphere_subset_closedBall hz.2⟩
      have hzR : hamiltonMarkedProjection ι κ L z ∈ R :=
        b.subset_domain (hmark.symm.subset ⟨z, hzpatch, rfl⟩).1
      have hxR : hamiltonMarkedProjection ι κ L x ∈ R :=
        b.subset_domain (hmark.symm.subset ⟨x, x.property, rfl⟩).1
      have hzx' := b.markedProjection_injOn_attaching_patch hpos hzpatch x.property
        (hinj hzR hxR hzx)
      exact hzx' ▸ hz.2
    · intro hx
      exact ⟨hamiltonMarkedProjection ι κ L x, ⟨x, ⟨x.property.1, hx⟩, rfl⟩, rfl⟩

end PoincareConjecture.M76

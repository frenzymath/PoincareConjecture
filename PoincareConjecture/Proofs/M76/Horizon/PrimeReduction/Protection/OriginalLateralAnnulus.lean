import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AnnularRealization

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem HamiltonMarkedProtectedBall.exists_original_exterior_contact_annulus
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ∃ p : P2 → LatticeHandleAmbient ι κ L,
      PolyhedralPLInCharts e p Ann ∧ InjOn p Ann ∧
      p '' Ann = closure (latticeHandleDomain ι κ L \ D) ∩ D ∧
      ∀ z ∈ Ann, p z ∈ frontier (latticeHandleDomain ι κ L) ↔
        depth 8 z = -1 ∨ depth 8 z = 1 := by
  classical
  let R := latticeHandleDomain ι κ L
  let T := closure (R \ D) ∩ D
  obtain ⟨hι⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hi
  let : Unique ι := hι
  obtain ⟨s,F,K,J,B,H,g,d,r,ann,col,hFc,hF,hFi,hK,hKs,hH,hgc,hg,hgPL,
    hball,hJK,hBJ,hJ,hB,hJmark,hBmark,hd,hdis,hcover,hrcover,hann,hlo,hhi,_⟩ :=
    b.exists_original_disk_complement_model he (by omega)
  have hmark : D ∩ frontier R = hamiltonAttachingBlock ι κ L (3/2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hJactual : J.space = F '' (D ∩ frontier R) := by rw [hmark]; exact hJmark
  have hannends (z : Ann) : (ann z : s → ℝ × V3) ∈ J.space ↔
      depth 8 (z : P2) = -1 ∨ depth 8 (z : P2) = 1 := by
    constructor
    · intro hzJ
      have hzB : (ann z : s → ℝ × V3) ∈ B.space := by
        by_contra hn
        exact (ann z).property.2 ⟨hzJ,hn⟩
      exact (hrcover.symm.subset hzB).elim
        (fun h => Or.inl ((hlo z).mpr h)) (fun h => Or.inr ((hhi z).mpr h))
    · intro hz
      exact SimplicialComplex.space_subset_of_le hBJ (hrcover.subset
        (hz.elim (fun h => Or.inl ((hlo z).mp h)) (fun h => Or.inr ((hhi z).mp h))))
  have hTR : T ⊆ R := inter_subset_right.trans b.subset_domain
  have hT : T = frontier D \ (hamiltonAttachingBlock ι κ L (3/2) \
      hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3/2))) :=
    b.closed_complement_lateral_contact he hdim hi
  have hFT : F '' frontier D \ (J.space \ B.space) = F '' T := by
    apply Subset.antisymm
    · rintro y ⟨⟨x,hx,rfl⟩,hn⟩
      refine ⟨x,hT.symm.subset ⟨hx,?_⟩,rfl⟩
      rintro ⟨hxa,hxr⟩
      apply hn
      refine ⟨hJmark.symm.subset (mem_image_of_mem F hxa),?_⟩
      intro hxB
      obtain ⟨z,hz,hzx⟩ := hBmark.subset hxB
      have hzR : z ∈ R := by
        have hzJ := SimplicialComplex.space_subset_of_le hBJ
          (hBmark.symm.subset (mem_image_of_mem F hz))
        obtain ⟨w,hw,hwz⟩ := hJactual.subset hzJ
        have hzr : z ∈ D := by
          have h := image_mono (prod_mono subset_rfl sphere_subset_closedBall) hz
          exact (hmark.symm.subset h).1
        exact b.subset_domain hzr
      exact hxr (hFi hzR (b.subset_domain (b.ball.boundary_subset hx)) hzx ▸ hz)
    · rintro _ ⟨x,hx,rfl⟩
      have hxT := hT.subset hx
      refine ⟨mem_image_of_mem F hxT.1,?_⟩
      rintro ⟨hxJ,hxB⟩
      obtain ⟨y,hy,hyx⟩ := hJactual.subset hxJ
      have hyx' := hFi (b.subset_domain hy.1) (hTR hx) hyx
      apply hxT.2
      refine ⟨hmark.subset (hyx' ▸ hy),?_⟩
      intro hxr
      exact hxB (hBmark.symm.subset (mem_image_of_mem F hxr))
  have hphysical : Subtype.val '' (ann '' (Subtype.val ⁻¹' Ann : Set Ann)) = F '' T := by
    rw [show (Subtype.val ⁻¹' Ann : Set Ann) = univ by ext z; simp]
    rw [image_univ,ann.surjective.range_eq,image_univ,Subtype.range_coe_subtype]
    exact hFT
  obtain ⟨p,hp,hpi,hpfront,hpint,hpimage,hpF⟩ := exists_original_annulus_realization
    F hFi K hKs H hH g hg hgPL
    (b.ball.boundary_subset.trans b.subset_domain) b.ball.boundary_subset hTR
    hJactual ann hann hannends (Subset.rfl : Ann ⊆ Ann) hphysical
  refine ⟨p,hp,hpi,hpimage,?_⟩
  intro z hz
  have hzD : p z ∈ D := b.ball.boundary_subset (hpfront ⟨z,hz,rfl⟩)
  have hpR : p z ∈ R := b.subset_domain hzD
  have hm : p z ∈ frontier R ↔ F (p z) ∈ J.space := by
    rw [hJactual]
    constructor
    · exact fun h => ⟨p z,⟨hzD,h⟩,rfl⟩
    · rintro ⟨y,hy,hyz⟩
      exact hFi (b.subset_domain hy.1) hpR hyz ▸ hy.2
  rw [hm,hpF ⟨z,hz⟩]
  exact hannends ⟨z,hz⟩

end PoincareConjecture.M76

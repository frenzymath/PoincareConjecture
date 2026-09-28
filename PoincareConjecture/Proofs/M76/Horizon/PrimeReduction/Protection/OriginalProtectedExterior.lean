import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.ClosedComplementContact
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalDiskProtectedBallProduct
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ClosedAttachmentComponentCarriers
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Cube" => ((I ×ˢ I) ×ˢ I : Set P3)

theorem HamiltonMarkedProtectedBall.closed_complement_lateral_contact
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    closure (latticeHandleDomain ι κ L \ D) ∩ D =
      frontier D \ (hamiltonAttachingBlock ι κ L (3 / 2) \
        hamiltonMarkedProjection ι κ L ''
          (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))) := by
  classical
  let R := latticeHandleDomain ι κ L
  let T := frontier D \ (hamiltonAttachingBlock ι κ L (3 / 2) \
    hamiltonMarkedProjection ι κ L ''
      (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2)))
  obtain ⟨p,G,hp,hval,hpi,himage,hfront,hends,hattach,hfaces,hlat⟩ :=
    b.exists_original_disk_protected_ball_product_with_lateral he hdim hi
  have hmark : D ∩ frontier R = hamiltonAttachingBlock ι κ L (3 / 2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hTimage : T = p '' {z : P3 | z ∈ Cube ∧ (|z.1.1| = 1 ∨ |z.1.2| = 1)} := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨z,hz,rfl⟩ := himage.symm.subset (b.ball.isCompact.isClosed.frontier_subset hx.1)
      exact ⟨z,⟨hz,(hlat z hz).mp hx⟩,rfl⟩
    · rintro _ ⟨z,⟨hz,hzl⟩,rfl⟩
      exact (hlat z hz).mpr hzl
  have hTc : IsClosed T := by
    rw [hTimage]
    apply IsCompact.isClosed
    apply IsCompact.image_of_continuousOn _ (hp.continuousOn.mono (fun _ hz => hz.1))
    have hcube : IsCompact Cube := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
    exact hcube.inter_right ((isClosed_eq
      (continuous_fst.fst.abs) continuous_const).union
        (isClosed_eq (continuous_fst.snd.abs) continuous_const))
  have hsub : frontier D ∩ interior R ⊆ T := by
    intro x hx
    refine ⟨hx.1,?_⟩
    intro h
    exact (hmark.symm.subset h.1).2.2 hx.2
  have hEq : T = closure (frontier D ∩ interior R) := by
    apply Subset.antisymm _ (closure_minimal hsub hTc)
    intro x hx
    obtain ⟨z,⟨hz,hzl⟩,rfl⟩ := hTimage.subset hx
    let v : ℝ → P3 := fun t => (z.1,t * z.2)
    have hv : Continuous v := continuous_const.prodMk (continuous_id.mul_const _)
    have hvCube : MapsTo v (Icc (0 : ℝ) 1) Cube := by
      intro t ht
      refine ⟨hz.1,?_⟩
      change -1 ≤ t * z.2 ∧ t * z.2 ≤ 1
      constructor <;> nlinarith [hz.2.1,hz.2.2,ht.1,ht.2]
    have hc : ContinuousOn (p ∘ v) (Icc (0 : ℝ) 1) :=
      hp.continuousOn.comp hv.continuousOn hvCube
    have hm : MapsTo (p ∘ v) (Ioo (0 : ℝ) 1) (frontier D ∩ interior R) := by
      intro t ht
      have hzv := hvCube ⟨ht.1.le,ht.2.le⟩
      have htT : p (v t) ∈ T := (hlat _ hzv).mpr hzl
      refine ⟨htT.1,(mem_interior_iff_notMem_frontier
        (b.subset_domain (himage.subset ⟨v t,hzv,rfl⟩))).mpr ?_⟩
      intro hfR
      have hh := (hends _ hzv).mp hfR
      have habs : |t * z.2| < 1 := abs_lt.mpr (by
        constructor <;> nlinarith [hz.2.1,hz.2.2,ht.1,ht.2])
      exact (ne_of_lt habs) hh
    have h1 : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      norm_num
    have hh := ((hc.continuousWithinAt (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)).mono
      Ioo_subset_Icc_self).mem_closure h1 hm
    simpa only [Function.comp_apply,v,one_mul,Prod.mk.eta] using hh
  exact (he.closed_complement_contact b.ball.isCompact.isClosed b.subset_domain
    b.ball.closure_interior).trans hEq.symm

theorem HamiltonMarkedProtectedBall.closed_complement_geometry
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    let T := frontier D \ (hamiltonAttachingBlock ι κ L (3 / 2) \
      hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2)))
    IsCompact E ∧ E ⊆ R ∧ E ∪ D = R ∧ E ∩ D = T ∧
      interior E = interior R \ D ∧ closure (interior E) = E ∧
      frontier E = T ∪ (E ∩ frontier R) := by
  dsimp only
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  have hER : E ⊆ R := closure_minimal sdiff_subset he.closed
  have hD := b.ball.isCompact.isClosed
  have hEq := he.closure_sdiff_eq_closure_interior_sdiff hD
  have hout : E ⊆ (interior D)ᶜ := closure_minimal
    (fun _ hx hy => hx.2 (interior_subset hy)) isOpen_interior.isClosed_compl
  have hiout : interior E ⊆ Dᶜ := by
    have h := interior_mono hout
    rwa [interior_compl,b.ball.closure_interior] at h
  have hiE : interior E = interior R \ D := by
    apply Subset.antisymm
    · exact fun _ hx => ⟨interior_mono hER hx,hiout hx⟩
    · apply (isOpen_interior.sdiff hD).subset_interior_iff.mpr
      exact fun _ hx => subset_closure ⟨interior_subset hx.1,hx.2⟩
  have hreg : closure (interior E) = E := by rw [hiE]; exact hEq.symm
  have hcontact := b.closed_complement_lateral_contact he hdim hi
  refine ⟨(isCompact_latticeHandleDomain ι κ L).of_isClosed_subset isClosed_closure hER,
    hER,?_,hcontact,hiE,hreg,?_⟩
  · apply Subset.antisymm (union_subset hER b.subset_domain)
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inr hxD
    · exact Or.inl (subset_closure ⟨hx,hxD⟩)
  · rw [←hcontact]
    apply Subset.antisymm
    · intro x hx
      have hxE : x ∈ E := isClosed_closure.frontier_subset hx
      by_cases hxD : x ∈ D
      · exact Or.inl ⟨hxE,hxD⟩
      · exact Or.inr ⟨hxE,⟨subset_closure (hER hxE),fun hiR =>
          hx.2 (hiE.symm ▸ ⟨hiR,hxD⟩)⟩⟩
    · rintro x (hx | hx)
      · exact ⟨subset_closure hx.1,fun h => hiout h hx.2⟩
      · exact ⟨subset_closure hx.1,fun h => hx.2.2 (interior_mono hER h)⟩

theorem HamiltonMarkedProtectedBall.isConnected_closed_complement
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    IsConnected (closure (latticeHandleDomain ι κ L \ D)) := by
  classical
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  obtain ⟨hEc,hER,hunion,hcontact,_,_,_⟩ := b.closed_complement_geometry he hdim hi
  obtain ⟨p,G,hp,hval,hpi,himage,hfront,hends,hattach,hfaces,hlat⟩ :=
    b.exists_original_disk_protected_ball_product_with_lateral he hdim hi
  have hcub (z : P3) (hz : z ∈ sphere (0 : P2) 1 ×ˢ I) : z ∈ Cube := by
    have hh := sphere_subset_closedBall hz.1
    rw [mem_closedBall_zero_iff,Prod.norm_def,max_le_iff,Real.norm_eq_abs,
      Real.norm_eq_abs,abs_le,abs_le] at hh
    exact ⟨hh,hz.2⟩
  have hs : E ∩ D = p '' (sphere (0 : P2) 1 ×ˢ I) := by
    rw [hcontact]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨z,hz,rfl⟩ := himage.symm.subset (b.ball.isCompact.isClosed.frontier_subset hx.1)
      refine ⟨z,⟨?_,hz.2⟩,rfl⟩
      rw [mem_sphere_zero_iff_norm,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
      have habs1 : |z.1.1| ≤ 1 := abs_le.mpr hz.1.1
      have habs2 : |z.1.2| ≤ 1 := abs_le.mpr hz.1.2
      rcases (hlat _ hz).mp hx with h | h
      · rw [h,max_eq_left habs2]
      · rw [h,max_eq_right habs1]
    · rintro _ ⟨z,hz,rfl⟩
      apply (hlat _ (hcub z hz)).mpr
      have hh := hz.1
      rw [mem_sphere_zero_iff_norm,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs] at hh
      rcases le_total |z.1.1| |z.1.2| with h | h
      · exact Or.inr (by simpa only [max_eq_right h] using hh)
      · exact Or.inl (by simpa only [max_eq_left h] using hh)
  have hED : IsConnected (E ∩ D) := by
    rw [hs]
    exact ((isConnected_sphere (by simp; norm_num) (0 : P2) zero_le_one).prod
      (isConnected_Icc (by norm_num : (-1 : ℝ) ≤ 1))).image p
        (hp.continuousOn.mono (fun z hz => hcub z hz))
  let : ConnectedSpace ((κ → ℝ) ⧸ L.toAddSubgroup) :=
    QuotientAddGroup.mk_surjective.connectedSpace QuotientAddGroup.continuous_mk
  have hR : IsConnected R :=
    ((convex_closedBall (0 : ι → ℝ) 1).isConnected
      ⟨0,mem_closedBall_self zero_le_one⟩).prod isConnected_univ
  obtain ⟨x,hxE,hxD⟩ := hED.nonempty
  have hcomp : E = connectedComponentIn E x := by
    apply Subset.antisymm _ (connectedComponentIn_subset _ _)
    intro y hy
    apply (Topology.mem_componentIn_closed_attachment_iff hEc.isClosed
      b.ball.isCompact.isClosed (b.ball.closure_interior ▸ b.ball.isConnected_interior.closure)
      hED hxE hy).mp
    rw [hunion,hR.isPreconnected.connectedComponentIn (hER hxE)]
    exact hER hy
  change IsConnected E
  rw [hcomp]
  exact ⟨⟨x,mem_connectedComponentIn hxE⟩,isPreconnected_connectedComponentIn⟩

end PoincareConjecture.M76

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedCrossingBoundaryValues
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AttachingDiskComplement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalLateralAnnulus
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.AnnulusConnected

set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.isConnected_closed_complement_frontier
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    IsConnected (frontier (closure (latticeHandleDomain ι κ L \ D))) := by
  classical
  obtain ⟨hι⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hi
  let : Unique ι := hι
  let : Nonempty κ := Fintype.card_pos_iff.mp (by omega)
  let q : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup := QuotientAddGroup.mk
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  let T := E ∩ D
  let A := (q '' Metric.ball (0 : κ → ℝ) (3/2))ᶜ
  let sides (t : ℝ) : Set (LatticeHandleAmbient ι κ L) := {fun _ => t} ×ˢ A
  have hAc : IsConnected A := b.isConnected_attaching_disk_complement (by omega) (by omega)
  have hside (t : ℝ) : IsConnected (sides t) := isConnected_singleton.prod hAc
  have hmark : D ∩ frontier R = hamiltonAttachingBlock ι κ L (3/2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  obtain ⟨hEc,hER,hunion,hcontact,_,_,hfront⟩ := b.closed_complement_geometry he hdim hi
  have hold : E ∩ frontier R = sphere (0 : ι → ℝ) 1 ×ˢ A := by
    ext x
    have hf : x ∈ frontier R ↔ x.1 ∈ sphere (0 : ι → ℝ) 1 := by
      simp only [R,latticeHandleDomain,frontier_prod_univ_eq,
        frontier_closedBall _ one_ne_zero,mem_prod,mem_univ,and_true]
    constructor
    · rintro ⟨hxE,hxf⟩
      refine ⟨hf.mp hxf,?_⟩
      rintro ⟨z,hz,hzx⟩
      have hxatt : x ∈ hamiltonAttachingBlock ι κ L (3/2) :=
        ⟨(x.1,z),⟨hf.mp hxf,ball_subset_closedBall hz⟩,Prod.ext rfl hzx⟩
      have hxD := (hmark.symm.subset hxatt).1
      have hxT := hcontact.subset ⟨hxE,hxD⟩
      apply hxT.2
      refine ⟨hxatt,?_⟩
      rintro ⟨w,hw,hwx⟩
      have heq := b.quotient_injOn_attaching_disk (by omega)
        (sphere_subset_closedBall hw.2) (ball_subset_closedBall hz)
        ((congrArg Prod.snd hwx).trans hzx.symm)
      have hn : dist w.2 0 = 3/2 := hw.2
      have hz' : dist z 0 < 3/2 := hz
      rw [heq] at hn
      linarith
    · rintro ⟨hxf,hxA⟩
      exact ⟨b.old_boundary_outside_open_patch_mem_exterior he hdim hi (hf.mpr hxf) hxA,
        hf.mpr hxf⟩
  have hsides : sphere (0 : ι → ℝ) 1 ×ˢ A = sides (-1) ∪ sides 1 := by
    ext x
    have hconst : x.1 = (fun _ => x.1 default) :=
      funext (fun i => congrArg x.1 (Subsingleton.elim i default))
    have hn : ‖x.1‖ = |x.1 default| := by
      conv_lhs => rw [hconst]
      simp only [pi_norm_const,Real.norm_eq_abs]
    simp only [sides,mem_prod,mem_sphere_zero_iff_norm,hn,mem_union,mem_singleton_iff]
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
    constructor
    · rintro ⟨h|h,hA⟩
      · exact Or.inr ⟨hconst.trans (by rw [h]),hA⟩
      · exact Or.inl ⟨hconst.trans (by rw [h]),hA⟩
    · rintro (⟨h,hA⟩|⟨h,hA⟩)
      · exact ⟨Or.inr (congrFun h default),hA⟩
      · exact ⟨Or.inl (congrFun h default),hA⟩
  obtain ⟨p,hp,_,himage,_⟩ := b.exists_original_exterior_contact_annulus he hdim hi
  have hTc : IsPreconnected T := by
    change IsPreconnected (closure (latticeHandleDomain ι κ L \ D) ∩ D)
    rw [← himage]
    exact (isPreconnected_complete_squareAnnulus (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (4 : ℝ) * 1 < 8)).image p hp.continuousOn
  have hmeet (t : ℝ) (ht : |t| = 1) : (T ∩ sides t).Nonempty := by
    let z : κ → ℝ := fun _ => 3/2
    have hz : z ∈ sphere (0 : κ → ℝ) (3/2) := by
      simp [z,pi_norm_const]
    have hf : (fun _ : ι => t) ∈ sphere (0 : ι → ℝ) 1 := by
      simpa [mem_sphere_zero_iff_norm,pi_norm_const,Real.norm_eq_abs] using ht
    let x : LatticeHandleAmbient ι κ L := (fun _ => t,q z)
    have hrim : x ∈ hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3/2)) :=
      ⟨((fun _ => t),z),⟨hf,hz⟩,rfl⟩
    have hxatt := image_mono (prod_mono subset_rfl sphere_subset_closedBall) hrim
    have hxD := (hmark.symm.subset hxatt).1
    have hxf := (hmark.symm.subset hxatt).2
    have hxfront := ((b.ball.frontier_inter_eq_of_subset b.subset_domain).symm.subset
      ⟨hxD,hxf⟩).1
    have hxT : x ∈ T := hcontact.symm.subset ⟨hxfront,fun h => h.2 hrim⟩
    refine ⟨x,hxT,?_,?_⟩
    · rfl
    · rintro ⟨w,hw,hwx⟩
      have heq := b.quotient_injOn_attaching_disk (by omega)
        (ball_subset_closedBall hw) (sphere_subset_closedBall hz) hwx
      subst w
      have hn : dist z 0 = 3/2 := hz
      have hn' : dist z 0 < 3/2 := hw
      linarith
  have hm := hmeet (-1) (by norm_num)
  have hp' := hmeet 1 (by norm_num)
  have hc := hTc.union' hm (hside (-1)).isPreconnected
  have hc' := hc.union' (hp'.mono (by intro x hx; exact ⟨Or.inl hx.1,hx.2⟩))
    (hside 1).isPreconnected
  rw [hfront,← hcontact,hold,hsides,← union_assoc]
  exact ⟨hm.mono (fun _ hx => Or.inl (Or.inl hx.1)),hc'⟩

end PoincareConjecture.M76

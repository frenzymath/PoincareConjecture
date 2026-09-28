import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalFiniteInwardCompression
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedArcSphereObstruction
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology











set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.OriginalFiniteCollarModel
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_inward_compression_with_ball_confinement
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (M : OriginalFiniteCollarModel e R) :
    ∃ (D : Set (M.vertices → ℝ × V3)) (H : M.complex.space ≃ₜ D),
      H.IsFinitePL ∧ D ⊆ M.complex.space ∧ Disjoint D M.boundary.space ∧
      D = M.complex.space \ M.collar '' (M.collarBase.space ×ˢ Ico (0 : ℝ) (1/2)) ∧
      ∀ (B S : Set X), ChartwisePLBall e B S → B ⊆ R →
        S ⊆ (fun z => (M.inverse z : X)) '' D →
        B ⊆ (fun z => (M.inverse z : X)) '' D := by
  classical
  obtain ⟨D,H,hH,hDK,hval,hfix,hclear⟩ :=
    Dehn.exists_inward_collar_compression M.complex M.collarBase M.finite
      M.collar_finite M.collar M.collar_pl M.collar_injective M.collar_inside M.collar_open
  have hDA : Disjoint D M.boundary.space := by
    apply disjoint_left.mpr
    intro y hyD hyA
    obtain ⟨x,hx⟩ := M.collarHomeomorph.surjective ⟨y,hyA⟩
    have hc : M.collar ((x : M.collarVertices → ℝ × V3),0) = y :=
      (M.collar_zero x).trans (congrArg Subtype.val hx)
    have ht := (hclear _ ⟨x.property,le_rfl,zero_le_one⟩).mp (hc.symm ▸ hyD)
    norm_num at ht
  have hDchar : D = M.complex.space \
      M.collar '' (M.collarBase.space ×ˢ Ico (0 : ℝ) (1/2)) := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨hDK hx,?_⟩
      rintro ⟨z,hz,rfl⟩
      exact not_le_of_gt hz.2.2 ((hclear z ⟨hz.1,hz.2.1,by linarith [hz.2.2]⟩).mp hx)
    · intro x hx
      by_cases hc : x ∈ M.collar '' (M.collarBase.space ×ˢ Ico (0 : ℝ) 1)
      · obtain ⟨z,hz,rfl⟩ := hc
        apply (hclear z ⟨hz.1,hz.2.1,hz.2.2.le⟩).mpr
        by_contra hn
        exact hx.2 ⟨z,⟨hz.1,hz.2.1,lt_of_not_ge hn⟩,rfl⟩
      · have heq : (H ⟨x,hx.1⟩ : M.vertices → ℝ × V3) = x := hfix ⟨x,hx.1⟩ hc
        exact heq ▸ (H ⟨x,hx.1⟩).property
  let g := fun z => (M.inverse z : X)
  have hgi : InjOn g M.complex.space := by
    intro x hx y hy hxy
    have hh : M.homeomorph.symm ⟨x,hx⟩ = M.homeomorph.symm ⟨y,hy⟩ :=
      Subtype.ext ((M.inverse_eq ⟨x,hx⟩).symm.trans (hxy.trans (M.inverse_eq ⟨y,hy⟩)))
    exact congrArg Subtype.val (M.homeomorph.symm.injective hh)
  have hcore : g '' D ⊆ interior R := by
    rintro _ ⟨z,hz,rfl⟩
    have hnot : g z ∉ frontier R := fun h => disjoint_left.mp hDA hz
      ((M.boundary_eq z (hDK hz)).mp h)
    by_contra hn
    exact hnot ⟨subset_closure (M.inverse z).property,hn⟩
  refine ⟨D,H,hH,hDK,hDA,hDchar,?_⟩
  intro B S b hBR hS x hx
  have hBint := b.subset_interior hBR (hS.trans hcore)
  by_contra hn
  let z := M.coordinates x
  have hzK : z ∈ M.complex.space := M.coordinates_mapsTo (hBR hx)
  have hzval : g z = x := M.inverse_coordinates x (hBR hx)
  have hznot : z ∉ D := fun hz => hn ⟨z,hz,hzval⟩
  have hzcollar : z ∈ M.collar '' (M.collarBase.space ×ˢ Ico (0 : ℝ) (1/2)) := by
    by_contra hz
    exact hznot (hDchar.symm ▸ ⟨hzK,hz⟩)
  obtain ⟨p,hp,hpz⟩ := hzcollar
  let C := (fun t : ℝ => g (M.collar (p.1,t))) '' Icc 0 p.2
  have hsub (t : ℝ) (ht : t ∈ Icc 0 p.2) : (p.1,t) ∈ M.collarBase.space ×ˢ I :=
    ⟨hp.1,ht.1,by linarith [ht.2,hp.2.2]⟩
  have hcont : ContinuousOn (fun t : ℝ => g (M.collar (p.1,t))) (Icc 0 p.2) :=
    M.inverse_pl.continuousOn.comp
      (M.collar_pl.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hsub)
      (fun t ht => M.collar_inside (hsub t ht))
  have hconn : IsPreconnected C := (convex_Icc (0 : ℝ) p.2).isPreconnected.image _ hcont
  have havoid : Disjoint C (frontier B) := by
    apply disjoint_left.mpr
    rintro y ⟨t,ht,rfl⟩ hy
    rw [b.frontier_eq] at hy
    obtain ⟨w,hw,heq⟩ := hS hy
    have heq' : w = M.collar (p.1,t) := hgi (hDK hw) (M.collar_inside (hsub t ht)) heq
    have ht' := (hclear (p.1,t) (hsub t ht)).mp (heq' ▸ hw)
    dsimp at ht'
    linarith [ht.2,hp.2.2]
  have hxC : x ∈ C := ⟨p.2,⟨hp.2.1,le_rfl⟩,by change g (M.collar p) = x; rw [hpz]; exact hzval⟩
  have hzeroC : g (M.collar (p.1,0)) ∈ C := ⟨0,⟨le_rfl,hp.2.1⟩,rfl⟩
  have hzeroFront : g (M.collar (p.1,0)) ∈ frontier R := by
    apply (M.boundary_eq _ (M.collar_inside (hsub 0 ⟨le_rfl,hp.2.1⟩))).mpr
    rw [M.collar_zero ⟨p.1,hp.1⟩]
    exact (M.collarHomeomorph ⟨p.1,hp.1⟩).property
  rcases preconnected_interior_or_exterior_of_frontier_avoidance b.isCompact.isClosed hconn havoid with hi | ho
  · exact hzeroFront.2 (hBint (interior_subset (hi hzeroC)))
  · exact ho hxC hx

end PoincareConjecture.M76.OriginalFiniteCollarModel


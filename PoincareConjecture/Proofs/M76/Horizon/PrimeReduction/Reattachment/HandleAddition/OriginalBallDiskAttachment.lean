import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalFiniteCollarModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFiniteModelBallImages
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage
import PoincareConjecture.Proofs.M76.Triangulation.PLBallActualDiskAttachment








set_option autoImplicit false
open Set Geometry Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem ChartwisePLBall.union_of_original_disk_contact
    {X α A : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    {e : α → OpenPartialHomeomorph X V3} {R B U S T : Set X}
    (he : PLDomain e R) (hR : IsCompact R)
    (b : ChartwisePLBall e B S) (u : ChartwisePLBall e U T)
    (hBR : B ⊆ R) (hUR : U ⊆ R)
    {d q : Set A} (hd : IsFinitePLBallPair P2 d q)
    (p : A → X) (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hdS : p '' d ⊆ S) (hdT : p '' d ⊆ T)
    (hSout : (S \ p '' d).Nonempty) (hTout : (T \ p '' d).Nonempty)
    (hBU : B ∩ U = p '' d) :
    Nonempty (ChartwisePLBall e (B ∪ U)
      ((S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q)))) := by
  classical
  have hSne := hSout
  obtain ⟨x,hxS,_⟩ := hSne
  obtain ⟨M⟩ := he.nonempty_original_finite_collar_model hR ⟨x,hBR (b.boundary_subset hxS)⟩
  let F := M.coordinates
  let g : (M.vertices → ℝ × V3) → X := fun z => M.inverse z
  have hSR : S ⊆ R := b.boundary_subset.trans hBR
  have hTR : T ⊆ R := u.boundary_subset.trans hUR
  have hdR : p '' d ⊆ R := hdS.trans hSR
  have hqR : p '' q ⊆ R := (image_mono hd.1).trans hdR
  let v : V3 ≃L[ℝ] P3 := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hb := (b.finitePLBallPair_image hBR F M.coordinates_pl M.coordinates_injective).model_equiv v
  have hu := (u.finitePLBallPair_image hUR F M.coordinates_pl M.coordinates_injective).model_equiv v
  have hd' := finitePLBallPair_original_image hd hp subset_rfl hpi
    (fun z hz => hdR (mem_image_of_mem p hz)) M.coordinates_pl M.coordinates_injective
  have hout {Z : Set X} (hZR : Z ⊆ R) (hout : (Z \ p '' d).Nonempty) :
      (F '' Z \ F '' (p '' d)).Nonempty := by
    obtain ⟨z,hz,hzd⟩ := hout
    refine ⟨F z,mem_image_of_mem F hz,?_⟩
    rintro ⟨y,hy,hyz⟩
    exact hzd (M.coordinates_injective (hdR hy) (hZR hz) hyz ▸ hy)
  have hmeet : F '' B ∩ F '' U = F '' (p '' d) := by
    apply Subset.antisymm
    · rintro z ⟨⟨x,hx,rfl⟩,y,hy,hxy⟩
      have h := M.coordinates_injective (hUR hy) (hBR hx) hxy
      exact mem_image_of_mem F (hBU.subset ⟨hx,h ▸ hy⟩)
    · intro z hz
      exact ⟨image_mono (hBU.symm.subset.trans inter_subset_left) hz,
        image_mono (hBU.symm.subset.trans inter_subset_right) hz⟩
  have hball := hb.union_of_actual_disk_contact hu hd' (image_mono hdS) (image_mono hdT)
    (hout hSR hSout) (hout hTR hTout) hmeet
  have hdiff {Z W : Set X} (hZR : Z ⊆ R) (hWR : W ⊆ R) :
      F '' (Z \ W) = F '' Z \ F '' W := by
    ext z
    constructor
    · rintro ⟨x,⟨hx,hxn⟩,rfl⟩
      refine ⟨mem_image_of_mem F hx,?_⟩
      rintro ⟨y,hy,hyx⟩
      exact hxn (M.coordinates_injective (hWR hy) (hZR hx) hyx ▸ hy)
    · rintro ⟨⟨x,hx,rfl⟩,hxn⟩
      exact ⟨x,⟨hx,fun h => hxn (mem_image_of_mem F h)⟩,rfl⟩
  have hboundary :
      (F '' S \ (F '' (p '' d) \ F '' (p '' q))) ∪
        (F '' T \ (F '' (p '' d) \ F '' (p '' q))) =
      F '' ((S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q))) := by
    rw [image_union,hdiff hSR (sdiff_subset.trans hdR),
      hdiff hTR (sdiff_subset.trans hdR),hdiff hdR hqR]
  rw [hboundary,←image_union] at hball
  have hsub : F '' (B ∪ U) ⊆ M.complex.space := by
    rintro _ ⟨x,hx,rfl⟩
    exact M.coordinates_mapsTo ((union_subset hBR hUR) hx)
  have hgi : InjOn g M.complex.space := by
    intro x hx y hy hxy
    have hh : M.homeomorph.symm ⟨x,hx⟩ = M.homeomorph.symm ⟨y,hy⟩ :=
      Subtype.ext ((M.inverse_eq ⟨x,hx⟩).symm.trans (hxy.trans (M.inverse_eq ⟨y,hy⟩)))
    exact congrArg Subtype.val (M.homeomorph.symm.injective hh)
  have himage {Z : Set X} (hZR : Z ⊆ R) : g '' (F '' Z) = Z := by
    rw [image_image]
    simpa only [image_id'] using image_congr (fun x hx => M.inverse_coordinates x (hZR hx))
  obtain ⟨joined⟩ := exists_chartwisePLBall_image hball v.symm M.inverse_pl hsub hgi
  rw [himage (union_subset hBR hUR),
    himage (union_subset (sdiff_subset.trans hSR) (sdiff_subset.trans hTR))] at joined
  exact ⟨joined⟩

end PoincareConjecture.M76

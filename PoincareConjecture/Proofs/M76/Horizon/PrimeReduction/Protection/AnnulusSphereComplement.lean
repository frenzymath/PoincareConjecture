import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AnnulusOutsidePoint
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Collars.FinitePLBallBoundaryCollar







set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Ann" => squareAnnulus 8 1

theorem exists_annulus_sphere_complement_disks
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B S A : Set E} (hB : IsFinitePLBallPair V3 B S)
    (H : Ann ≃ₜ A) (hH : H.IsFinitePL) (hAS : A ⊆ S) :
    ∃ d r : Bool → Set E,
      (∀ i, IsFinitePLBallPair P2 (d i) (r i) ∧ d i ⊆ S ∧
        d i ∩ A = r i ∧ r i = (fun z : Ann => (H z : E)) ''
          {z | depth 8 z = if i then 1 else -1}) ∧
      Disjoint (d true) (d false) ∧ (d true ∪ d false) ∪ A = S := by
  classical
  obtain ⟨u,hu,hub⟩ := hB.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  obtain ⟨_,L,_,_,hL,hLs⟩ := hB.exists_finite_carrier_and_rim_complexes
  let uS := u.restrictSubsets hB.1 isClosed_closedBall.frontier_subset hub
  have huS : uS.IsFinitePL :=
    hu.restrictSubsets hB.1 isClosed_closedBall.frontier_subset hub L hL hLs
  let Z : S ≃ₜ Sphere := uS.trans (Homeomorph.setCongr (frontier_closedBall _ one_ne_zero))
  have hZ : Z.IsFinitePL := huS.setCongr rfl (frontier_closedBall _ one_ne_zero)
  have hZcopy := hZ
  obtain ⟨f,hf,hfval⟩ := hZcopy
  obtain ⟨g,hg,hgval⟩ := hZ.symm
  have hgf : LeftInvOn g f S := by
    intro x hx
    rw [← hfval ⟨x,hx⟩,← hgval,Z.symm_apply_apply]
  have hfg : LeftInvOn f g Sphere := by
    intro x hx
    rw [← hgval ⟨x,hx⟩,← hfval,Z.apply_symm_apply]
  have hfS : f '' S = Sphere := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [← hfval ⟨x,hx⟩]
      exact (Z ⟨x,hx⟩).property
    · intro y hy
      exact ⟨Z.symm ⟨y,hy⟩,(Z.symm ⟨y,hy⟩).property,
        (hfval _).symm.trans (congrArg Subtype.val (Z.apply_symm_apply _))⟩
  have hgS : g '' Sphere = S := by
    rw [← hfS]
    exact hgf.image_image
  have hcopy := hH
  obtain ⟨a,ha,haval⟩ := hcopy
  have haA : a '' Ann = A := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [← haval ⟨x,hx⟩]
      exact (H ⟨x,hx⟩).property
    · intro x hx
      exact ⟨H.symm ⟨x,hx⟩,(H.symm ⟨x,hx⟩).property,
        (haval _).symm.trans (congrArg Subtype.val (H.apply_symm_apply _))⟩
  have hai : InjOn a Ann := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((haval ⟨x,hx⟩).trans (hxy.trans (haval ⟨y,hy⟩).symm))))
  have haS : MapsTo a Ann S := fun _ hx => hAS (haA.subset (mem_image_of_mem _ hx))
  have hfa : FinitePiecewiseAffineOn (f ∘ a) Ann := hf.comp ha haS
  obtain ⟨c,hc,hcval⟩ := hfa.exists_homeomorph_image (hgf.injOn.comp hai haS)
  have hband : (f ∘ a) '' Ann ⊆ Sphere := by
    rw [image_comp,haA]
    exact (image_mono hAS).trans hfS.subset
  have hout : (Sphere \ (f ∘ a) '' Ann).Nonempty := by
    by_contra hn
    have heq : (f ∘ a) '' Ann = Sphere :=
      Subset.antisymm hband (by intro x hx; by_contra h; exact hn ⟨x,hx,h⟩)
    let v : V3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    let N := PoincareConjecture.Proofs.M02.Topology.unitSphereHomeomorph v
    let : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      PoincareConjecture.Proofs.M02.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
    exact not_simplyConnected_squareAnnulus (by norm_num) (by norm_num)
      ((c.trans (Homeomorph.setCongr heq)).trans N).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨p,hp,hpout⟩ := hout
  obtain ⟨k,q,_,hq,hk,hdis,hcover,_⟩ :=
    exists_sphere_annulus_product_balls c hc hband ⟨p,hp⟩ hpout
  have hback : g '' ((f ∘ a) '' Ann) = A := by
    rw [image_comp,haA]
    exact (hgf.mono hAS).image_image
  refine ⟨fun i => g '' k i,fun i => g '' q i,?_,?_,?_⟩
  · intro i
    refine ⟨(hk i).1.image_of_subset hg (hk i).2.1 hfg.injOn,
      (image_mono (hk i).2.1).trans hgS.subset,?_,?_⟩
    · rw [← hback,← hfg.injOn.image_inter (hk i).2.1 hband,(hk i).2.2]
    · dsimp only
      rw [hq i,image_image]
      apply image_congr
      intro z _
      rw [hcval z]
      exact (hgf (haS z.property)).trans (haval z).symm
  · apply disjoint_left.mpr
    rintro x ⟨a,ha,rfl⟩ ⟨b,hb,hba⟩
    exact disjoint_left.mp hdis ha
      (hfg.injOn ((hk false).2.1 hb) ((hk true).2.1 ha) hba ▸ hb)
  · rw [← hback,← image_union,← image_union,hcover,hgS]

end PoincareConjecture.M76

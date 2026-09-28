import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SphereSurgeryNonbounding
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import PoincareConjecture.Proofs.M76.Mathlib.ContractibleBallExtension
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.BoundaryDisks.JordanFillingCoverage
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere.SphereDiskExtension

set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

theorem OriginalDiskProduct.center_rim_nullhomotopic_of_retained_disk_avoids_frontier
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R S E : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (hE : IsClosed E) {d q : Set V3} (hd : IsFinitePLBallPair P2 d q)
    (hdS : d ⊆ Sphere) (b : Bool) (hqr : s.map '' q = P.capRimSet b)
    (havoid : Disjoint (s.map '' d) (frontier E))
    (hband : P.map '' (Rim ×ˢ J) ⊆ S ∩ interior E) :
    ∃ gamma : C(Rim, ↥(S ∩ interior E)),
      (∀ z : Rim, (gamma z : X) = P.map (z,0)) ∧ gamma.Nullhomotopic := by
  classical
  let t : ℝ := if b then 1/2 else -(1/2)
  have htJ : t ∈ J := by cases b <;> norm_num [t]
  have hretS : s.map '' d ⊆ S := by
    rintro _ ⟨z,hz,rfl⟩
    rw [s.map_eq ⟨z,hdS hz⟩]
    exact (s.parametrization ⟨z,hdS hz⟩).property
  have hc : ContinuousOn s.map d := s.piecewiseAffine.continuousOn.mono hdS
  have hret : s.map '' d ⊆ interior E := by
    rcases preconnected_interior_or_exterior_of_frontier_avoidance hE
      (hd.isConnected.isPreconnected.image s.map hc) havoid with hin | hout
    · exact hin
    · have hone : (1 : V2) ∈ Rim := by simp
      have hr : P.map ((1 : V2),t) ∈ s.map '' d := by
        apply image_mono hd.1
        exact hqr.symm.subset ⟨((1 : V2),t),⟨hone,rfl⟩,rfl⟩
      exact (hout hr (interior_subset (hband ⟨((1 : V2),t),⟨hone,htJ⟩,rfl⟩).2)).elim
  have hretE : s.map '' d ⊆ S ∩ interior E := fun x hx => ⟨hretS hx,hret hx⟩
  let f : C(d,↥(S ∩ interior E)) := ⟨fun z => ⟨s.map z,hretE ⟨z,z.property,rfl⟩⟩,
    hc.domRestrict.subtype_mk _⟩
  have hsi : InjOn s.map d := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hdS hx⟩,s.map_eq ⟨y,hdS hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  let : CompactSpace d := isCompact_iff_compactSpace.mp hd.isCompact
  let H : d ≃ₜ (s.map '' d) := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn s.map d hsi) (hc.domRestrict.subtype_mk _)
  have hH (z : d) : (H z : X) = s.map z := rfl
  have hPL : ContinuousOn P.map (Disk ×ˢ Icc (-1 : ℝ) 1) := P.polyhedral.continuousOn
  have hsmall : Rim ×ˢ J ⊆ Disk ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨z,u⟩ ⟨hz,hu⟩
    exact ⟨sphere_subset_closedBall hz,by constructor <;> linarith [hu.1,hu.2]⟩
  have hendpoint : Continuous (fun z : Rim => P.map (z,t)) :=
    hPL.comp_continuous (continuous_subtype_val.prodMk continuous_const)
      (fun z => hsmall ⟨z.property,htJ⟩)
  have hendret (z : Rim) : P.map (z,t) ∈ s.map '' d :=
    image_mono hd.1 (hqr.symm.subset ⟨((z : V2),t),⟨z.property,rfl⟩,rfl⟩)
  let endRet : C(Rim,s.map '' d) :=
    ⟨fun z => ⟨P.map (z,t),hendret z⟩,hendpoint.subtype_mk _⟩
  let lift : C(Rim,d) := (⟨H.symm,H.symm.continuous⟩ : C(_,d)).comp endRet
  let endpoint : C(Rim,↥(S ∩ interior E)) :=
    ⟨fun z => ⟨P.map (z,t),hband ⟨((z : V2),t),⟨z.property,htJ⟩,rfl⟩⟩,
      hendpoint.subtype_mk _⟩
  have heq : f.comp lift = endpoint := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    exact (hH (H.symm (endRet z))).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply (endRet z)))
  have hdcontractible : ContractibleSpace d := by
    obtain ⟨_,C,_,hcv,hne,HC,_,_⟩ := hd
    let : Nonempty C := ⟨⟨hne.some,interior_subset hne.some_mem⟩⟩
    let : ContractibleSpace C := hcv.contractibleSpace (hne.mono interior_subset)
    exact HC.contractibleSpace
  let := hdcontractible
  have hendnull : endpoint.Nullhomotopic := by
    rw [←heq]
    exact ((id_nullhomotopic d).comp_right f).comp_left lift
  have hzero : (0 : ℝ) ∈ J := by norm_num
  let gamma : C(Rim,↥(S ∩ interior E)) :=
    ⟨fun z => ⟨P.map (z,0),hband ⟨((z : V2),0),⟨z.property,hzero⟩,rfl⟩⟩,
      (hPL.comp_continuous (continuous_subtype_val.prodMk continuous_const)
        (fun z => hsmall ⟨z.property,hzero⟩)).subtype_mk _⟩
  have htime (u : unitInterval) : (u : ℝ) * t ∈ J := by
    cases b <;> dsimp [t] <;> constructor <;> nlinarith [u.property.1,u.property.2]
  let hom : gamma.Homotopy endpoint := {
    toFun := fun z => ⟨P.map ((z.2 : V2),(z.1 : ℝ)*t),
      hband ⟨((z.2 : V2),(z.1 : ℝ)*t),⟨z.2.property,htime z.1⟩,rfl⟩⟩
    continuous_toFun := (hPL.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk
        ((continuous_subtype_val.comp continuous_fst).mul_const t))
      (fun z => hsmall ⟨z.2.property,htime z.1⟩)).subtype_mk _
    map_zero_left := fun z => by apply Subtype.ext; simp [gamma]
    map_one_left := fun z => by apply Subtype.ext; simp [endpoint] }
  obtain ⟨x,hx⟩ := hendnull
  exact ⟨gamma,fun _ => rfl,x,(show gamma.Homotopic endpoint from ⟨hom⟩).trans hx⟩

theorem polygon_closed_inside_subset_of_nullhomotopic_rim
    {A : Set P2} {n : ℕ} (P : Polygon P2 (n+3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (gamma : C(Rim,A)) (hgamma : Function.Injective gamma)
    (himage : range (fun z => (gamma z : P2)) = P.boundary ℝ)
    (hnull : gamma.Nullhomotopic) : closure P.inside ⊆ A := by
  classical
  let Plane := EuclideanSpace ℝ (Fin 2)
  let a : P2 ≃L[ℝ] Plane := ContinuousLinearEquiv.ofFinrankEq (by simp [Plane])
  let c : V2 ≃L[ℝ] Plane := ContinuousLinearEquiv.ofFinrankEq (by simp [Plane])
  let H := Poincare.Topology.unitSphereHomeomorph c
  obtain ⟨g,hg⟩ := hnull.exists_closedBall_extension gamma
  let G : C(Disk,Plane) :=
    ⟨fun z => a (g z : P2),a.continuous.comp (continuous_subtype_val.comp g.continuous)⟩
  let inc : C(sphere (0 : Plane) 1,Disk) :=
    ⟨fun z => ⟨H.symm z,sphere_subset_closedBall (H.symm z).property⟩,
      (continuous_subtype_val.comp H.symm.continuous).subtype_mk _⟩
  let r : C(sphere (0 : Plane) 1,Plane) :=
    ⟨fun z => a (gamma (H.symm z) : P2),
      a.continuous.comp (continuous_subtype_val.comp (gamma.continuous.comp H.symm.continuous))⟩
  have hr : Function.Injective r := by
    intro x y hxy
    exact H.symm.injective (hgamma (Subtype.ext (a.injective hxy)))
  have hrange : range r = a '' P.boundary ℝ := by
    rw [←himage]
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨gamma (H.symm z),⟨H.symm z,rfl⟩,rfl⟩
    · rintro ⟨_,⟨z,rfl⟩,rfl⟩
      exact ⟨H z,by simp [r]⟩
  have hUb : Bornology.IsBounded (a '' P.inside) :=
    ((P.isCompact_closure_inside hP hPi).image a.continuous).isBounded.subset
      (image_mono subset_closure)
  have hfront : frontier (a '' P.inside) = range r := by
    rw [hrange]
    exact (a.toHomeomorph.image_frontier P.inside).symm.trans
      (congrArg (fun Z : Set P2 => a '' Z) (P.frontier_inside hP hPi))
  have hfill := bounded_jordan_side_subset_filling G r hr inc
    (fun z => congrArg (fun x : A => a (x : P2)) (hg (H.symm z))) hUb hfront
  have hin : P.inside ⊆ A := by
    intro x hx
    obtain ⟨z,hz⟩ := hfill ⟨x,hx,rfl⟩
    have hv : (g z : P2) = x := a.injective hz
    exact hv ▸ (g z).property
  rw [closure_eq_self_union_frontier,P.frontier_inside hP hPi]
  apply union_subset hin
  intro x hx
  obtain ⟨z,rfl⟩ := himage.symm.subset hx
  exact (gamma z).property

theorem OriginalDiskProduct.retained_disk_contact_of_nondisk_planar_rim
    {X α : Type*} [MetricSpace X]
    {e : α → OpenPartialHomeomorph X V3} {R S E : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (hE : IsClosed E) {d q : Set V3} (hd : IsFinitePLBallPair P2 d q)
    (hdS : d ⊆ Sphere) (b : Bool) (hqr : s.map '' q = P.capRimSet b)
    (hband : P.map '' (Rim ×ˢ J) ⊆ S ∩ interior E)
    {A B : Set P2} (hA : IsCompact A) (p : P2 → X)
    (hp : ContinuousOn p A) (hpi : InjOn p A) (hps : p '' A = S ∩ E)
    (hproper : ∀ z ∈ A, p z ∈ frontier E ↔ z ∈ B)
    {n : ℕ} (L : Polygon P2 (n+3)) (hL : L.HasSimplicialEdges)
    (hLi : Function.Injective L) (hLA : L.boundary ℝ ⊆ interior A)
    (hcenter : p '' L.boundary ℝ = P.map '' (Rim ×ˢ {(0 : ℝ)}))
    (hnondisk : ¬ closure L.inside ⊆ interior A \ B) :
    ((s.map '' d) ∩ frontier E).Nonempty := by
  classical
  by_contra hn
  have havoid : Disjoint (s.map '' d) (frontier E) :=
    disjoint_left.mpr (fun x hx hf => hn ⟨x,hx,hf⟩)
  obtain ⟨gamma,hgamma,hnull⟩ :=
    P.center_rim_nullhomotopic_of_retained_disk_avoids_frontier s hE hd hdS b hqr havoid hband
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let H : A ≃ₜ ↥(S ∩ E) :=
    (Continuous.homeoOfEquivCompactToT2 (f := Equiv.Set.imageOfInjOn p A hpi)
      (hp.domRestrict.subtype_mk _)).trans (Homeomorph.setCongr hps)
  have hH (z : A) : (H z : X) = p z := rfl
  let inc : C(↥(S ∩ interior E),↥(S ∩ E)) :=
    ContinuousMap.inclusion (inter_subset_inter_right S interior_subset)
  have hv (y : ↥(S ∩ interior E)) : p (H.symm (inc y)) = (y : X) :=
    (hH (H.symm (inc y))).symm.trans (congrArg Subtype.val (H.apply_symm_apply (inc y)))
  have hnotB (y : ↥(S ∩ interior E)) : (H.symm (inc y) : P2) ∉ B := by
    intro hb
    have hf := (hproper _ (H.symm (inc y)).property).mpr hb
    rw [hv y] at hf
    exact hf.2 y.property.2
  let back : C(↥(S ∩ interior E),↥(A \ B)) :=
    ⟨fun y => ⟨H.symm (inc y), (H.symm (inc y)).property,hnotB y⟩,
      (continuous_subtype_val.comp (H.symm.continuous.comp inc.continuous)).subtype_mk _⟩
  have hback (y : ↥(S ∩ interior E)) : p (back y) = (y : X) := hv y
  let delta : C(Rim,↥(A \ B)) := back.comp gamma
  have hval (z : Rim) : p (delta z) = P.map (z,0) :=
    (hback (gamma z)).trans (hgamma z)
  have hdi : Function.Injective delta := by
    intro x y hxy
    have heq : P.map ((x : V2),0) = P.map ((y : V2),0) :=
      (hval x).symm.trans ((congrArg (fun z : ↥(A \ B) => p z) hxy).trans (hval y))
    have hh := P.injective ⟨sphere_subset_closedBall x.property,by norm_num⟩
      ⟨sphere_subset_closedBall y.property,by norm_num⟩ heq
    exact Subtype.ext (congrArg Prod.fst hh)
  have hds : range (fun z => (delta z : P2)) = L.boundary ℝ := by
    apply Subset.antisymm
    · rintro _ ⟨z,rfl⟩
      obtain ⟨w,hw,heq⟩ := hcenter.symm.subset
        (show P.map ((z : V2),0) ∈ P.map '' (Rim ×ˢ {(0 : ℝ)}) from
          ⟨((z : V2),0),⟨z.property,rfl⟩,rfl⟩)
      have hh := hpi (interior_subset (hLA hw)) (delta z).property.1 (heq.trans (hval z).symm)
      change (delta z : P2) ∈ L.boundary ℝ
      rw [←hh]
      exact hw
    · intro x hx
      obtain ⟨⟨z,t⟩,⟨hz,ht⟩,heq⟩ := hcenter.subset ⟨x,hx,rfl⟩
      have ht0 : t = 0 := ht
      subst t
      refine ⟨⟨z,hz⟩,?_⟩
      exact hpi (delta ⟨z,hz⟩).property.1 (interior_subset (hLA hx))
        ((hval ⟨z,hz⟩).trans heq)
  have hfill : closure L.inside ⊆ A \ B :=
    polygon_closed_inside_subset_of_nullhomotopic_rim L hL hLi delta hdi hds
      (hnull.comp_right back)
  apply hnondisk
  intro x hx
  refine ⟨?_,(hfill hx).2⟩
  rw [closure_eq_self_union_frontier,L.frontier_inside hL hLi] at hx
  rcases hx with hi | hb
  · exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset ((L.isOpen_inside hL hLi).mem_nhds hi)
        (fun y hy => (hfill (subset_closure hy)).1))
  · exact hLA hb

end PoincareConjecture.M76

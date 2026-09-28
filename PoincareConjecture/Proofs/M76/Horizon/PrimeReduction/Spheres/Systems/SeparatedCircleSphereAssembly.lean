import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MemberCircleCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleCollarRetainedDisks
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryDiskBoundary
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolyhedralPLCompatibleChart









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1



theorem ChartwisePLSphere.exists_cap_on_retained_disk
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x ∈ Q.source, ∃ i, x ∈ (e i).source)
    {d b r c q : Set V3}
    (hd : IsFinitePLBallPair P2 d r) (hb : IsFinitePLBallPair P2 b r)
    (hc : IsFinitePLBallPair P2 c q)
    (hunion : d ∪ b = Sphere) (hinter : d ∩ b = r)
    (hcQ : c ⊆ Q.target) (hcap : (Q.symm '' c) ∩ S = Q.symm '' q)
    (hrimage : s.map '' r = Q.symm '' q) :
    ∃ t : ChartwisePLSphere e ((s.map '' d) ∪ (Q.symm '' c)),
      EqOn t.map s.map d ∧ t.map '' b = Q.symm '' c := by
  have hdS : d ⊆ Sphere := subset_union_left.trans hunion.subset
  have hrS : r ⊆ Sphere := hd.1.trans hdS
  have hrQ : MapsTo s.map r Q.source := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hrimage.subset ⟨x,hx,rfl⟩
    exact hxy ▸ Q.map_target (hcQ (hc.1 hy))
  obtain ⟨n,P,hPi,hP,hPr⟩ := hd.exists_polygon_boundary
  let K := P.simplicialComplex hP
  have hK := P.finite_simplicialComplex_faces hP
  have hKr : K.space = r := (P.simplicialComplex_space hP).trans hPr
  have hmapPL := s.piecewiseAffine.restrict_finite K hK (hKr.subset.trans hrS)
  have hf : FinitePiecewiseAffineOn (Q ∘ s.map) r := by
    rw [←hKr]
    exact hmapPL.finitePiecewiseAffineOn_compatible_chart_finite_source K hK Q hQ
      (fun _ hx => hrQ (hKr.subset hx))
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hfi : InjOn (Q ∘ s.map) r := by
    intro x hx y hy hxy
    exact hsi (hrS hx) (hrS hy) (Q.injOn (hrQ hx) (hrQ hy) hxy)
  have himage : (Q ∘ s.map) '' r = q := by
    rw [image_comp,hrimage,image_image]
    exact (image_congr (fun x hx => Q.right_inv (hcQ (hc.1 hx)))).trans (image_id q)
  obtain ⟨er,her,herval⟩ := hf.exists_homeomorph_image hfi
  let er' : r ≃ₜ q := er.trans (Homeomorph.setCongr himage)
  have her' : er'.IsFinitePL := her.setCongr rfl himage
  have hermap (x : r) : s.map x = Q.symm (er' x) := by
    have hx : (er' x : V3) = Q (s.map x) := herval x
    rw [hx,Q.left_inv (hrQ x.property)]
  exact exists_raw_member_cap s he Q hQ hcover hd hb hc hunion hinter hcQ hcap
    er' her' hermap




theorem exists_separated_circle_spheres
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) (i : κ)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x ∈ Q.source, ∃ i, x ∈ (e i).source)
    (d r c q : Bool → Set V3)
    (hd : ∀ b, IsFinitePLBallPair P2 (d b) (r b))
    (hdS : ∀ b, d b ⊆ Sphere)
    (hb : ∀ b, IsFinitePLBallPair P2 (Sphere \ (d b \ r b)) (r b))
    (hddis : Disjoint (d true) (d false))
    (hc : ∀ b, IsFinitePLBallPair P2 (c b) (q b))
    (hcQ : ∀ b, c b ⊆ Q.target)
    (hcdis : Disjoint (c true) (c false))
    (hcap : ∀ b, (Q.symm '' c b) ∩ (⋃ j, S j) = Q.symm '' q b)
    (hrimage : ∀ b, (sS i).map '' r b = Q.symm '' q b) :
    ∃ t : ∀ b : Bool, ChartwisePLSphere e (((sS i).map '' d b) ∪ (Q.symm '' c b)),
      (∀ b, EqOn (t b).map (sS i).map (d b) ∧
        (t b).map '' (Sphere \ (d b \ r b)) = Q.symm '' c b) ∧
      Disjoint (((sS i).map '' d true) ∪ (Q.symm '' c true))
        (((sS i).map '' d false) ∪ (Q.symm '' c false)) ∧
      ∀ b j, j ≠ i →
        Disjoint (((sS i).map '' d b) ∪ (Q.symm '' c b)) (S j) := by
  classical
  have hmapS : MapsTo (sS i).map Sphere (S i) := by
    intro x hx
    rw [(sS i).map_eq ⟨x,hx⟩]
    exact ((sS i).parametrization ⟨x,hx⟩).property
  have hsi : InjOn (sS i).map Sphere := by
    intro x hx y hy hxy
    rw [(sS i).map_eq ⟨x,hx⟩,(sS i).map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val ((sS i).parametrization.injective (Subtype.ext hxy))
  have hrS (b : Bool) : Q.symm '' q b ⊆ S i := by
    rw [←hrimage b]
    rintro _ ⟨x,hx,rfl⟩
    exact hmapS (hdS b ((hd b).1 hx))
  have hcap' (b : Bool) : (Q.symm '' c b) ∩ S i = Q.symm '' q b := by
    apply Subset.antisymm
    · intro x hx
      exact (hcap b).subset ⟨hx.1,(subset_iUnion S i) hx.2⟩
    · intro x hx
      exact ⟨((hcap b).symm.subset hx).1,hrS b hx⟩
  have hunion (b : Bool) : d b ∪ (Sphere \ (d b \ r b)) = Sphere := by
    ext x
    have hd' := @hdS b x
    simp only [mem_union,mem_sdiff]
    tauto
  have hinter (b : Bool) : d b ∩ (Sphere \ (d b \ r b)) = r b := by
    ext x
    have hr' := @(hd b).1 x
    have hd' := @hdS b x
    simp only [mem_inter_iff,mem_sdiff]
    tauto
  choose t ht htb using fun b => (sS i).exists_cap_on_retained_disk he Q hQ hcover
    (hd b) (hb b) (hc b) (hunion b) (hinter b) (hcQ b) (hcap' b) (hrimage b)
  have hret : Disjoint ((sS i).map '' d true) ((sS i).map '' d false) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
    have huv := hsi (hdS true hu) (hdS false hv) (hux.trans hvx.symm)
    exact Set.disjoint_left.mp hddis hu (huv.symm ▸ hv)
  have hcapdis : Disjoint (Q.symm '' c true) (Q.symm '' c false) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
    have huv := Q.symm.injOn (hcQ true hu) (hcQ false hv) (hux.trans hvx.symm)
    exact Set.disjoint_left.mp hcdis hu (huv.symm ▸ hv)
  have hrret (b : Bool) : Q.symm '' q b ⊆ (sS i).map '' d b := by
    rw [←hrimage b]
    exact image_mono (hd b).1
  have hretS (b : Bool) : (sS i).map '' d b ⊆ S i := by
    rintro _ ⟨x,hx,rfl⟩
    exact hmapS (hdS b hx)
  refine ⟨t,fun b => ⟨ht b,htb b⟩,?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro x (hxt | hxc) (hxf | hxd)
    · exact Set.disjoint_left.mp hret hxt hxf
    · exact Set.disjoint_left.mp hret hxt
        (hrret false ((hcap' false).subset ⟨hxd,hretS true hxt⟩))
    · exact Set.disjoint_left.mp hret
        (hrret true ((hcap' true).subset ⟨hxc,hretS false hxf⟩)) hxf
    · exact Set.disjoint_left.mp hcapdis hxc hxd
  · intro b j hji
    apply Set.disjoint_left.mpr
    rintro x (hxd | hxc) hxj
    · exact Set.disjoint_left.mp (hdis hji.symm) (hretS b hxd) hxj
    · have hr := (hcap b).subset ⟨hxc,(subset_iUnion S j) hxj⟩
      exact Set.disjoint_left.mp (hdis hji.symm) (hrS b hr) hxj




theorem exists_separated_circle_spheres_of_collar
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j)) (i : κ)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x ∈ Q.source, ∃ i, x ∈ (e i).source)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space ⊆ Q.target)
    {β : ℝ} (hβ : 0 < β) (σ : P2 × ℝ → V3)
    (hσ : FinitePiecewiseAffineOn σ (Dehn.signedTubeDiamond ×ˢ Icc 0 β))
    (hσJ : MapsTo σ (Dehn.signedTubeDiamond ×ˢ Icc 0 β) J.space)
    (hσS : ∀ z ∈ Dehn.signedTubeDiamond ×ˢ Icc 0 β,
      z.1.2 = 0 → Q.symm (σ z) ∈ S i)
    (hfib : ∀ x ∈ Dehn.signedTubeDiamond ×ˢ Icc 0 β,
      ∀ y ∈ Dehn.signedTubeDiamond ×ˢ Icc 0 β,
      σ x = σ y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (x.2 = β ∧ y.2 = 0)))
    (c : Bool → Set V3)
    (hc : ∀ b, IsFinitePLBallPair P2 (c b)
      ((fun t => σ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β))
    (hcQ : ∀ b, c b ⊆ Q.target) (hcdis : Disjoint (c true) (c false))
    (hcap : ∀ b, (Q.symm '' c b) ∩ (⋃ j, S j) =
      Q.symm '' ((fun t => σ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β)) :
    ∃ (φ : P2 → V3) (k : Bool → Set V3),
      FinitePiecewiseAffineOn φ (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) ∧
      MapsTo φ (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) Sphere ∧
      (∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
        (sS i).map (φ z) = Q.symm (σ ((z.1,0),z.2))) ∧
      (∀ b,
        let r := (fun t : ℝ => φ (if b then 1/4 else -1/4,t)) '' Icc 0 β
        IsFinitePLBallPair P2 (k b) r ∧ k b ⊆ Sphere ∧
        IsFinitePLBallPair P2 (Sphere \ (k b \ r)) r ∧
        (sS i).map '' r = Q.symm ''
          ((fun t => σ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β)) ∧
      Disjoint (k true) (k false) ∧
      (∀ b, Disjoint (k b) ((fun t : ℝ => φ (0, t)) '' Icc 0 β)) ∧
      (k true ∪ k false) ∪ (φ '' (Icc (-1/4:ℝ) (1/4) ×ˢ Icc 0 β)) = Sphere ∧
      ∃ t : ∀ b : Bool, ChartwisePLSphere e (((sS i).map '' k b) ∪ (Q.symm '' c b)),
        (∀ b, EqOn (t b).map (sS i).map (k b) ∧
          (t b).map '' (Sphere \ (k b \
            ((fun t : ℝ => φ (if b then 1/4 else -1/4,t)) '' Icc 0 β))) = Q.symm '' c b) ∧
        Disjoint (((sS i).map '' k true) ∪ (Q.symm '' c true))
          (((sS i).map '' k false) ∪ (Q.symm '' c false)) ∧
        ∀ b j, j ≠ i →
          Disjoint (((sS i).map '' k b) ∪ (Q.symm '' c b)) (S j) := by
  obtain ⟨φ,k,hφ,hφS,hφval,hk,hkdis,hwhole⟩ :=
    (sS i).exists_circle_collar_retained_disks Q hQ J hJ hJQ hβ σ hσ hσJ hσS hfib
  let r : Bool → Set V3 := fun b =>
    (fun t : ℝ => φ (if b then 1/4 else -1/4,t)) '' Icc 0 β
  let q : Bool → Set V3 := fun b =>
    (fun t => σ ((if b then 1/4 else -1/4,0),t)) '' Icc 0 β
  have hrimage (b : Bool) : (sS i).map '' r b = Q.symm '' q b := by
    simpa only [r,q,image_image,Function.comp_def] using (hk b).2.2.2.2.2.1
  refine ⟨φ,k,hφ,hφS,hφval,?_,hkdis,fun b => (hk b).2.2.2.2.2.2.2,hwhole,?_⟩
  · exact fun b => ⟨(hk b).1,(hk b).2.1,(hk b).2.2.1,hrimage b⟩
  · exact exists_separated_circle_spheres S sS hdis i he Q hQ hcover k r c q
      (fun b => (hk b).1) (fun b => (hk b).2.1) (fun b => (hk b).2.2.1)
      hkdis hc hcQ hcdis hcap hrimage

end PoincareConjecture.M76

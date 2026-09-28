import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalRetainedDiskCap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalExteriorAnnulusDisks









set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Sphere" => sphere (0 : V3) 1
local notation "J" => Icc (-(1 / 2 : ℝ)) (1 / 2)

theorem exists_original_retained_end_cap
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d q : Set V3} (hd : IsFinitePLBallPair P2 d q) (hdS : d ⊆ Sphere)
    (hb : IsFinitePLBallPair P2 (Sphere \ (d \ q)) q)
    (hcontact : P.closedStrip ∩ S = P.map '' (Rim ×ˢ J))
    (a : Bool)
    (hrim : s.map '' q = P.map '' (Rim ×ˢ {if a then (1/2 : ℝ) else -(1/2)})) :
    ∃ t : ChartwisePLSphere e
      ((s.map '' d) ∪ (P.map '' (Disk ×ˢ {if a then (1/2 : ℝ) else -(1/2)}))),
      EqOn t.map s.map d ∧
      t.map '' (Sphere \ (d \ q)) =
        P.map '' (Disk ×ˢ {if a then (1/2 : ℝ) else -(1/2)}) := by
  let τ : ℝ := if a then 1/2 else -(1/2)
  have hτ : τ ∈ J := by cases a <;> norm_num [τ]
  let A : V2 →ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousAffineMap.id ℝ V2).prod (ContinuousAffineMap.const ℝ V2 τ)
  have hAval (x : V2) : A x = (x,τ) := rfl
  let p : V2 → X := P.map ∘ A
  have hfull (x : V2) (hx : x ∈ Disk) : A x ∈ Disk ×ˢ Icc (-1 : ℝ) 1 := by
    rw [hAval]
    exact ⟨hx,by linarith [hτ.1],by linarith [hτ.2]⟩
  have hcube := isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := hcube
  have hp : PolyhedralPLInCharts e p Disk := by
    rw [←hLs]
    exact P.polyhedral.comp_finitePiecewiseAffineOn L hL
      ⟨L,hL,rfl,L.affineOnFaces_affine A⟩
      (fun x hx => hfull x (hLs.subset hx))
  have hpi : InjOn p Disk := by
    intro x hx y hy hxy
    exact congrArg Prod.fst (P.injective (hfull x hx) (hfull y hy) hxy)
  have himage (Z : Set V2) : p '' Z = P.map '' (Z ×ˢ {τ}) := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(z,τ),⟨hz,rfl⟩,rfl⟩
    · rintro ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      change t = τ at ht
      subst t
      exact ⟨z,hz,rfl⟩
  have hcap : (p '' Disk) ∩ S = p '' Rim := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x,hx,rfl⟩,hxS⟩
      have hstrip : p x ∈ P.closedStrip := ⟨(x,τ),⟨hx,hτ⟩,rfl⟩
      obtain ⟨z,hz,hzx⟩ := hcontact.subset ⟨hstrip,hxS⟩
      have hzi : z ∈ Disk ×ˢ Icc (-1 : ℝ) 1 :=
        ⟨sphere_subset_closedBall hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
      have heq := P.injective hzi (hfull x hx) hzx
      have hxz : z.1 = x := congrArg Prod.fst heq
      exact ⟨x,hxz ▸ hz.1,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨⟨x,sphere_subset_closedBall hx,rfl⟩,
        (hcontact.symm.subset ⟨(x,τ),⟨hx,hτ⟩,rfl⟩).2⟩
  have hunion : d ∪ (Sphere \ (d \ q)) = Sphere := by
    ext x
    have h := @hdS x
    simp only [mem_union,mem_sdiff]
    tauto
  have hinter : d ∩ (Sphere \ (d \ q)) = q := by
    ext x
    have h := @hdS x
    have hq := @hd.1 x
    simp only [mem_inter_iff,mem_sdiff]
    tauto
  have hrimage : s.map '' q = p '' Rim := hrim.trans (himage Rim).symm
  obtain ⟨t,ht,htb⟩ := s.exists_original_cap_on_retained_disk hcompat hd hb
    (isFinitePLBallPair_unit_cube (ι := Fin 2)) hp hpi hunion hinter hcap hrimage
  change ∃ t : ChartwisePLSphere e ((s.map '' d) ∪ (P.map '' (Disk ×ˢ {τ}))),
    EqOn t.map s.map d ∧ t.map '' (Sphere \ (d \ q)) = P.map '' (Disk ×ˢ {τ})
  rw [←himage Disk]
  exact ⟨t,ht,htb⟩



theorem exists_original_exterior_retained_caps
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (B : Bool → Set X)
    (sB : ∀ a, ChartwisePLSphere e (B a))
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hK : IsClosed K) (hfront : frontier K = B false ∪ B true)
    (hstrip : P.closedStrip ∩ K = P.map '' (Rim ×ˢ J))
    (owner : Bool) (hband : P.map '' (Rim ×ˢ J) ⊆ B owner)
    (k q : Bool → Set V3)
    (hk : ∀ a, IsFinitePLBallPair P2 (k a) (q a) ∧ k a ⊆ Sphere ∧
      IsFinitePLBallPair P2 (Sphere \ (k a \ q a)) (q a) ∧
      (sB owner).map '' q a =
        P.map '' (Rim ×ˢ {if a then (1/2 : ℝ) else -(1/2)})) :
    ∃ t : ∀ a : Bool, ChartwisePLSphere e
      (((sB owner).map '' k a) ∪
        (P.map '' (Disk ×ˢ {if a then (1/2 : ℝ) else -(1/2)}))),
      ∀ a, EqOn (t a).map (sB owner).map (k a) ∧
        (t a).map '' (Sphere \ (k a \ q a)) =
          P.map '' (Disk ×ˢ {if a then (1/2 : ℝ) else -(1/2)}) := by
  have hBK : B owner ⊆ K := by
    apply (show B owner ⊆ frontier K from ?_).trans hK.frontier_subset
    rw [hfront]
    cases owner <;> simp
  have hcontact : P.closedStrip ∩ B owner = P.map '' (Rim ×ˢ J) := by
    apply Subset.antisymm
    · exact fun x hx => hstrip.subset ⟨hx.1,hBK hx.2⟩
    · exact fun x hx => ⟨(hstrip.symm.subset hx).1,hband hx⟩
  choose t ht using fun a => P.exists_original_retained_end_cap (sB owner) hcompat
    (hk a).1 (hk a).2.1 (hk a).2.2.1 hcontact a (hk a).2.2.2
  exact ⟨t,ht⟩

end PoincareConjecture.M76.OriginalDiskProduct

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedSphereDiskPortGluing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModel









set_option autoImplicit false
open Set Geometry Geometry.CubicalThreeSphere

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)

theorem HasPuncturedSphereModel.of_disk_glued_marked_models
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {κ : Bool → Type*} [∀ b, Finite (κ b)]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    (R : Bool → Set X) (hR : ∀ b, IsCompact (R b))
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f (R false ∪ R true))
    (a r : ∀ b, κ b → Set V4)
    (ha : ∀ b j, IsFinitePLBallPair V3 (a b j) (r b j))
    (haS : ∀ b j, a b j ⊆ sphere)
    (hopen : ∀ b j, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a b j \ r b j)))
    (hdis : ∀ b, Pairwise fun j k => Disjoint (a b j) (a b k)) (i : ∀ b, κ b)
    (M : Bool → Set E) (G : ∀ b, R b ≃ₜ M b)
    (hG : ∀ b (x : R b), (G b x : E) = f x)
    (C : ∀ b, M b ≃ₜ (sphere \ ⋃ j, a b j \ r b j : Set V4))
    (hC : ∀ b, (C b).IsFinitePL)
    {d q : Set X} (hqd : q ⊆ d)
    (hd : IsFinitePLBallPair (ℝ × ℝ) (f '' d) (f '' q))
    (hcontact : R false ∩ R true = d)
    (hport : ∀ b (x : R b), (x : X) ∈ d → (C b (G b x) : V4) ∈ r b (i b))
    (hout : ∀ b, ∃ x : R b, (C b (G b x) : V4) ∈ r b (i b) ∧ (x : X) ∉ d)
    (hfront :
      let s : Bool → Set X := fun b => (Subtype.val : R b → X) ''
        ((fun x : R b => (C b (G b x) : V4)) ⁻¹' r b (i b))
      frontier (R false ∪ R true) =
        ((s false \ (d \ q)) ∪ (s true \ (d \ q))) ∪
        ⋃ (b : Bool) (j : {j : κ b // j ≠ i b}),
          (Subtype.val : R b → X) '' ((fun x : R b => (C b (G b x) : V4)) ⁻¹' r b j)) :
    HasPuncturedSphereModel e f (R false ∪ R true) := by
  let J := (b : Bool) × {j : κ b // j ≠ i b}
  let sX : ∀ b, κ b → Set X := fun b j => (Subtype.val : R b → X) ''
    ((fun x : R b => (C b (G b x) : V4)) ⁻¹' r b j)
  let sE : ∀ b, κ b → Set E := fun b j => (Subtype.val : M b → E) ''
    ((fun x : M b => (C b x : V4)) ⁻¹' r b j)
  have hRU (b : Bool) : R b ⊆ R false ∪ R true := by
    cases b; exact subset_union_left; exact subset_union_right
  have hdR (b : Bool) : d ⊆ R b := by
    cases b
    · exact fun _ hx => (hcontact.symm.subset hx).1
    · exact fun _ hx => (hcontact.symm.subset hx).2
  have hGi (b : Bool) (y : M b) : f ((G b).symm y) = y := by
    rw [←hG b ((G b).symm y),(G b).apply_symm_apply]
  have hMR (b : Bool) : M b = f '' R b := by
    apply Subset.antisymm
    · intro y hy
      exact ⟨(G b).symm ⟨y,hy⟩,((G b).symm ⟨y,hy⟩).property,hGi b ⟨y,hy⟩⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact hG b ⟨x,hx⟩ ▸ (G b ⟨x,hx⟩).property
  have hMcontact : M false ∩ M true = f '' d := by
    rw [hMR false,hMR true,←image_inter_on
      (fun _ hx _ hy hxy => hfi (hRU true hx) (hRU false hy) hxy),hcontact]
  have hMport (b : Bool) (y : M b) (hy : (y : E) ∈ f '' d) :
      (C b y : V4) ∈ r b (i b) := by
    obtain ⟨z,hz,hzy⟩ := hy
    have hzx : z = ((G b).symm y : X) := hfi (hRU b (hdR b hz))
      (hRU b ((G b).symm y).property) (hzy.trans (hGi b y).symm)
    have h := hport b ((G b).symm y) (hzx ▸ hz)
    simpa only [(G b).apply_symm_apply] using h
  have hMout (b : Bool) : ∃ y : M b, (C b y : V4) ∈ r b (i b) ∧ (y : E) ∉ f '' d := by
    obtain ⟨x,hxr,hxd⟩ := hout b
    refine ⟨G b x,hxr,?_⟩
    rintro ⟨z,hz,hzx⟩
    have heq := hfi (hRU b (hdR b hz)) (hRU b x.property) (hzx.trans (hG b x))
    exact hxd (heq ▸ hz)
  obtain ⟨A,t,hAt,hAdis,H,hH,houter,hmark⟩ := Set.exists_physical_punctured_sphere_disk_port_gluing
    M a r ha haS hopen hdis i C hC hd hMcontact hMport hMout
  have hc (b : Bool) : ContinuousOn f (R b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h := continuous_subtype_val.comp (G b).continuous
    convert h using 1
    funext x
    exact (hG b x).symm
  have hcU := (hc false).union_of_isClosed (hc true) (hR false).isClosed (hR true).isClosed
  let : CompactSpace (R false ∪ R true : Set X) := isCompact_iff_compactSpace.mp ((hR false).union (hR true))
  let U₀ : (R false ∪ R true : Set X) ≃ (f '' (R false ∪ R true)) :=
    Equiv.Set.imageOfInjOn f _ hfi
  have hU₀ : Continuous U₀ := hcU.domRestrict.subtype_mk _
  let U₁ := hU₀.homeoOfEquivCompactToT2 (f := U₀)
  have htarget : f '' (R false ∪ R true) = M false ∪ M true := by rw [image_union,←hMR,←hMR]
  let U := U₁.trans (Homeomorph.setCongr htarget)
  have hUval (x : (R false ∪ R true : Set X)) : (U x : E) = f x := rfl
  have himage (D : Set X) (hDU : D ⊆ R false ∪ R true)
      (x : (R false ∪ R true : Set X)) : (U x : E) ∈ f '' D ↔ (x : X) ∈ D := by
    rw [hUval]
    constructor
    · rintro ⟨y,hy,hyx⟩
      exact hfi (hDU hy) x.property hyx ▸ hy
    · exact fun hx => ⟨x,hx,rfl⟩
  have hmodels (b : Bool) (j : κ b) (x : (R false ∪ R true : Set X)) :
      (x : X) ∈ sX b j ↔ (U x : E) ∈ sE b j := by
    constructor
    · rintro ⟨y,hy,hyx⟩
      refine ⟨G b y,hy,?_⟩
      rw [hG,hUval,hyx]
    · rintro ⟨y,hy,hyx⟩
      let z := (G b).symm y
      have hzx : (z : X) = x := hfi (hRU b z.property) x.property
        ((hGi b y).trans (hyx.trans (hUval x)))
      refine ⟨z,?_,hzx⟩
      change (C b (G b ((G b).symm y)) : V4) ∈ r b j
      rwa [(G b).apply_symm_apply]
  apply HasPuncturedSphereModel.of_marked_model A t
    (fun j => (hAt j).1) (fun j => (hAt j).2.1) hAdis (fun j => (hAt j).2.2)
    hf U hUval H hH
  intro x
  have hdx := himage d ((hdR false).trans (hRU false)) x
  have hqx := himage q (hqd.trans ((hdR false).trans (hRU false))) x
  have houterX : (x : X) ∈ (sX false (i false) \ (d \ q)) ∪ (sX true (i true) \ (d \ q)) ↔
      (H (U x) : V4) ∈ t none := by
    rw [←houter (U x)]
    change ((x : X) ∈ sX false (i false) ∧ ¬ ((x : X) ∈ d ∧ (x : X) ∉ q)) ∨
      ((x : X) ∈ sX true (i true) ∧ ¬ ((x : X) ∈ d ∧ (x : X) ∉ q)) ↔ _
    rw [hmodels false (i false) x,hmodels true (i true) x,←hdx,←hqx]
    rfl
  change (x : X) ∈ frontier (R false ∪ R true) ↔ _
  rw [hfront]
  constructor
  · rintro (hx | hx)
    · exact mem_iUnion.mpr ⟨none,houterX.mp hx⟩
    · obtain ⟨b,hb⟩ := mem_iUnion.mp hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp hb
      exact mem_iUnion.mpr ⟨some ⟨b,j⟩,(hmark ⟨b,j⟩ (U x)).mp ((hmodels b j x).mp hj)⟩
  · intro hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    cases j with
    | none => exact Or.inl (houterX.mpr hj)
    | some j =>
      exact Or.inr (mem_iUnion.mpr ⟨j.1,mem_iUnion.mpr ⟨j.2,
        (hmodels j.1 j.2 x).mpr ((hmark j (U x)).mpr hj)⟩⟩)

end PoincareConjecture.M76

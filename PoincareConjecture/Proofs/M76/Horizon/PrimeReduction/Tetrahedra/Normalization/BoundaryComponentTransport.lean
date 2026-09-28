import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.CarrierComponentTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalCarrierComponentTransport
import Mathlib.Data.Set.Card

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem ncard_image_eq_of_same_fibers
    {ρ α β : Type*} (U : Set ρ) (old : ρ → α) (new : ρ → β)
    (hfib : ∀ i ∈ U, ∀ j ∈ U, old i = old j ↔ new i = new j) :
    (old '' U).ncard = (new '' U).ncard := by
  classical
  let F : ∀ a ∈ old '' U, β := fun a ha => new (Classical.choose ha)
  have hF (a : α) (ha : a ∈ old '' U) : F a ha ∈ new '' U :=
    mem_image_of_mem new (Classical.choose_spec ha).1
  apply ncard_congr F hF
  · intro a b ha hb hab
    have heq := (hfib _ (Classical.choose_spec ha).1 _ (Classical.choose_spec hb).1).mpr hab
    exact (Classical.choose_spec ha).2.symm.trans (heq.trans (Classical.choose_spec hb).2)
  · rintro _ ⟨i,hi,rfl⟩
    let ha : old i ∈ old '' U := mem_image_of_mem old hi
    refine ⟨old i,ha,?_⟩
    exact (hfib _ (Classical.choose_spec ha).1 i hi).mp (Classical.choose_spec ha).2

theorem boundary_component_label_ncard_eq
    {X ρ η : Type*} [TopologicalSpace X]
    (A B : η → Set X) (G : ∀ k, A k ≃ₜ B k)
    (side : ρ → η) (point : ρ → X)
    (hpoint : ∀ i, point i ∈ A (side i))
    (hfix : ∀ i, (G (side i) ⟨point i,hpoint i⟩ : X) = point i)
    (selected : Set η) :
    ((fun i => (side i,connectedComponentIn (A (side i)) (point i))) ''
      {i | side i ∈ selected}).ncard =
    ((fun i => (side i,connectedComponentIn (B (side i)) (point i))) ''
      {i | side i ∈ selected}).ncard := by
  classical
  let f : η → X → X := fun k x => if hx : x ∈ A k then (G k ⟨x,hx⟩ : X) else x
  have hfval (k : η) (x : A k) : f k x = (G k x : X) := by
    simp only [f,dif_pos x.property]
  have hfi (k : η) : InjOn (f k) (A k) := by
    intro x hx y hy hxy
    have heq : G k ⟨x,hx⟩ = G k ⟨y,hy⟩ := Subtype.ext
      ((hfval k ⟨x,hx⟩).symm.trans (hxy.trans (hfval k ⟨y,hy⟩)))
    exact congrArg Subtype.val ((G k).injective heq)
  have hfull (k : η) : f k '' A k = B k := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [hfval k ⟨x,hx⟩]
      exact (G k ⟨x,hx⟩).property
    · intro y hy
      refine ⟨(G k).symm ⟨y,hy⟩,((G k).symm ⟨y,hy⟩).property,?_⟩
      rw [hfval,(G k).apply_symm_apply]
  have hcomponent (i : ρ) :
      f (side i) '' connectedComponentIn (A (side i)) (point i) =
        connectedComponentIn (B (side i)) (point i) := by
    have h := (G (side i)).image_connectedComponentIn_of_values (hfval (side i))
      subset_rfl (hpoint i)
    rwa [hfull,hfval (side i) ⟨point i,hpoint i⟩,hfix i] at h
  apply ncard_image_eq_of_same_fibers
  intro i _ j _
  constructor
  · intro hij
    have hs := congrArg Prod.fst hij
    have hc := congrArg Prod.snd hij
    dsimp only at hs hc
    have hj := hcomponent j
    rw [←hs] at hc hj
    apply Prod.ext hs
    have hcc := (hcomponent i).symm.trans ((congrArg (fun C => f (side i) '' C) hc).trans hj)
    simpa only [hs] using hcc
  · intro hij
    have hs := congrArg Prod.fst hij
    have hc := congrArg Prod.snd hij
    dsimp only at hs hc
    have hj := hcomponent j
    rw [←hs] at hc hj
    apply Prod.ext hs
    have heq := (hcomponent i).trans (hc.trans hj.symm)
    have hcc := ((hfi (side i)).image_eq_image_iff
      (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)).mp heq
    simpa only [hs] using hcc

theorem boundary_component_label_ncard_eq_of_section_values
    {X ρ η : Type*} [TopologicalSpace X]
    (A B : η → Set X) {T : Set X}
    (G : ∀ k, (A k ∩ T : Set X) ≃ₜ (B k ∩ T : Set X))
    (f : η → X → X)
    (hval : ∀ k (x : (A k ∩ T : Set X)), (G k x : X) = f k x)
    (side : ρ → η) (point : ρ → X)
    (hpoint : ∀ i, point i ∈ A (side i) ∩ T)
    (hfix : ∀ i, f (side i) (point i) = point i) (selected : Set η) :
    ((fun i => (side i,connectedComponentIn (A (side i) ∩ T) (point i))) ''
      {i | side i ∈ selected}).ncard =
    ((fun i => (side i,connectedComponentIn (B (side i) ∩ T) (point i))) ''
      {i | side i ∈ selected}).ncard :=
  boundary_component_label_ncard_eq (fun k => A k ∩ T) (fun k => B k ∩ T) G side point
    hpoint (fun i => (hval _ _).trans (hfix i)) selected

theorem boundary_component_label_ncard_eq_of_realization
    {X Y ρ η : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {K : Set X} {L : Set Y} (H : K ≃ₜ L) (f : X → Y)
    (hval : ∀ x : K, f x = (H x : Y))
    (A : η → Set X) (hAK : ∀ k, A k ⊆ K)
    (side : ρ → η) (point : ρ → X) (hpoint : ∀ i, point i ∈ A (side i))
    (selected : Set η) :
    ((fun i => (side i,connectedComponentIn (A (side i)) (point i))) ''
      {i | side i ∈ selected}).ncard =
    ((fun i => (side i,connectedComponentIn (f '' A (side i)) (f (point i)))) ''
      {i | side i ∈ selected}).ncard := by
  have hfi : InjOn f K := by
    intro x hx y hy hxy
    have heq : H ⟨x,hx⟩ = H ⟨y,hy⟩ := Subtype.ext
      ((hval ⟨x,hx⟩).symm.trans (hxy.trans (hval ⟨y,hy⟩)))
    exact congrArg Subtype.val (H.injective heq)
  let label := fun i => (side i,connectedComponentIn (A (side i)) (point i))
  let transport : η × Set X → η × Set Y := fun z => (z.1,f '' z.2)
  have hinj : InjOn transport (label '' {i | side i ∈ selected}) := by
    rintro _ ⟨i,hi,rfl⟩ _ ⟨j,hj,rfl⟩ hij
    have hs := congrArg Prod.fst hij
    have hc := congrArg Prod.snd hij
    change side i = side j at hs
    change (side i,connectedComponentIn (A (side i)) (point i)) =
      (side j,connectedComponentIn (A (side j)) (point j))
    apply Prod.ext hs
    exact (hfi.image_eq_image_iff ((connectedComponentIn_subset _ _).trans (hAK _))
      ((connectedComponentIn_subset _ _).trans (hAK _))).mp hc
  have himage : transport '' (label '' {i | side i ∈ selected}) =
      (fun i => (side i,connectedComponentIn (f '' A (side i)) (f (point i)))) ''
        {i | side i ∈ selected} := by
    rw [←image_comp]
    apply image_congr
    intro i _
    exact Prod.ext rfl (H.image_connectedComponentIn_of_values hval (hAK _) (hpoint i))
  exact hinj.ncard_image.symm.trans (congrArg Set.ncard himage)

theorem boundary_component_label_ncard_eq_in_original_realization
    {X E ι ρ η : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : Geometry.PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (A B : η → Set E) (hAK : ∀ k, A k ⊆ K.space) (hBK : ∀ k, B k ⊆ K.space)
    (G : ∀ k, A k ≃ₜ B k) (side : ρ → η) (point : ρ → X)
    (hpoint : ∀ i, point i ∈ g '' A (side i))
    (hfix : ∀ i (x : A (side i)), g x = point i → (G (side i) x : E) = x)
    (selected : Set η) :
    ((fun i => (side i,connectedComponentIn (g '' A (side i)) (point i))) ''
      {i | side i ∈ selected}).ncard =
    ((fun i => (side i,connectedComponentIn (g '' B (side i)) (point i))) ''
      {i | side i ∈ selected}).ncard := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let J := hg.continuousOn.domRestrict.isClosedEmbedding
    (fun x y h => Subtype.ext (hgi x.property y.property h)) |>.isEmbedding.toHomeomorph
  let pr : K.space ≃ₜ (g '' K.space) :=
    J.trans (Homeomorph.setCongr (image_eq_range g K.space).symm)
  have hpr (x : K.space) : g x = (pr x : X) := rfl
  choose p hp hpval using hpoint
  have hfixed (i : ρ) : (G (side i) ⟨p i,hp i⟩ : E) = p i :=
    hfix i ⟨p i,hp i⟩ (hpval i)
  have hpB (i : ρ) : p i ∈ B (side i) := by
    rw [←hfixed i]
    exact (G (side i) ⟨p i,hp i⟩).property
  have hraw := boundary_component_label_ncard_eq_of_realization pr g hpr A hAK side p hp selected
  have hsep := boundary_component_label_ncard_eq_of_realization pr g hpr B hBK side p hpB selected
  have hcount := boundary_component_label_ncard_eq A B G side p hp hfixed selected
  have heq := hraw.symm.trans (hcount.trans hsep)
  simpa only [hpval] using heq

theorem boundary_component_label_ncard_eq_of_original_section_support
    {X E ι ρ η : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : Geometry.PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (A B : η → Set E) (hAK : ∀ k, A k ⊆ K.space) (hBK : ∀ k, B k ⊆ K.space)
    {T : Set E} (hTK : T ⊆ K.space)
    (G : ∀ k, (A k ∩ T : Set E) ≃ₜ (B k ∩ T : Set E)) (f : η → E → E)
    (hval : ∀ k (x : (A k ∩ T : Set E)), (G k x : E) = f k x)
    (hsupport : ∀ k, EqOn (f k) id (A k \ g ⁻¹' interior (g '' T)))
    (side : ρ → η) (point : ρ → X)
    (hpoint : ∀ i, point i ∈ (g '' A (side i)) ∩ (g '' T))
    (hboundary : ∀ i, point i ∉ interior (g '' T)) (selected : Set η) :
    ((fun i => (side i,connectedComponentIn ((g '' A (side i)) ∩ (g '' T)) (point i))) ''
      {i | side i ∈ selected}).ncard =
    ((fun i => (side i,connectedComponentIn ((g '' B (side i)) ∩ (g '' T)) (point i))) ''
      {i | side i ∈ selected}).ncard := by
  have hinter (W : Set E) (hWK : W ⊆ K.space) :
      g '' (W ∩ T) = (g '' W) ∩ (g '' T) :=
    image_inter_on (fun x hx y hy hxy => hgi (hTK hx) (hWK hy) hxy)
  have hfix (i : ρ) (x : (A (side i) ∩ T : Set E)) (hx : g x = point i) :
      (G (side i) x : E) = x := by
    rw [hval]
    apply hsupport (side i)
    exact ⟨x.property.1,fun hn => hboundary i (hx ▸ hn)⟩
  have hout := boundary_component_label_ncard_eq_in_original_realization K hK hg hgi
    (fun k => A k ∩ T) (fun k => B k ∩ T)
    (fun k => inter_subset_left.trans (hAK k)) (fun k => inter_subset_left.trans (hBK k))
    G side point (fun i => (hinter _ (hAK _)).symm.subset (hpoint i)) hfix selected
  simpa only [hinter _ (hAK _),hinter _ (hBK _)] using hout

end PoincareConjecture.M76

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismFiberMidpoint

set_option autoImplicit false
noncomputable section
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

def prismFiberPoint {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) (t : I) : B :=
  H ⟨((H.symm x : E × ℝ).1,t),(H.symm x).property.1,t.property⟩

def prismFiberEndPair {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) : Set E :=
  {(prismFiberPoint H x 0 : E),(prismFiberPoint H x 1 : E)}

def prismTrimFiberEndPair {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) : Set E :=
  {(prismFiberPoint H x (trimInterval 0) : E),(prismFiberPoint H x (trimInterval 1) : E)}

theorem prismFiberPoint_midpoint {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) (t : I) :
    prismFiberPoint H (prismFiberMidpoint H x) t = prismFiberPoint H x t := by
  simp only [prismFiberPoint,prismFiberMidpoint,H.symm_apply_apply]

theorem prismFiberPoint_on_global_rectangle
    {E : Type*} [TopologicalSpace E] {A B M : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (u s t : I) :
    (prismFiberPoint H ⟨G ⟨(u,s),u.property,s.property⟩,hMB (G _).property⟩ t : E) =
      G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩ := by
  have h0 := prism_inverse_on_global_rectangle H G hMB flip hformula u s
  have h1 := hformula u t
  apply congrArg (fun x : B => (x : E)) (a₂ :=
    ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,hMB (G _).property⟩)
  apply H.symm.injective
  apply Subtype.ext
  simp only [prismFiberPoint,H.symm_apply_apply,h0,h1]

theorem prismTrimFiberEndPair_on_global_rectangle
    {E : Type*} [TopologicalSpace E] {A B M : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (u t : I) :
    prismTrimFiberEndPair H ⟨G ⟨(u,t),u.property,t.property⟩,hMB (G _).property⟩ =
      {(G ⟨(u,trimInterval 0),u.property,(trimInterval 0).property⟩ : E),
        (G ⟨(u,trimInterval 1),u.property,(trimInterval 1).property⟩ : E)} := by
  rw [prismTrimFiberEndPair,prismFiberPoint_on_global_rectangle H G hMB flip hformula,
    prismFiberPoint_on_global_rectangle H G hMB flip hformula]
  cases flip
  · rfl
  · have h0 : fiberFlip true (trimInterval 0) = trimInterval 1 := by
      apply Subtype.ext
      change 1-(1/4+(0 : ℝ)/2) = 1/4+1/2
      norm_num
    have h1 : fiberFlip true (trimInterval 1) = trimInterval 0 := by
      apply Subtype.ext
      change 1-(1/4+(1 : ℝ)/2) = 1/4+0/2
      norm_num
    rw [h0,h1]
    exact pair_comm _ _

theorem prismFiberPoint_trim_chart
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim H)
    (hC : ∀ x, (C x : E) = H (trimProduct A x)) (x : prismTrim H) (t : I) :
    (prismFiberPoint C x t : E) =
      prismFiberPoint H ⟨x,prismTrim_subset H x.property⟩ (trimInterval t) := by
  let y := C.symm x
  have hx : (x : E) = H (trimProduct A y) := by
    simpa only [y,C.apply_symm_apply] using hC y
  have hsource : H.symm ⟨x,prismTrim_subset H x.property⟩ = trimProduct A y := by
    apply H.injective
    exact (H.apply_symm_apply _).trans (Subtype.ext hx)
  change (C ⟨((y : E × ℝ).1,t),y.property.1,t.property⟩ : E) = _
  rw [hC]
  unfold prismFiberPoint
  apply congrArg (fun z => (H z : E))
  apply Subtype.ext
  apply Prod.ext
  · exact (congrArg (fun z : (A ×ˢ I : Set (E × ℝ)) => (z : E × ℝ).1) hsource).symm
  · rfl

theorem prismFiberEndPair_trim_chart
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim H)
    (hC : ∀ x, (C x : E) = H (trimProduct A x)) (x : prismTrim H) :
    prismFiberEndPair C x = prismTrimFiberEndPair H ⟨x,prismTrim_subset H x.property⟩ := by
  simp only [prismFiberEndPair,prismTrimFiberEndPair,prismFiberPoint_trim_chart H C hC]

theorem prismTrimFiberEndPair_on_affine_side
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B M : Set E} (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (G : Square ≃ₜ M)
    (hMB : M ⊆ B) (flip b : Bool)
    (hformula : ∀ (u t : I),
      (H.symm ⟨G ⟨(u,fiberFlip flip t),u.property,(fiberFlip flip t).property⟩,
        hMB (G _).property⟩ : E × ℝ) =
        ((G ⟨(u,fiberFlip flip 0),u.property,(fiberFlip flip 0).property⟩ : E),(t : ℝ)))
    (hside : ∀ t, (G (sidePoint b t) : E) =
      AffineMap.lineMap (G (sidePoint b 0) : E) (G (sidePoint b 1) : E) (t : ℝ))
    (t : I) :
    prismTrimFiberEndPair H ⟨G (sidePoint b t),hMB (G _).property⟩ =
      {AffineMap.lineMap (G (sidePoint b 0) : E) (G (sidePoint b 1) : E) (1/4 : ℝ),
        AffineMap.lineMap (G (sidePoint b 0) : E) (G (sidePoint b 1) : E) (3/4 : ℝ)} := by
  have he : prismTrimFiberEndPair H ⟨G (sidePoint b t),hMB (G _).property⟩ =
      {(G (sidePoint b (trimInterval 0)) : E),(G (sidePoint b (trimInterval 1)) : E)} := by
    cases b
    · exact prismTrimFiberEndPair_on_global_rectangle H G hMB flip hformula 0 t
    · exact prismTrimFiberEndPair_on_global_rectangle H G hMB flip hformula 1 t
  rw [he,hside (trimInterval 0),hside (trimInterval 1)]
  norm_num [trimInterval]

theorem quarter_pair_eq_of_endpoint_pair_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c d : E} (h : ({a,b} : Set E) = {c,d}) :
    ({AffineMap.lineMap a b (1/4 : ℝ),AffineMap.lineMap a b (3/4 : ℝ)} : Set E) =
      {AffineMap.lineMap c d (1/4 : ℝ),AffineMap.lineMap c d (3/4 : ℝ)} := by
  rcases pair_eq_pair_iff.mp h with ⟨hac,hbd⟩ | ⟨had,hbc⟩
  · rw [hac,hbd]
  · rw [had,hbc]
    have h0 : AffineMap.lineMap d c (1/4 : ℝ) = AffineMap.lineMap c d (3/4 : ℝ) := by
      simp only [AffineMap.lineMap_apply_module]
      module
    have h1 : AffineMap.lineMap d c (3/4 : ℝ) = AffineMap.lineMap c d (1/4 : ℝ) := by
      simp only [AffineMap.lineMap_apply_module]
      module
    rw [h0,h1,pair_comm]

end PoincareConjecture.M76.PrismBelt

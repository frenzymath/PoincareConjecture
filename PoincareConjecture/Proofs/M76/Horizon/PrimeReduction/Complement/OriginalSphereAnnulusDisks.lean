import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereAnnulusParameter








set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "Annulus" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

theorem ChartwisePLSphere.exists_original_annulus_disks
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f Annulus)
    (hfi : InjOn f Annulus) (hfS : MapsTo f Annulus S)
    (p : S) (hp : (p : X) ∉ f '' Annulus) :
    ∃ (g : P2 → V3) (k q : Bool → Set V3) (C : Bool → Set (V3 × ℝ)),
      FinitePiecewiseAffineOn g Annulus ∧ MapsTo g Annulus Sphere ∧
      (∀ z ∈ Annulus, s.map (g z) = f z) ∧
      s.map '' (g '' Annulus) = f '' Annulus ∧
      (∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧ k b ⊆ Sphere ∧
        k b ∩ (g '' Annulus) = q b ∧
        s.map '' q b = (fun z : Annulus => f z) ''
          {z | depth 8 z = if b then 1 else -1} ∧
        (s.map '' k b) ∩ (f '' Annulus) = s.map '' q b) ∧
      Disjoint (s.map '' k true) (s.map '' k false) ∧
      ((s.map '' k true) ∪ (s.map '' k false)) ∪ (f '' Annulus) = S ∧
      ∀ b,
        let A := Sphere \ (k b \ q b)
        IsFinitePLBallPair P2 A (q b) ∧ k (!b) ∪ (g '' Annulus) = A ∧
        IsFinitePLBallPair P2 (C b) (q b ×ˢ {(1 : ℝ)}) ∧
        IsFinitePLBallPair P2 (k (!b) ×ˢ {(1 : ℝ)}) (q (!b) ×ˢ {(1 : ℝ)}) ∧
        IsFinitePLBallPair P3 (A ×ˢ I)
          (((g '' Annulus) ×ˢ {(1 : ℝ)}) ∪ (C b ∪ (k (!b) ×ˢ {(1 : ℝ)}))) ∧
        C b ∩ ((g '' Annulus) ×ˢ {(1 : ℝ)}) = q b ×ˢ {(1 : ℝ)} ∧
        (k (!b) ×ˢ {(1 : ℝ)}) ∩ ((g '' Annulus) ×ˢ {(1 : ℝ)}) =
          q (!b) ×ˢ {(1 : ℝ)} ∧
        Disjoint (k (!b) ×ˢ {(1 : ℝ)}) (C b) := by
  obtain ⟨g,c,hg,hc,hcval,hgS,hvalue,himage⟩ :=
    s.exists_finitePL_annulus_parameter hcompat f hf hfi hfS
  let p0 := s.parametrization.symm p
  have hp0 : (p0 : V3) ∉ g '' Annulus := by
    intro h
    have hmem := himage.subset (mem_image_of_mem s.map h)
    rw [s.map_eq p0,s.parametrization.apply_symm_apply] at hmem
    exact hp hmem
  have hband : g '' Annulus ⊆ Sphere := by rintro _ ⟨x,hx,rfl⟩; exact hgS hx
  obtain ⟨k,q,C,hq,hk,hdis,hcover,hprod⟩ :=
    exists_sphere_annulus_product_balls c hc hband p0 hp0
  have hs : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hsimage : s.map '' Sphere = S := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [s.map_eq ⟨x,hx⟩]
      exact (s.parametrization ⟨x,hx⟩).property
    · intro x hx
      exact ⟨s.parametrization.symm ⟨x,hx⟩,(s.parametrization.symm ⟨x,hx⟩).property,
        (s.map_eq _).trans (congrArg Subtype.val (s.parametrization.apply_symm_apply _))⟩
  refine ⟨g,k,q,C,hg,hgS,hvalue,himage,?_,?_,?_,?_⟩
  · intro b
    refine ⟨(hk b).1,(hk b).2.1,(hk b).2.2,?_,?_⟩
    · rw [hq b,image_image]
      apply image_congr
      intro z _
      rw [hcval z]
      exact hvalue z z.property
    · rw [← himage,← hs.image_inter (hk b).2.1 hband,(hk b).2.2]
  · apply disjoint_left.mpr
    rintro x ⟨a,ha,rfl⟩ ⟨b,hb,hab⟩
    exact disjoint_left.mp hdis ha
      (hs ((hk false).2.1 hb) ((hk true).2.1 ha) hab ▸ hb)
  · rw [← himage,← image_union,← image_union,hcover,hsimage]
  · intro b
    obtain ⟨hA,hAeq,_,hC,hcap,hball,hmeet,hcapmeet,hcapdis⟩ := hprod b
    exact ⟨hA,hAeq,hC,hcap,hball,hmeet,hcapmeet,hcapdis⟩

end PoincareConjecture.M76

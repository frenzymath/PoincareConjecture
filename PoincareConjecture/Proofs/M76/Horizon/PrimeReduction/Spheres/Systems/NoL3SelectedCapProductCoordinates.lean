import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalCollarSphereCoordinates









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "Sphere" => sphere (0 : V3) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem ChartwisePLSphere.exists_original_centered_product_coordinates
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (N.space ×ˢ I)) (hci : InjOn c (N.space ×ˢ I))
    (hzero : c '' (N.space ×ˢ {(0 : ℝ)}) = S) :
    ∃ F : V3 × ℝ → X,
      PolyhedralPLInCharts e F (Sphere ×ˢ I) ∧ InjOn F (Sphere ×ˢ I) ∧
      (∀ x ∈ Sphere, F (x,0) = s.map x) ∧
      ∀ A : Set ℝ, F '' (Sphere ×ˢ A) = c '' (N.space ×ˢ A) := by
  classical
  let a : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have ha : FinitePiecewiseAffineOn a N.space :=
    ⟨N,hN,rfl,N.affineOnFaces_affine a⟩
  have hs : PolyhedralPLInCharts e (fun x => c (x,0)) N.space :=
    hc.comp_finitePiecewiseAffineOn N hN ha (fun x hx => ⟨hx,by norm_num⟩)
  have hsi : InjOn (fun x => c (x,0)) N.space := by
    intro x hx y hy hxy
    exact congrArg Prod.fst (hci ⟨hx,by norm_num⟩ ⟨hy,by norm_num⟩ hxy)
  have hsimage : (fun x => c (x,0)) '' N.space = S := by
    rw [←hzero]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨(y,0),⟨hy,rfl⟩,rfl⟩
    · rintro ⟨⟨y,t⟩,⟨hy,ht⟩,hval⟩
      exact ⟨y,hy,by simpa only [show t = 0 from ht] using hval⟩
  let : CompactSpace N.space := isCompact_iff_compactSpace.mp (N.isCompact_space_of_finite hN)
  let H0 : N.space ≃ₜ ((fun x => c (x,0)) '' N.space) :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn (fun x => c (x,0)) N.space hsi)
      (hs.continuousOn.domRestrict.subtype_mk _)
  let H := H0.trans (Homeomorph.setCongr hsimage)
  have hHval (x : N.space) : (H x : X) = c ((x : E),0) := rfl
  let q : V3 → E := fun x =>
    if hx : x ∈ Sphere then H.symm (s.parametrization ⟨x,hx⟩) else 0
  have hqval (x : Sphere) : q x = (H.symm (s.parametrization x) : E) := by
    simp only [q,dif_pos x.property]
  have hqN : MapsTo q Sphere N.space := by
    intro x hx
    rw [hqval ⟨x,hx⟩]
    exact (H.symm (s.parametrization ⟨x,hx⟩)).property
  have hqcont : ContinuousOn q Sphere := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp (H.symm.continuous.comp s.parametrization.continuous) using 1
    funext x
    exact hqval x
  have hqzero (x : V3) (hx : x ∈ Sphere) : c (q x,0) = s.map x := by
    rw [hqval ⟨x,hx⟩,←hHval,H.apply_symm_apply,s.map_eq ⟨x,hx⟩]
  obtain ⟨L,hL,hLS⟩ := exists_finite_unitCubeSphere (ι := Fin 3)
  have hq : FinitePiecewiseAffineOn q Sphere := by
    have hcomp : PolyhedralPLInCharts e ((fun x => c (x,0)) ∘ q) Sphere :=
      s.piecewiseAffine.congr (fun x hx => (hqzero x hx).symm)
    exact hLS ▸ hs.finitePiecewiseAffineOn_lift hcompat hsi L hL
      (hqcont.mono hLS.subset) (fun x hx => hqN (hLS.subset hx)) (hLS.symm ▸ hcomp)
  have hqi : InjOn q Sphere := by
    intro x hx y hy hxy
    rw [hqval ⟨x,hx⟩,hqval ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (H.symm.injective (Subtype.ext hxy)))
  have hqonto : q '' Sphere = N.space := by
    apply Subset.antisymm (by rintro _ ⟨x,hx,rfl⟩; exact hqN hx)
    intro y hy
    let x := s.parametrization.symm (H ⟨y,hy⟩)
    refine ⟨x,x.property,?_⟩
    rw [hqval x,s.parametrization.apply_symm_apply,H.symm_apply_apply]
  obtain ⟨_,_,_,_,_,_,⟨_,⟨J,hJ,hJs,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) I :=
    ⟨J,hJ,hJs,J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  let F := c ∘ Prod.map q id
  have hF : PolyhedralPLInCharts e F (Sphere ×ˢ I) := by
    obtain ⟨M,hM,hMs,hfaces⟩ := hq.prodMap hid
    rw [←hMs]
    exact hc.comp_finitePiecewiseAffineOn M hM ⟨M,hM,rfl,hfaces⟩
      (fun z hz => ⟨hqN (hMs.subset hz).1,(hMs.subset hz).2⟩)
  refine ⟨F,hF,?_,hqzero,?_⟩
  · intro z hz w hw hzw
    have h := hci ⟨hqN hz.1,hz.2⟩ ⟨hqN hw.1,hw.2⟩ hzw
    exact Prod.ext (hqi hz.1 hw.1 (congrArg Prod.fst h)) (congrArg (fun p : E × ℝ => p.2) h)
  · intro A
    change (c ∘ Prod.map q id) '' (Sphere ×ˢ A) = _
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(q z.1,z.2),⟨hqN hz.1,hz.2⟩,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨y,hy,hyq⟩ := hqonto.symm.subset hz.1
      exact ⟨(y,z.2),⟨hy,hz.2⟩,by change c (q y,z.2) = c z; rw [hyq]⟩

end PoincareConjecture.M76

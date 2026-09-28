import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MemberCircleCaps
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLInverse

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1

private theorem exists_original_cap_with_rim_map
    {X ι E M : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d b r : Set V3} {c q : Set E} {p : E → X}
    (hd : IsFinitePLBallPair P2 d r) (hb : IsFinitePLBallPair P2 b r)
    (hc : IsFinitePLBallPair M c q)
    (hp : PolyhedralPLInCharts e p c) (hpi : InjOn p c)
    (hunion : d ∪ b = Sphere) (hinter : d ∩ b = r)
    (hcap : (p '' c) ∩ S = p '' q)
    (er : r ≃ₜ q) (her : er.IsFinitePL)
    (hermap : ∀ x : r, s.map x = p (er x)) :
    ∃ t : ChartwisePLSphere e ((s.map '' d) ∪ (p '' c)),
      EqOn t.map s.map d ∧ t.map '' b = p '' c := by
  classical
  obtain ⟨H, hH, hHr, hHmem⟩ := hb.exists_extension hc er her
  obtain ⟨f, hf, hHf⟩ := hH
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨D, hD, hDs, _⟩, _⟩, _⟩ := hd
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨B, hB, hBs, _⟩, _⟩, _⟩ := hb
  have hdS : d ⊆ Sphere := subset_union_left.trans hunion.subset
  have hbS : b ⊆ Sphere := subset_union_right.trans hunion.subset
  have hmapf (x : V3) (hx : x ∈ b) : f x ∈ c := by
    rw [← hHf ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hcapPL : PolyhedralPLInCharts e (p ∘ f) B.space := by
    exact hp.comp_finitePiecewiseAffineOn B hB (hBs.symm ▸ hf)
      (fun x hx => hmapf x (hBs.subset hx))
  have hagree (x : V3) (hxd : x ∈ d) (hxb : x ∈ b) : s.map x = p (f x) := by
    have hxr : x ∈ r := hinter.subset ⟨hxd, hxb⟩
    have hval := congrArg (fun y : c => (y : E)) (hHr ⟨x, hxr⟩)
    exact (hermap ⟨x, hxr⟩).trans (congrArg p (hval.symm.trans (hHf ⟨x, hxb⟩)))
  obtain ⟨k, hk, hkd, hkb⟩ := Dehn.exists_circle_attachment_map_union he D B hD hB
    (s.piecewiseAffine.restrict_finite D hD (hDs.subset.trans hdS)) hcapPL
    (fun x hx hy => hagree x (hDs.subset hx) (hBs.subset hy))
  have hkd' : EqOn k s.map d := hDs ▸ hkd
  have hkb' : EqOn k (p ∘ f) b := hBs ▸ hkb
  have hkS : PolyhedralPLInCharts e k Sphere := by
    simpa only [hDs, hBs, hunion] using hk
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x, hx⟩, s.map_eq ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hfi : InjOn f b := by
    intro x hx y hy hxy
    have hh : H ⟨x, hx⟩ = H ⟨y, hy⟩ :=
      Subtype.ext ((hHf ⟨x, hx⟩).trans (hxy.trans (hHf ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective hh)
  have hmix (x : V3) (hx : x ∈ d) (y : V3) (hy : y ∈ b)
      (hxy : s.map x = p (f y)) : x = y := by
    have hxS : s.map x ∈ S := by
      rw [s.map_eq ⟨x, hdS hx⟩]
      exact (s.parametrization ⟨x, hdS hx⟩).property
    have hyq : f y ∈ q := by
      obtain ⟨z, hz, hzy⟩ := hcap.subset ⟨⟨f y, hmapf y hy, rfl⟩, hxy ▸ hxS⟩
      exact hpi (hc.1 hz) (hmapf y hy) hzy ▸ hz
    have hyr : y ∈ r := (hHmem ⟨y, hy⟩).mpr (by rwa [hHf])
    have hyd : y ∈ d := (hinter.symm.subset hyr).1
    exact hsi (hdS hx) (hbS hy) (hxy.trans (hagree y hyd hy).symm)
  have hki : InjOn k Sphere := by
    intro x hx y hy hxy
    rcases hunion.symm.subset hx with hxd | hxb
    · rcases hunion.symm.subset hy with hyd | hyb
      · exact hsi hx hy ((hkd' hxd).symm.trans (hxy.trans (hkd' hyd)))
      · exact hmix x hxd y hyb ((hkd' hxd).symm.trans (hxy.trans (hkb' hyb)))
    · rcases hunion.symm.subset hy with hyd | hyb
      · exact (hmix y hyd x hxb ((hkd' hyd).symm.trans (hxy.symm.trans (hkb' hxb)))).symm
      · apply hfi hxb hyb
        exact hpi (hmapf x hxb) (hmapf y hyb)
          ((hkb' hxb).symm.trans (hxy.trans (hkb' hyb)))
  have hfb : f '' b = c := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hmapf x hx
    · intro y hy
      obtain ⟨x, hx⟩ := H.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (hHf x).symm.trans (congrArg Subtype.val hx)⟩
  have hkimage : k '' b = p '' c := by
    rw [image_congr hkb', image_comp, hfb]
  have hwhole : k '' Sphere = (s.map '' d) ∪ (p '' c) := by
    rw [← hunion, image_union, image_congr hkd', hkimage]
  let fS : Sphere → X := fun x => k x
  have hfc : Continuous fS := hkS.continuousOn.domRestrict
  have hfsi : Function.Injective fS := fun x y h =>
    Subtype.ext (hki x.property y.property h)
  let : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let u := hfc.isClosedEmbedding hfsi |>.isEmbedding.toHomeomorph
  have hrange : range fS = (s.map '' d) ∪ (p '' c) := by
    rw [← hwhole]
    exact (image_eq_range k Sphere).symm
  let t : ChartwisePLSphere e ((s.map '' d) ∪ (p '' c)) := {
    parametrization := u.trans (Homeomorph.setCongr hrange)
    map := k
    map_eq := fun _ => rfl
    piecewiseAffine := hkS }
  exact ⟨t, hkd', hkimage⟩

theorem ChartwisePLSphere.exists_original_cap_on_retained_disk
    {X ι E M : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d b r : Set V3} {c q : Set E} {p : E → X}
    (hd : IsFinitePLBallPair P2 d r) (hb : IsFinitePLBallPair P2 b r)
    (hc : IsFinitePLBallPair M c q)
    (hp : PolyhedralPLInCharts e p c) (hpi : InjOn p c)
    (hunion : d ∪ b = Sphere) (hinter : d ∩ b = r)
    (hcap : (p '' c) ∩ S = p '' q) (hrimage : s.map '' r = p '' q) :
    ∃ t : ChartwisePLSphere e ((s.map '' d) ∪ (p '' c)),
      EqOn t.map s.map d ∧ t.map '' b = p '' c := by
  classical
  have hdS : d ⊆ Sphere := subset_union_left.trans hunion.subset
  have hrS : r ⊆ Sphere := hd.1.trans hdS
  let : CompactSpace c := isCompact_iff_compactSpace.mp hc.isCompact
  let H := hp.continuousOn.domRestrict.isClosedEmbedding
    (fun x y h => Subtype.ext (hpi x.property y.property h)) |>.isEmbedding.toHomeomorph
  let pr : c ≃ₜ (p '' c) := H.trans (Homeomorph.setCongr (image_eq_range p c).symm)
  have hrpc : MapsTo s.map r (p '' c) := by
    intro x hx
    exact image_mono hc.1 (hrimage.subset ⟨x,hx,rfl⟩)
  let g : V3 → E := fun x => if hx : x ∈ r then pr.symm ⟨s.map x,hrpc hx⟩ else 0
  have hgval (x : r) : g x = (pr.symm ⟨s.map x,hrpc x.property⟩ : E) := by
    simp only [g,dif_pos x.property]
  have hgc : MapsTo g r c := by
    intro x hx
    rw [hgval ⟨x,hx⟩]
    exact (pr.symm ⟨s.map x,hrpc hx⟩).property
  have hvalue (x : V3) (hx : x ∈ r) : p (g x) = s.map x := by
    rw [hgval ⟨x,hx⟩]
    exact congrArg Subtype.val (pr.apply_symm_apply ⟨s.map x,hrpc hx⟩)
  have hgcont : ContinuousOn g r := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (pr.symm.continuous.comp
      ((s.piecewiseAffine.continuousOn.mono hrS).domRestrict.subtype_mk
        (fun x => hrpc x.property)))
    convert h using 1
    funext x
    exact hgval x
  obtain ⟨n,P,_,hP,hPr⟩ := hd.exists_polygon_boundary
  let J := P.simplicialComplex hP
  have hJ := P.finite_simplicialComplex_faces hP
  have hJr : J.space = r := (P.simplicialComplex_space hP).trans hPr
  have hg : FinitePiecewiseAffineOn g r := by
    rw [←hJr]
    exact hp.finitePiecewiseAffineOn_lift he hpi J hJ (hgcont.mono hJr.subset)
      (fun _ hx => hgc (hJr.subset hx))
      ((s.piecewiseAffine.restrict_finite J hJ (hJr.subset.trans hrS)).congr
        (fun x hx => (hvalue x (hJr.subset hx)).symm))
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hgi : InjOn g r := by
    intro x hx y hy hxy
    apply hsi (hrS hx) (hrS hy)
    rw [←hvalue x hx,←hvalue y hy,hxy]
  have hgimage : g '' r = q := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨y,hy,hyx⟩ := hrimage.subset ⟨x,hx,rfl⟩
      exact hpi (hc.1 hy) (hgc hx) (hyx.trans (hvalue x hx).symm) ▸ hy
    · intro y hy
      obtain ⟨x,hx,hxy⟩ := hrimage.symm.subset ⟨y,hy,rfl⟩
      exact ⟨x,hx,hpi (hgc hx) (hc.1 hy) ((hvalue x hx).trans hxy)⟩
  obtain ⟨er,her,herval⟩ := hg.exists_homeomorph_image hgi
  let er' : r ≃ₜ q := er.trans (Homeomorph.setCongr hgimage)
  have her' : er'.IsFinitePL := her.setCongr rfl hgimage
  have hermap (x : r) : s.map x = p (er' x) := by
    have hx : (er' x : E) = g x := herval x
    rw [hx,hvalue x x.property]
  exact exists_original_cap_with_rim_map s he hd hb hc hp hpi hunion hinter hcap
    er' her' hermap

end PoincareConjecture.M76

import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MemberCircleCut
import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleNormalCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem exists_raw_member_cap
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x ∈ Q.source, ∃ i, x ∈ (e i).source)
    {d b r c q : Set V3}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d r)
    (hb : IsFinitePLBallPair (ℝ × ℝ) b r)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hunion : d ∪ b = Sphere) (hinter : d ∩ b = r)
    (hcQ : c ⊆ Q.target) (hcap : (Q.symm '' c) ∩ S = Q.symm '' q)
    (er : r ≃ₜ q) (her : er.IsFinitePL)
    (hermap : ∀ x : r, s.map x = Q.symm (er x)) :
    ∃ t : ChartwisePLSphere e ((s.map '' d) ∪ (Q.symm '' c)),
      EqOn t.map s.map d ∧ t.map '' b = Q.symm '' c := by
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
  have hcapPL : PolyhedralPLInCharts e (Q.symm ∘ f) B.space :=
    polyhedralPLInCharts_of_compatible_inverse e Q hcover hQ B hB
      (hBs.symm ▸ hf) (fun x hx => hcQ (hmapf x (hBs.subset hx)))
  have hagree (x : V3) (hxd : x ∈ d) (hxb : x ∈ b) : s.map x = Q.symm (f x) := by
    have hxr : x ∈ r := hinter.subset ⟨hxd, hxb⟩
    have hval := congrArg (fun y : c => (y : V3)) (hHr ⟨x, hxr⟩)
    exact (hermap ⟨x, hxr⟩).trans (congrArg Q.symm (hval.symm.trans (hHf ⟨x, hxb⟩)))
  obtain ⟨k, hk, hkd, hkb⟩ := Dehn.exists_circle_attachment_map_union he D B hD hB
    (s.piecewiseAffine.restrict_finite D hD (hDs.subset.trans hdS)) hcapPL
    (fun x hx hy => hagree x (hDs.subset hx) (hBs.subset hy))
  have hkd' : EqOn k s.map d := hDs ▸ hkd
  have hkb' : EqOn k (Q.symm ∘ f) b := hBs ▸ hkb
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
      (hxy : s.map x = Q.symm (f y)) : x = y := by
    have hxS : s.map x ∈ S := by
      rw [s.map_eq ⟨x, hdS hx⟩]
      exact (s.parametrization ⟨x, hdS hx⟩).property
    have hyq : f y ∈ q := by
      obtain ⟨z, hz, hzy⟩ := hcap.subset ⟨⟨f y, hmapf y hy, rfl⟩, hxy ▸ hxS⟩
      exact Q.symm.injOn (hcQ (hc.1 hz)) (hcQ (hmapf y hy)) hzy ▸ hz
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
        apply Q.symm.injOn (hcQ (hmapf x hxb)) (hcQ (hmapf y hyb))
        exact (hkb' hxb).symm.trans (hxy.trans (hkb' hyb))
  have hfb : f '' b = c := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hmapf x hx
    · intro y hy
      obtain ⟨x, hx⟩ := H.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (hHf x).symm.trans (congrArg Subtype.val hx)⟩
  have hkimage : k '' b = Q.symm '' c := by
    rw [image_congr hkb', image_comp, hfb]
  have hwhole : k '' Sphere = (s.map '' d) ∪ (Q.symm '' c) := by
    rw [← hunion, image_union, image_congr hkd', hkimage]
  let fS : Sphere → X := fun x => k x
  have hfc : Continuous fS := hkS.continuousOn.domRestrict
  have hfsi : Function.Injective fS := fun x y h =>
    Subtype.ext (hki x.property y.property h)
  let : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let u := hfc.isClosedEmbedding hfsi |>.isEmbedding.toHomeomorph
  have hrange : range fS = (s.map '' d) ∪ (Q.symm '' c) := by
    rw [← hwhole]
    exact (image_eq_range k Sphere).symm
  let t : ChartwisePLSphere e ((s.map '' d) ∪ (Q.symm '' c)) := {
    parametrization := u.trans (Homeomorph.setCongr hrange)
    map := k
    map_eq := fun _ => rfl
    piecewiseAffine := hkS }
  exact ⟨t, hkd', hkimage⟩




theorem ChartwisePLSphere.exists_circle_caps
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x ∈ Q.source, ∃ i, x ∈ (e i).source)
    (J P : SimplicialComplex ℝ V3) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) (hP : P.faces.Finite)
    (hPs : P.space = Q '' (S ∩ Q.source) ∩ J.space)
    {n : ℕ} (L : Polygon V3 (n + 3))
    (hL : L.HasSimplicialEdges) (hLi : Function.Injective L)
    (hLP : L.boundary ℝ ⊆ P.space)
    (B : OpenPartialHomeomorph V3 P3) {w : V3}
    (hw : w ∈ B.source) (hBw : B w = 0)
    (hBS : ∀ x ∈ B.source, x ∈ P.space ↔ (B x).2 = 0)
    (hBL : ∀ x ∈ L.boundary ℝ ∩ B.source, (B x).1.1 = 0)
    {c : Set V3} (hc : IsFinitePLBallPair (ℝ × ℝ) c (L.boundary ℝ))
    (hcQ : c ⊆ Q.target)
    (hcap : (Q.symm '' c) ∩ S = Q.symm '' L.boundary ℝ) :
    ∃ (g : V3 → V3) (m : ℕ) (R : Polygon V3 (m + 3)) (d₀ d₁ : Set V3),
      FinitePiecewiseAffineOn g P.space ∧ InjOn g P.space ∧
      Function.Injective R ∧ R.HasSimplicialEdges ∧
      R.boundary ℝ = g '' L.boundary ℝ ∧
      IsFinitePLBallPair (ℝ × ℝ) d₀ (R.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) d₁ (R.boundary ℝ) ∧
      d₀ ∪ d₁ = Sphere ∧ d₀ ∩ d₁ = R.boundary ℝ ∧
      (s.map '' d₀) ∪ (s.map '' d₁) = S ∧
      (s.map '' d₀) ∩ (s.map '' d₁) = Q.symm '' L.boundary ℝ ∧
      ∃ (s₀ : ChartwisePLSphere e ((s.map '' d₀) ∪ (Q.symm '' c)))
        (s₁ : ChartwisePLSphere e ((s.map '' d₁) ∪ (Q.symm '' c))),
        EqOn s₀.map s.map d₀ ∧ EqOn s₁.map s.map d₁ ∧
        s₀.map '' d₁ = Q.symm '' c ∧ s₁.map '' d₀ = Q.symm '' c ∧
        ((s.map '' d₀) ∪ (Q.symm '' c)) ∩
          ((s.map '' d₁) ∪ (Q.symm '' c)) = Q.symm '' c := by
  classical
  obtain ⟨g, m, R, d₀, d₁, hg, hgi, _, hRi, hR, hRb, hd₀, hd₁,
      hunion, hinter, _, _, _, hphysical, hphysicalrim, hright⟩ :=
    s.exists_parameter_circle_cut Q hQ J P hJ hJQ hP hPs L hL hLi hLP B hw hBw hBS hBL
  have hgL : FinitePiecewiseAffineOn g (L.boundary ℝ) := by
    rw [← L.simplicialComplex_space hL]
    exact hg.restrict (L.simplicialComplex hL) (L.finite_simplicialComplex_faces hL)
      ((L.simplicialComplex_space hL).subset.trans hLP)
  obtain ⟨E, hE, hEval⟩ := hgL.exists_homeomorph_image (hgi.mono hLP)
  let er : L.boundary ℝ ≃ₜ R.boundary ℝ := E.trans (Homeomorph.setCongr hRb.symm)
  have her : er.IsFinitePL := hE.setCongr rfl hRb.symm
  have hermap (x : R.boundary ℝ) : s.map x = Q.symm (er.symm x) := by
    have hval : g (er.symm x) = x := by
      have hval' : (er (er.symm x) : V3) = g (er.symm x) := hEval (er.symm x)
      exact hval'.symm.trans (congrArg Subtype.val (er.apply_symm_apply x))
    rw [← hval]
    exact hright _ (er.symm x).property
  obtain ⟨s₀, hs₀, hs₀cap⟩ := exists_raw_member_cap s he Q hQ hcover
    hd₀ hd₁ hc hunion hinter hcQ hcap er.symm her.symm hermap
  obtain ⟨s₁, hs₁, hs₁cap⟩ := exists_raw_member_cap s he Q hQ hcover
    hd₁ hd₀ hc (by rwa [union_comm]) (by rwa [inter_comm]) hcQ hcap er.symm her.symm hermap
  refine ⟨g, m, R, d₀, d₁, hg, hgi, hRi, hR, hRb, hd₀, hd₁,
    hunion, hinter, hphysical, hphysicalrim, s₀, s₁, hs₀, hs₁, hs₀cap, hs₁cap, ?_⟩
  ext x
  constructor
  · rintro ⟨hx₀ | hxc, hx₁ | hxc⟩
    · exact (image_mono hc.1) (hphysicalrim.subset ⟨hx₀, hx₁⟩)
    · exact hxc
    · exact hxc
    · exact hxc
  · exact fun hx => ⟨Or.inr hx, Or.inr hx⟩

end PoincareConjecture.M76

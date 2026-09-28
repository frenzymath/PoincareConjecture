import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningBigonNonbounding
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalSphereAnnulusParameter
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.OriginalSphere
import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.exists_original_disk_complement
    {X F ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d q : Set F} (hd : IsFinitePLBallPair P2 d q)
    (p : F → X) (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hpS : p '' d ⊆ S) (hout : (S \ p '' d).Nonempty) :
    ∃ k r : Set V3, IsFinitePLBallPair P2 k r ∧ k ⊆ Sphere ∧
      PolyhedralPLInCharts e s.map k ∧ InjOn s.map k ∧
      s.map '' k = S \ (p '' d \ p '' q) ∧ s.map '' r = p '' q := by
  classical
  let g : F → V3 := fun z => if hz : z ∈ d then
    s.parametrization.symm ⟨p z,hpS ⟨z,hz,rfl⟩⟩ else 0
  have hgval (z : d) : g z = (s.parametrization.symm ⟨p z,hpS ⟨z,z.property,rfl⟩⟩ : V3) := by
    simp only [g,dif_pos z.property]
  have hgc : ContinuousOn g d := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (s.parametrization.symm.continuous.comp
      (hp.continuousOn.domRestrict.subtype_mk (fun z => hpS ⟨z,z.property,rfl⟩)))
    convert h using 1
    funext z
    exact hgval z
  have hgS : MapsTo g d Sphere := by
    intro z hz
    rw [hgval ⟨z,hz⟩]
    exact (s.parametrization.symm ⟨p z,hpS ⟨z,hz,rfl⟩⟩).property
  have hvalue (z : F) (hz : z ∈ d) : s.map (g z) = p z := by
    rw [hgval ⟨z,hz⟩,s.map_eq,s.parametrization.apply_symm_apply]
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hsd : s.map '' Sphere = S := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      rw [s.map_eq ⟨z,hz⟩]
      exact (s.parametrization ⟨z,hz⟩).property
    · intro x hx
      exact ⟨s.parametrization.symm ⟨x,hx⟩,(s.parametrization.symm ⟨x,hx⟩).property,
        by rw [s.map_eq,s.parametrization.apply_symm_apply]⟩
  have hcomp : PolyhedralPLInCharts e (s.map ∘ g) d := hp.congr (fun z hz => (hvalue z hz).symm)
  have hg : FinitePiecewiseAffineOn g d := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hd
    rw [←hKs]
    exact s.piecewiseAffine.finitePiecewiseAffineOn_lift he hsi K hK
      (hgc.mono hKs.subset) (fun z hz => hgS (hKs.subset hz)) (hKs.symm ▸ hcomp)
  have hgi : InjOn g d := by
    intro x hx y hy hxy
    exact hpi hx hy ((hvalue x hx).symm.trans ((congrArg s.map hxy).trans (hvalue y hy)))
  have himage (Z : Set F) (hZ : Z ⊆ d) : s.map '' (g '' Z) = p '' Z := by
    rw [image_image]
    exact image_congr (fun z hz => hvalue z (hZ hz))
  have hgd : g '' d ⊆ Sphere := image_subset_iff.mpr hgS
  have hgr : g '' q ⊆ g '' d := image_mono hd.1
  have hout' : (Sphere \ g '' d).Nonempty := by
    obtain ⟨x,hx,hxn⟩ := hout
    obtain ⟨z,hz,rfl⟩ := hsd.symm.subset hx
    exact ⟨z,hz,fun h => hxn ((himage d subset_rfl).subset ⟨z,h,rfl⟩)⟩
  have hk := (isFinitePLBallPair_unit_cube (ι := Fin 3)).boundary_disk_complement
    (by simp) (hd.image hg hgi) hgd hout'
  let k := Sphere \ (g '' d \ g '' q)
  have hkS : k ⊆ Sphere := sdiff_subset
  have hsk : PolyhedralPLInCharts e s.map k := by
    obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hk
    change PolyhedralPLInCharts e s.map (Sphere \ (g '' d \ g '' q))
    rw [←hKs]
    exact s.piecewiseAffine.restrict_finite K hK (hKs.subset.trans hkS)
  refine ⟨k,g '' q,hk,hkS,hsk,hsi.mono hkS,?_,himage q hd.1⟩
  change s.map '' (Sphere \ (g '' d \ g '' q)) = S \ (p '' d \ p '' q)
  rw [hsi.image_sdiff_subset (sdiff_subset.trans hgd),hsd,
    (hsi.mono hgd).image_sdiff_subset hgr,himage d subset_rfl,himage q hd.1]

theorem ball_patch_set_identities
    {X : Type*} {S Q T A r : Set X}
    (hrA : r ⊆ A) (hAT : A ⊆ T) (hTQ : T ⊆ Q) (hcontact : Q ∩ S = A) :
    (S \ (A \ r)) ∩ (T \ (A \ r)) = r ∧
    Q ∩ ((S \ (A \ r)) ∪ (T \ (A \ r))) = T \ (A \ r) ∧
    S = (((S \ (A \ r)) ∪ (T \ (A \ r))) \ ((T \ (A \ r)) \ r)) ∪
      (T \ ((T \ (A \ r)) \ r)) := by
  have hAS : A ⊆ S := hcontact.symm.subset.trans inter_subset_right
  have hST : S ∩ T = A := by
    ext x
    constructor
    · intro hx
      exact hcontact.subset ⟨hTQ hx.2,hx.1⟩
    · intro hx
      exact ⟨hAS hx,hAT hx⟩
  refine ⟨?_,?_,?_⟩
  · ext x
    have hst : x ∈ S ∧ x ∈ T ↔ x ∈ A := Set.ext_iff.mp hST x
    have hr := @hrA x
    have haS := @hAS x
    have haT := @hAT x
    simp only [mem_inter_iff,mem_sdiff]
    tauto
  · ext x
    have hqs : x ∈ Q ∧ x ∈ S ↔ x ∈ A := Set.ext_iff.mp hcontact x
    have htq := @hTQ x
    have hat := @hAT x
    simp only [mem_inter_iff,mem_union,mem_sdiff]
    tauto
  · ext x
    have hst : x ∈ S ∧ x ∈ T ↔ x ∈ A := Set.ext_iff.mp hST x
    have hr := @hrA x
    have haS := @hAS x
    have haT := @hAT x
    simp only [mem_union,mem_sdiff]
    tauto

theorem ChartwisePLSphere.exists_original_ball_patch_replacement
    {X F ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {S Q T : Set X}
    (s : ChartwisePLSphere e S) (u : ChartwisePLBall e Q T)
    (he : ∀ i j,(e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {d q : Set F} (hd : IsFinitePLBallPair P2 d q)
    (p : F → X) (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hcontact : Q ∩ S = p '' d) (hdT : p '' d ⊆ T)
    (hSout : (S \ p '' d).Nonempty) (hTout : (T \ p '' d).Nonempty) :
    ∃ (f g : V3 → X) (k r c b : Set V3),
      IsFinitePLBallPair P2 k r ∧ IsFinitePLBallPair P2 c b ∧
      PolyhedralPLInCharts e f k ∧ PolyhedralPLInCharts e g c ∧
      InjOn f k ∧ InjOn g c ∧
      f '' k = S \ (p '' d \ p '' q) ∧ g '' c = T \ (p '' d \ p '' q) ∧
      f '' r = p '' q ∧ g '' b = p '' q ∧
      Nonempty (ChartwisePLSphere e ((S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q)))) ∧
      Q ∩ ((S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q))) = T \ (p '' d \ p '' q) := by
  obtain ⟨t⟩ := u.nonempty_boundarySphere
  obtain ⟨k,r,hk,_,hfk,hfi,hfimage,hfrim⟩ := s.exists_original_disk_complement
    he hd p hp hpi (hcontact.symm.subset.trans inter_subset_right) hSout
  obtain ⟨c,b,hc,_,hgc,hgi,hgimage,hgrim⟩ := t.exists_original_disk_complement
    he hd p hp hpi hdT hTout
  obtain ⟨hmeet,hQnew,_⟩ := ball_patch_set_identities (image_mono hd.1) hdT u.boundary_subset hcontact
  have hsg : (s.map '' k) ∩ (t.map '' c) = s.map '' r := by
    rw [hfimage,hgimage,hfrim]
    exact hmeet
  have hnew := Dehn.Annuli.nonempty_original_sphere_of_disk_union he hk hc hfk hgc hfi hgi
    (hfrim.trans hgrim.symm) hsg
  rw [hfimage,hgimage] at hnew
  exact ⟨s.map,t.map,k,r,c,b,hk,hc,hfk,hgc,hfi,hgi,hfimage,hgimage,hfrim,hgrim,hnew,hQnew⟩

theorem ChartwisePLSphere.nonbounding_original_ball_patch_replacement
    {X F ι : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {R S Q T : Set X}
    (s : ChartwisePLSphere e S) (he : PLDomain e R) (hR : IsCompact R)
    (u : ChartwisePLBall e Q T) (hQR : Q ⊆ interior R) (hSR : S ⊆ interior R)
    {d q : Set F} (hd : IsFinitePLBallPair P2 d q)
    (p : F → X) (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    (hcontact : Q ∩ S = p '' d) (hdT : p '' d ⊆ T)
    (hSout : (S \ p '' d).Nonempty) (hTout : (T \ p '' d).Nonempty)
    (hnonbounding : ¬∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B S)) :
    Nonempty (ChartwisePLSphere e ((S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q)))) ∧
      Q ∩ ((S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q))) = T \ (p '' d \ p '' q) ∧
      ¬∃ B, B ⊆ R ∧ Nonempty (ChartwisePLBall e B
        ((S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q)))) := by
  obtain ⟨f,g,k,r,c,b,_,hc,_,hgc,_,hgi,_,hgimage,_,hgrim,hnew,hQnew⟩ :=
    s.exists_original_ball_patch_replacement u he.compatible hd p hp hpi hcontact hdT hSout hTout
  have hnewR : (S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q)) ⊆ interior R :=
    union_subset (sdiff_subset.trans hSR) (sdiff_subset.trans (u.boundary_subset.trans hQR))
  have hnewout : (((S \ (p '' d \ p '' q)) ∪ (T \ (p '' d \ p '' q))) \ g '' c).Nonempty := by
    rw [hgimage]
    obtain ⟨x,hxS,hxn⟩ := hSout
    refine ⟨x,Or.inl ⟨hxS,fun h => hxn h.1⟩,?_⟩
    intro hx
    exact hxn (hcontact.subset ⟨u.boundary_subset hx.1,hxS⟩)
  have hTout' : (T \ g '' c).Nonempty := by
    rw [hgimage]
    obtain ⟨z,hzd,hzq⟩ := hd.sdiff_nonempty
    have hpz : p z ∈ p '' d := ⟨z,hzd,rfl⟩
    have hpzq : p z ∉ p '' q := by
      rintro ⟨w,hw,hwz⟩
      exact hzq (hpi (hd.1 hw) hzd hwz ▸ hw)
    exact ⟨p z,hdT hpz,fun h => h.2 ⟨hpz,hpzq⟩⟩
  obtain ⟨_,_,hback⟩ := ball_patch_set_identities (image_mono hd.1) hdT u.boundary_subset hcontact
  refine ⟨hnew,hQnew,?_⟩
  exact s.nonbounding_of_ball_patch_replacement he hR u (hQR.trans interior_subset) hnewR
    hc g hgc hgi (by rw [hgimage]; exact hQnew) (by rw [hgimage]; exact sdiff_subset)
    hnewout hTout' (by rw [hgimage,hgrim]; exact hback) hnonbounding

end PoincareConjecture.M76

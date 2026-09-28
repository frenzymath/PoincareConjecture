import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalRetainedDiskCap
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalPolygonCut










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Sphere" => sphere (0 : V3) 1

theorem ChartwisePLSphere.exists_original_raw_circle_caps
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (d : Fin 2 → Set V3) {r : Set V3}
    (hd : ∀ b, IsFinitePLBallPair P2 (d b) r)
    (hwhole : d 0 ∪ d 1 = Sphere) (hinter : d 0 ∩ d 1 = r)
    {c q : Set E} {p : E → X} (hc : IsFinitePLBallPair P2 c q)
    (hp : PolyhedralPLInCharts e p c) (hpi : InjOn p c)
    (hcap : (p '' c) ∩ S = p '' q) (hrim : s.map '' r = p '' q) :
    ∃ t : ∀ b, ChartwisePLSphere e ((s.map '' d b) ∪ (p '' c)),
      (∀ b, EqOn (t b).map s.map (d b)) ∧
      (∀ b, (t b).map '' d b.rev = p '' c) ∧
      (s.map '' d 0) ∪ (s.map '' d 1) = S ∧
      (s.map '' d 0) ∩ (s.map '' d 1) = p '' q ∧
      ((s.map '' d 0) ∪ (p '' c)) ∪ ((s.map '' d 1) ∪ (p '' c)) = S ∪ (p '' c) ∧
      ((s.map '' d 0) ∪ (p '' c)) ∩ ((s.map '' d 1) ∪ (p '' c)) = p '' c ∧
      (∀ b, ((s.map '' d b) ∪ (p '' c)) ∩ S = s.map '' d b) ∧
      (∀ b, ((s.map '' d b) ∪ (p '' c)) \ (p '' c) =
        (s.map '' d b) \ (p '' q)) := by
  classical
  have hside (b : Fin 2) : d b ∪ d b.rev = Sphere := by
    fin_cases b
    · simpa using hwhole
    · simpa [union_comm] using hwhole
  have hsideint (b : Fin 2) : d b ∩ d b.rev = r := by
    fin_cases b
    · simpa using hinter
    · simpa [inter_comm] using hinter
  choose t ht htb using fun b => s.exists_original_cap_on_retained_disk he
    (hd b) (hd b.rev) hc hp hpi (hside b) (hsideint b) hcap hrim
  have hdS (b : Fin 2) : d b ⊆ Sphere := subset_union_left.trans (hside b).subset
  have hsS : s.map '' Sphere = S := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [s.map_eq ⟨x,hx⟩]
      exact (s.parametrization ⟨x,hx⟩).property
    · intro y hy
      obtain ⟨x,hx⟩ := s.parametrization.surjective ⟨y,hy⟩
      exact ⟨x,x.property,(s.map_eq x).trans (congrArg Subtype.val hx)⟩
  have hsi : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x,hx⟩,s.map_eq ⟨y,hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hphysical : (s.map '' d 0) ∪ (s.map '' d 1) = S := by
    rw [←image_union,hwhole,hsS]
  have hphysicalrim : (s.map '' d 0) ∩ (s.map '' d 1) = p '' q := by
    rw [←hrim,←hinter]
    apply Subset.antisymm
    · rintro x ⟨⟨y,hy,hyx⟩,⟨z,hz,hzx⟩⟩
      have hyz := hsi (hdS 0 hy) (hdS 1 hz) (hyx.trans hzx.symm)
      exact ⟨y,⟨hy,hyz.symm ▸ hz⟩,hyx⟩
    · rintro x ⟨y,hy,hyx⟩
      exact ⟨⟨y,hy.1,hyx⟩,⟨y,hy.2,hyx⟩⟩
  have hret (b : Fin 2) : s.map '' d b ⊆ S := (image_mono (hdS b)).trans hsS.subset
  have hrret (b : Fin 2) : p '' q ⊆ s.map '' d b :=
    hrim.symm.subset.trans (image_mono (hd b).1)
  refine ⟨t,ht,htb,hphysical,hphysicalrim,?_,?_,?_,?_⟩
  · rw [union_union_union_comm,hphysical,union_self]
  · apply Subset.antisymm
    · rintro x ⟨hx | hx,hx' | hx'⟩
      · exact image_mono hc.1 (hphysicalrim.subset ⟨hx,hx'⟩)
      · exact hx'
      · exact hx
      · exact hx
    · intro x hx
      exact ⟨Or.inr hx,Or.inr hx⟩
  · intro b
    apply Subset.antisymm
    · rintro x ⟨hx | hx,hxS⟩
      · exact hx
      · exact hrret b (hcap.subset ⟨hx,hxS⟩)
    · intro x hx
      exact ⟨Or.inl hx,hret b hx⟩
  · intro b
    ext x
    constructor
    · rintro ⟨hx | hx,hn⟩
      · exact ⟨hx,fun hq => hn (image_mono hc.1 hq)⟩
      · exact False.elim (hn hx)
    · rintro ⟨hx,hn⟩
      exact ⟨Or.inl hx,fun hc => hn (hcap.subset ⟨hc,hret b hx⟩)⟩

theorem ChartwisePLSphere.exists_original_disk_rim_raw_caps
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {c q : Set E} {p : E → X} (hc : IsFinitePLBallPair P2 c q)
    (hp : PolyhedralPLInCharts e p c) (hpi : InjOn p c)
    (hcap : (p '' c) ∩ S = p '' q)
    (z : S) (hz : (z : X) ∉ p '' q) :
    ∃ (m : ℕ) (R : Polygon V3 (m + 3)) (d : Fin 2 → Set V3),
      Function.Injective R ∧ R.HasSimplicialEdges ∧
      (∀ b, IsFinitePLBallPair P2 (d b) (R.boundary ℝ)) ∧
      d 0 ∪ d 1 = Sphere ∧ d 0 ∩ d 1 = R.boundary ℝ ∧
      s.map '' R.boundary ℝ = p '' q ∧
      ∃ t : ∀ b, ChartwisePLSphere e ((s.map '' d b) ∪ (p '' c)),
        (∀ b, EqOn (t b).map s.map (d b)) ∧
        (∀ b, (t b).map '' d b.rev = p '' c) ∧
        (s.map '' d 0) ∪ (s.map '' d 1) = S ∧
        (s.map '' d 0) ∩ (s.map '' d 1) = p '' q ∧
        ((s.map '' d 0) ∪ (p '' c)) ∪ ((s.map '' d 1) ∪ (p '' c)) = S ∪ (p '' c) ∧
        ((s.map '' d 0) ∪ (p '' c)) ∩ ((s.map '' d 1) ∪ (p '' c)) = p '' c ∧
        (∀ b, ((s.map '' d b) ∪ (p '' c)) ∩ S = s.map '' d b) ∧
        (∀ b, ((s.map '' d b) ∪ (p '' c)) \ (p '' c) =
          (s.map '' d b) \ (p '' q)) := by
  obtain ⟨n,P,hPi,hP,hPq⟩ := hc.exists_polygon_boundary
  let J := P.simplicialComplex hP
  have hJ := P.finite_simplicialComplex_faces hP
  have hJs : J.space = q := (P.simplicialComplex_space hP).trans hPq
  have hpq : PolyhedralPLInCharts e p (P.boundary ℝ) := by
    rw [←P.simplicialComplex_space hP]
    exact hp.restrict_finite J hJ (hJs.subset.trans hc.1)
  have hqS : p '' q ⊆ S := hcap.symm.subset.trans inter_subset_right
  obtain ⟨m,R,d,hRi,hR,hd,hwhole,hinter,hrim⟩ :=
    s.exists_original_polygon_parameter_cut he P hP hPi hpq
      (hpi.mono (hPq.subset.trans hc.1))
      (by simpa only [hPq] using hqS) z (by simpa only [hPq] using hz)
  have hrim' : s.map '' R.boundary ℝ = p '' q := by simpa only [hPq] using hrim
  exact ⟨m,R,d,hRi,hR,hd,hwhole,hinter,hrim',
    s.exists_original_raw_circle_caps he d hd hwhole hinter hc hp hpi hcap hrim'⟩

end PoincareConjecture.M76

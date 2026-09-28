import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBallPairRecognition
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.DiskAttachment
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage

set_option autoImplicit false
open Set Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem isFinitePLBallPair_of_original_cap_annulus
    {X E F ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {C r : Set E} (hCK : C ⊆ K.space) (hrK : r ⊆ K.space)
    {d q : Set F} (hd : IsFinitePLBallPair P2 d q)
    {p : F → X} (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    {a : P2 → X} (ha : PolyhedralPLInCharts e a Ann) (hai : InjOn a Ann)
    (hcarrier : (p '' d) ∪ (a '' Ann) = g '' C)
    (hcontact : (p '' d) ∩ (a '' Ann) = p '' q)
    (hinner : ∀ x ∈ Ann, a x ∈ p '' q ↔ depth 8 x = 1)
    (hrA : g '' r ⊆ a '' Ann)
    (houter : ∀ x ∈ Ann, a x ∈ g '' r ↔ depth 8 x = -1) :
    IsFinitePLBallPair P2 C r := by
  classical
  let D := K.space ∩ g ⁻¹' (p '' d)
  let R := K.space ∩ g ⁻¹' (p '' q)
  have hpK : p '' d ⊆ g '' K.space :=
    subset_union_left.trans (hcarrier.subset.trans (image_mono hCK))
  have haK : a '' Ann ⊆ g '' K.space :=
    subset_union_right.trans (hcarrier.subset.trans (image_mono hCK))
  have hgD : g '' D = p '' d := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x,hx,hxy⟩ := hpK hy
      exact ⟨x,⟨hx,show g x ∈ p '' d from hxy.symm ▸ hy⟩,hxy⟩
  have hgR : g '' R = p '' q := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x,hx,hxy⟩ := hpK (image_mono hd.1 hy)
      exact ⟨x,⟨hx,show g x ∈ p '' q from hxy.symm ▸ hy⟩,hxy⟩
  have hD : IsFinitePLBallPair P2 D R :=
    isFinitePLBallPair_of_original_parametrization he K hK hg hgi
      inter_subset_left inter_subset_left hd hp hpi hgD.symm hgR.symm
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  let B : K.space ≃ₜ (g '' K.space) := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn g K.space hgi)
    (hg.continuousOn.domRestrict.subtype_mk _)
  let f : P2 → E := fun x => if hx : x ∈ Ann then
    B.symm ⟨a x,haK ⟨x,hx,rfl⟩⟩ else 0
  have hfval (x : Ann) : f x = (B.symm ⟨a x,haK ⟨x,x.property,rfl⟩⟩ : E) := by
    simp only [f,dif_pos x.property]
  have hfK : MapsTo f Ann K.space := by
    intro x hx
    rw [hfval ⟨x,hx⟩]
    exact (B.symm _).property
  have hvalue (x : P2) (hx : x ∈ Ann) : g (f x) = a x := by
    rw [hfval ⟨x,hx⟩]
    exact congrArg Subtype.val (B.apply_symm_apply _)
  have hfc : ContinuousOn f Ann := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := continuous_subtype_val.comp (B.symm.continuous.comp
      (ha.continuousOn.domRestrict.subtype_mk (fun x => haK ⟨x,x.property,rfl⟩)))
    convert hc using 1
    funext x
    exact hfval x
  obtain ⟨J,hJ,hJs⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8)
  have hf : FinitePiecewiseAffineOn f Ann := by
    rw [←hJs]
    exact hg.finitePiecewiseAffineOn_lift he hgi J hJ (hfc.mono hJs.subset)
      (fun x hx => hfK (hJs.subset hx))
      ((hJs.symm ▸ ha).congr (fun x hx => (hvalue x (hJs.subset hx)).symm))
  have hfi : InjOn f Ann := by
    intro x hx y hy hxy
    exact hai hx hy ((hvalue x hx).symm.trans ((congrArg g hxy).trans (hvalue y hy)))
  obtain ⟨c,hc,hcf⟩ := hf.exists_homeomorph_image hfi
  have hmem (x : P2) (hx : x ∈ Ann) {s : Set E} (hs : s ⊆ K.space) :
      f x ∈ s ↔ a x ∈ g '' s := by
    constructor
    · intro h
      exact ⟨f x,h,hvalue x hx⟩
    · rintro ⟨y,hy,hyx⟩
      exact (hgi (hs hy) (hfK hx) (hyx.trans (hvalue x hx).symm)) ▸ hy
  have hcapcontact : D ∩ (f '' Ann) = R := by
    apply Subset.antisymm
    · rintro x ⟨hxD,⟨y,hy,hyx⟩⟩
      refine ⟨hxD.1,hcontact.subset ⟨hxD.2,?_⟩⟩
      exact ⟨y,hy,(hvalue y hy).symm.trans (congrArg g hyx)⟩
    · intro x hx
      obtain ⟨y,hy,hyx⟩ := (hcontact.symm.subset hx.2).2
      refine ⟨⟨hx.1,image_mono hd.1 hx.2⟩,y,hy,?_⟩
      exact hgi (hfK hy) hx.1 ((hvalue y hy).trans hyx)
  have hrsource : r ⊆ f '' Ann := by
    intro x hx
    obtain ⟨y,hy,hyx⟩ := hrA ⟨x,hx,rfl⟩
    exact ⟨y,hy,hgi (hfK hy) (hrK hx) ((hvalue y hy).trans hyx)⟩
  have hball : IsFinitePLBallPair P2 (D ∪ f '' Ann) r := by
    apply Dehn.isFinitePLBallPair_attach_annulus_inner hD hcapcontact
      (by norm_num) (by norm_num) c hc ?_ hrsource ?_
    · intro z
      rw [hcf]
      exact (hinner z z.property).symm.trans
        (by rw [←hgR]; exact (hmem z z.property inter_subset_left).symm)
    · intro z
      rw [hcf]
      exact (houter z z.property).symm.trans (hmem z z.property hrK).symm
  have hsource : D ∪ f '' Ann = C := by
    apply Subset.antisymm
    · intro x hx
      have hxK : x ∈ K.space := hx.elim (fun h => h.1) (by rintro ⟨y,hy,rfl⟩; exact hfK hy)
      have hximage : g x ∈ (p '' d) ∪ (a '' Ann) := by
        rcases hx with hx | ⟨y,hy,rfl⟩
        · exact Or.inl hx.2
        · exact Or.inr ⟨y,hy,(hvalue y hy).symm⟩
      obtain ⟨y,hy,hyx⟩ := hcarrier.subset hximage
      exact hgi (hCK hy) hxK hyx ▸ hy
    · intro x hx
      rcases hcarrier.symm.subset ⟨x,hx,rfl⟩ with hc | ha
      · exact Or.inl ⟨hCK hx,hc⟩
      · obtain ⟨y,hy,hyx⟩ := ha
        exact Or.inr ⟨y,hy,hgi (hfK hy) (hCK hx) ((hvalue y hy).trans hyx)⟩
  exact hsource ▸ hball

theorem original_cap_annulus_carrier_is_proper_disk
    {X E F ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {r : Set E} (hrT : r ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))
    {d q : Set F} (hd : IsFinitePLBallPair P2 d q)
    {p : F → X} (hp : PolyhedralPLInCharts e p d) (hpi : InjOn p d)
    {a : P2 → X} (ha : PolyhedralPLInCharts e a Ann) (hai : InjOn a Ann)
    (hcap : p '' d ⊆ interior (g '' convexHull ℝ (t : Set E)))
    (haT : a '' Ann ⊆ g '' convexHull ℝ (t : Set E))
    (hain : (a '' Ann) \ (g '' r) ⊆ interior (g '' convexHull ℝ (t : Set E)))
    (hcontact : (p '' d) ∩ (a '' Ann) = p '' q)
    (hinner : ∀ x ∈ Ann, a x ∈ p '' q ↔ depth 8 x = 1)
    (hrA : g '' r ⊆ a '' Ann)
    (houter : ∀ x ∈ Ann, a x ∈ g '' r ↔ depth 8 x = -1) :
    let C := (convexHull ℝ (t : Set E)) ∩ g ⁻¹' ((p '' d) ∪ (a '' Ann))
    IsFinitePLBallPair P2 C r ∧
      C ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = r ∧
      g '' C = (p '' d) ∪ (a '' Ann) := by
  classical
  let T := convexHull ℝ (t : Set E)
  let C := T ∩ g ⁻¹' ((p '' d) ∪ (a '' Ann))
  have hfrontT : intrinsicFrontier ℝ T ⊆ T :=
    intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hrK := hrT.trans (hfrontT.trans (K.convexHull_subset_space ht))
  have himage : g '' C = (p '' d) ∪ (a '' Ann) := by
    apply Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro y hy
      have hyT : y ∈ g '' T := hy.elim (fun h => interior_subset (hcap h)) (fun h => haT h)
      obtain ⟨x,hx,hxy⟩ := hyT
      exact ⟨x,⟨hx,show g x ∈ (p '' d) ∪ (a '' Ann) from hxy.symm ▸ hy⟩,hxy⟩
  have hball : IsFinitePLBallPair P2 C r :=
    isFinitePLBallPair_of_original_cap_annulus he K hK hg hgi
      (inter_subset_left.trans (K.convexHull_subset_space ht)) hrK hd hp hpi ha hai
      himage.symm hcontact hinner hrA houter
  obtain ⟨B⟩ := exists_chartwisePLBall_image
    (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
    (ContinuousLinearEquiv.refl ℝ V3) hg (K.convexHull_subset_space ht) hgi
  refine ⟨hball,?_,himage⟩
  apply Subset.antisymm
  · rintro x ⟨hxC,hxfront⟩
    have hxphysical : g x ∈ frontier (g '' T) := by
      rw [B.frontier_eq]
      exact ⟨x,hxfront,rfl⟩
    have hxrim : g x ∈ g '' r := by
      rcases hxC.2 with hxc | hxa
      · exact False.elim (hxphysical.2 (hcap hxc))
      · by_contra hn
        exact hxphysical.2 (hain ⟨hxa,hn⟩)
    obtain ⟨y,hy,hyx⟩ := hxrim
    exact hgi (hrK hy) (K.convexHull_subset_space ht hxC.1) hyx ▸ hy
  · intro x hx
    exact ⟨⟨hfrontT (hrT hx),Or.inr (hrA ⟨x,hx,rfl⟩)⟩,hrT hx⟩

end PoincareConjecture.M76

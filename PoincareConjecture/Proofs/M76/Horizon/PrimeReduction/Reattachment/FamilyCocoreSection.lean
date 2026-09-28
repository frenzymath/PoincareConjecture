import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RegularCocoreCrossings
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ComponentMembership
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ProperDiskSelectedHole
import PoincareConjecture.Proofs.M76.PrimeReduction.BallModelCoordinates








set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem has_disjoint_polygon_presentation_iUnion
    {κ : Type*} [Finite κ] (T : κ → Set V3)
    (h : ∀i,HasDisjointPolygonPresentation (T i))
    (hdis : Pairwise fun i j => Disjoint (T i) (T j)) :
    HasDisjointPolygonPresentation (⋃i,T i) := by
  classical
  choose m n L hL hcover hpair using h
  let A := (i : κ) × Fin (m i)
  refine hasDisjointPolygonPresentation_of_family
    (fun x : A => n x.1 x.2) (fun x : A => L x.1 x.2) (fun x => hL x.1 x.2) ?_ ?_
  · ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      obtain ⟨a,ha⟩ := mem_iUnion.mp ((hcover i).subset hi)
      exact mem_iUnion.mpr ⟨⟨i,a⟩,ha⟩
    · intro hx
      obtain ⟨⟨i,a⟩,ha⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i,(hcover i).symm.subset (mem_iUnion.mpr ⟨a,ha⟩)⟩
  · rintro ⟨i,a⟩ ⟨j,b⟩ hne
    by_cases hij : i=j
    · subst j
      exact hpair i (fun hab => hne (by change a=b at hab; exact congrArg (fun z => (⟨i,z⟩ : A)) hab))
    · exact (hdis hij).mono
        (by intro x hx; rw [hcover]; exact mem_iUnion.mpr ⟨a,hx⟩)
        (by intro x hx; rw [hcover]; exact mem_iUnion.mpr ⟨b,hx⟩)

theorem exists_sphere_family_regular_cocore_section
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (s : ∀i,ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀i,(e i).symm.trans Q∈piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space⊆Q.target)
    (A : V3 →ᵃ[ℝ] ℝ) {a b : ℝ} (hab : a<b)
    (hband : ∀x∈Q '' ((⋃i,S i)∩Q.source)∩J.space,A x∈Ioo a b → x∈interior J.space) :
    ∃t∈Ioo a b,
      (∀i,HasDisjointPolygonPresentation ((Q '' (S i∩Q.source)∩J.space)∩{x | A x=t})) ∧
      HasDisjointPolygonPresentation ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | A x=t}) ∧
      ∀w∈(Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | A x=t},
        ∀O : Set V3,IsOpen O → w∈O →
          ∃B : OpenPartialHomeomorph V3 P3,
            w∈B.source ∧ B.source⊆O∩interior J.space ∧ B w=0 ∧
            LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀x∈B.source,Q.symm x∈⋃i,S i ↔ (B x).2=0) ∧
            ∀x∈B.source,A x-t=(B x).1.1 := by
  classical
  choose P hP hPs hbound hlocal using fun i => (s i).exists_finite_chart_carrier Q hQ J hJ hJQ
  have hvertices : (⋃i,(P i).vertices).Finite := finite_iUnion fun i =>
    (P i).finite_vertices_of_finite_faces (hP i)
  obtain ⟨t,ht,htnot⟩ := (Ioo_infinite hab).exists_notMem_finite (hvertices.image A)
  have hreg (i : κ) : ∀v∈(P i).vertices,A v≠t :=
    fun v hv h => htnot ⟨v,mem_iUnion.mpr ⟨i,hv⟩,h⟩
  let T : κ → Set V3 := fun i => (Q '' (S i∩Q.source)∩J.space)∩{x | A x=t}
  have hTi (i : κ) : T i⊆(Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | A x=t} :=
    inter_subset_inter_left _ (inter_subset_inter_left _ (image_mono
      (inter_subset_inter_left _ (subset_iUnion S i))))
  have hT (i : κ) : HasDisjointPolygonPresentation (T i) := by
    have hh := (s i).regular_cocore_section_of_carrier Q hQ J (P i) hJ hJQ (hP i)
      (hPs i) (hbound i) A t (hreg i) (fun x hx =>
        hband x (hTi i ⟨(hPs i).subset hx.1,hx.2⟩).1 (hx.2 ▸ ht))
    simpa only [hPs] using hh
  have hTdis : Pairwise fun i j => Disjoint (T i) (T j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨⟨⟨y,hy,hyx⟩,_⟩,_⟩ ⟨⟨⟨z,hz,hzx⟩,_⟩,_⟩
    have heq := Q.injOn hy.2 hz.2 (hyx.trans hzx.symm)
    exact disjoint_left.mp (hdis hij) hy.1 (heq.symm ▸ hz.1)
  have hTall : ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | A x=t})=⋃i,T i := by
    ext x
    constructor
    · rintro ⟨⟨⟨y,⟨hy,hyQ⟩,hyx⟩,hxJ⟩,hxt⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨i,⟨⟨y,⟨hi,hyQ⟩,hyx⟩,hxJ⟩,hxt⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact hTi i hi
  refine ⟨t,ht,hT,hTall.symm ▸ has_disjoint_polygon_presentation_iUnion T hT hTdis,?_⟩
  intro w hw O hO hwO
  obtain ⟨i,hwi⟩ := mem_iUnion.mp (hTall.subset hw)
  have hwJ : w∈interior J.space := hband w hw.1 (hw.2 ▸ ht)
  have hwQ := hJQ (interior_subset hwJ)
  have hwS : Q.symm w∈S i := by
    obtain ⟨y,hy,hyw⟩ := hwi.1.1
    rw [←hyw,Q.left_inv hy.2]
    exact hy.1
  let others := ⋃j : {j : κ // j≠i},S j.val
  have hOthers : IsClosed others := isClosed_iUnion_of_finite fun j => (s j.val).isCompact.isClosed
  have hwOthers : Q.symm w∉others := by
    intro hh
    obtain ⟨j,hj⟩ := mem_iUnion.mp hh
    exact disjoint_left.mp (hdis (Ne.symm j.property)) hwS hj
  let V := O∩(Q.target∩Q.symm ⁻¹' othersᶜ)
  have hV : IsOpen V := hO.inter (Q.symm.isOpen_inter_preimage hOthers.isOpen_compl)
  let Bheight : V3 →ᵃ[ℝ] ℝ := A-AffineMap.const ℝ V3 t
  obtain ⟨B,hwB,hBV,hBw,hB,hBi,hBS,hBA⟩ :=
    (s i).exists_regular_cocore_crossing_chart Q hQ J (P i) hJ hJQ (hP i) (hPs i)
      Bheight (fun v hv hz => hreg i v hv (sub_eq_zero.mp hz))
      ((hPs i).symm.subset hwi.1) hwJ (sub_eq_zero.mpr hw.2) hV ⟨hwO,hwQ,hwOthers⟩
  refine ⟨B,hwB,fun x hx => ⟨(hBV hx).1.1,(hBV hx).2⟩,hBw,hB,hBi,?_,hBA⟩
  intro x hx
  have hmem : Q.symm x∈⋃i,S i ↔ Q.symm x∈S i := by
    constructor
    · intro hh
      obtain ⟨j,hj⟩ := mem_iUnion.mp hh
      by_cases hji : j=i
      · exact hji ▸ hj
      · exact ((hBV hx).1.2.2 (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)).elim
    · exact fun hh => mem_iUnion.mpr ⟨i,hh⟩
  exact hmem.trans (hBS x hx)

theorem exists_sphere_family_cocore_innermost_disk_at_height
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (s : ∀i,ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (Q : OpenPartialHomeomorph X V3)
    (J : SimplicialComplex ℝ V3) (hJQ : J.space⊆Q.target)
    (hJcv : Convex ℝ J.space) (H : V3 ≃ᴬ[ℝ] P3) (t : ℝ)
    (hpres : HasDisjointPolygonPresentation
      ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t}))
    (hinside : ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t})⊆interior J.space)
    (hcross : ∀w∈(Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t},
      ∀O : Set V3,IsOpen O → w∈O →
        ∃B : OpenPartialHomeomorph V3 P3,
          w∈B.source ∧ B.source⊆O∩interior J.space ∧ B w=0 ∧
          LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀x∈B.source,Q.symm x∈⋃i,S i ↔ (B x).2=0) ∧
          ∀x∈B.source,(H x).2-t=(B x).1.1)
    (hne : ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t}).Nonempty) :
        ∃(i : κ) (n : ℕ) (L : Polygon V3 (n+3)) (D U : Set V3),
          Function.Injective L ∧ L.HasSimplicialEdges ∧
          IsFinitePLBallPair (ℝ × ℝ) D (L.boundary ℝ) ∧
          D⊆interior J.space∩{x | (H x).2=t} ∧
          D∩Q '' ((⋃i,S i)∩Q.source)=L.boundary ℝ ∧
          D∩Q '' (S i∩Q.source)=L.boundary ℝ ∧
          IsCompact (((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t})\L.boundary ℝ) ∧
          IsOpen U ∧ D⊆U ∧ U⊆interior J.space ∧
          (∀j,j≠i → Disjoint (Q.symm '' U) (S j)) ∧
          (∀x∈U,x∈L.boundary ℝ ↔ Q.symm x∈S i ∧ (H x).2=t) ∧
          ∀w∈L.boundary ℝ,∀O : Set V3,IsOpen O → w∈O →
            ∃B : OpenPartialHomeomorph V3 P3,
              w∈B.source ∧ B.source⊆O∩interior J.space ∧ B w=0 ∧
              LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
              (∀x∈B.source,Q.symm x∈S i ↔ (B x).2=0) ∧
              ∀x∈B.source,(H x).2-t=(B x).1.1 := by
  classical
  let F : (ℝ × ℝ) →ᴬ[ℝ] V3 := H.symm.toContinuousAffineMap.comp
    ((ContinuousAffineMap.id ℝ (ℝ × ℝ)).prod (ContinuousAffineMap.const ℝ (ℝ × ℝ) t))
  let G : V3 →ᴬ[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap
  have hF (z : ℝ × ℝ) : F z=H.symm (z,t) := rfl
  have hG (x : V3) : G x=(H x).1 := rfl
  have hleft : Function.LeftInverse G F := by intro z; rw [hG,hF,H.apply_symm_apply]
  have hright : LeftInvOn F G {x | (H x).2=t} := by
    intro x hx
    rw [hF,hG,←hx]
    exact H.symm_apply_apply x
  have hplane : MapsTo F univ {x | (H x).2=t} := by
    intro z _
    change (H (F z)).2=t
    rw [hF,H.apply_symm_apply]
  obtain ⟨n,L,D,hLi,hL,hD,hDsub,hcontact,hrem⟩ :=
    exists_innermost_disk_in_convex_section_with_polygon hpres hJcv
      hinside F G hleft hright hplane hne
  have hDQ : D⊆Q.target := (fun x hx => hJQ (interior_subset (hDsub hx).1))
  have hrQ : L.boundary ℝ⊆Q.target := hD.1.trans hDQ
  have hphysical (x : V3) (hx : x∈Q.target) :
      Q.symm x∈⋃i,S i ↔ x∈Q '' ((⋃i,S i)∩Q.source) := by
    constructor
    · exact fun h => ⟨Q.symm x,⟨h,Q.map_target hx⟩,Q.right_inv hx⟩
    · rintro ⟨y,hy,hyx⟩
      rw [←hyx,Q.left_inv hy.2]
      exact hy.1
  have hD2 := hD.model_equiv (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  have hconn := hD2.isConnected_boundary_two.image Q.symm (Q.continuousOn_symm.mono hrQ)
  obtain ⟨i,hri,_⟩ := exists_unique_sphere_member_of_preconnected S s hdis
    hconn.nonempty hconn.isPreconnected (by
      rintro _ ⟨x,hx,rfl⟩
      exact (hphysical x (hrQ hx)).mpr (hcontact.symm.subset hx).2)
  have hmember : D∩Q '' (S i∩Q.source)=L.boundary ℝ := by
    apply Subset.antisymm
    · exact fun x hx => hcontact.subset ⟨hx.1,
        image_mono (inter_subset_inter_left _ (subset_iUnion S i)) hx.2⟩
    · intro x hx
      exact ⟨hD.1 hx,Q.symm x,⟨hri ⟨x,hx,rfl⟩,Q.map_target (hrQ hx)⟩,Q.right_inv (hrQ hx)⟩
  let others := ⋃j : {j : κ // j≠i},S j.val
  have hOthers : IsClosed others := isClosed_iUnion_of_finite fun j => (s j.val).isCompact.isClosed
  have hDother (x : V3) (hx : x∈D) : Q.symm x∉others := by
    intro hh
    obtain ⟨j,hj⟩ := mem_iUnion.mp hh
    have hxl : x∈L.boundary ℝ := hcontact.subset ⟨hx,
      (hphysical x (hDQ hx)).mp (mem_iUnion.mpr ⟨j.val,hj⟩)⟩
    exact disjoint_left.mp (hdis (Ne.symm j.property)) (hri ⟨x,hxl,rfl⟩) hj
  let rest := ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t})\L.boundary ℝ
  let U := (interior J.space\rest)∩(Q.target∩Q.symm ⁻¹' othersᶜ)
  have hU : IsOpen U := (isOpen_interior.sdiff hrem.isClosed).inter
    (Q.symm.isOpen_inter_preimage hOthers.isOpen_compl)
  have hDU : D⊆U := fun x hx =>
    ⟨⟨(hDsub hx).1,fun hc => hc.2 (hcontact.subset ⟨hx,hc.1.1.1⟩)⟩,hDQ hx,hDother x hx⟩
  have hUJ : U⊆interior J.space := fun x hx => hx.1.1
  refine ⟨i,n,L,D,U,hLi,hL,hD,hDsub,hcontact,hmember,hrem,hU,hDU,hUJ,?_,?_,?_⟩
  · intro j hji
    apply disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ hxj
    exact hx.2.2 (mem_iUnion.mpr ⟨⟨j,hji⟩,hxj⟩)
  · intro x hx
    constructor
    · intro h
      exact ⟨hri ⟨x,h,rfl⟩,(hDsub (hD.1 h)).2⟩
    · intro h
      by_contra hn
      exact hx.1.2 ⟨⟨⟨(hphysical x hx.2.1).mp (mem_iUnion.mpr ⟨i,h.1⟩),
        interior_subset hx.1.1⟩,h.2⟩,hn⟩
  · intro w hw O hO hwO
    have hwsection : w∈(Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t} :=
      ⟨⟨(hcontact.symm.subset hw).2,interior_subset (hDsub (hD.1 hw)).1⟩,(hDsub (hD.1 hw)).2⟩
    obtain ⟨B,hwB,hBO,hBw,hB,hBi,hBS,hBA⟩ := hcross w hwsection (O∩U)
      (hO.inter hU) ⟨hwO,hDU (hD.1 hw)⟩
    refine ⟨B,hwB,fun x hx => ⟨(hBO hx).1.1,(hBO hx).2⟩,hBw,hB,hBi,?_,hBA⟩
    intro x hx
    have hmem : Q.symm x∈S i ↔ Q.symm x∈⋃j,S j := by
      constructor
      · exact fun hh => mem_iUnion.mpr ⟨i,hh⟩
      · intro hh
        obtain ⟨j,hj⟩ := mem_iUnion.mp hh
        by_cases hji : j=i
        · exact hji ▸ hj
        · exact ((hBO hx).1.2.2.2 (mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)).elim
    exact hmem.trans (hBS x hx)


theorem exists_sphere_family_cocore_innermost_disk
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (s : ∀i,ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀i,(e i).symm.trans Q∈piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ V3) (hJ : J.faces.Finite) (hJQ : J.space⊆Q.target)
    (hJcv : Convex ℝ J.space) (H : V3 ≃ᴬ[ℝ] P3) {a b : ℝ} (hab : a<b)
    (hband : ∀x∈Q '' ((⋃i,S i)∩Q.source)∩J.space,(H x).2∈Ioo a b → x∈interior J.space) :
    ∃t∈Ioo a b,
      HasDisjointPolygonPresentation ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t}) ∧
      (((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t}=∅) ∨
        ∃(i : κ) (n : ℕ) (L : Polygon V3 (n+3)) (D U : Set V3),
          Function.Injective L ∧ L.HasSimplicialEdges ∧
          IsFinitePLBallPair (ℝ × ℝ) D (L.boundary ℝ) ∧
          D⊆interior J.space∩{x | (H x).2=t} ∧
          D∩Q '' ((⋃i,S i)∩Q.source)=L.boundary ℝ ∧
          D∩Q '' (S i∩Q.source)=L.boundary ℝ ∧
          IsCompact (((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t})\L.boundary ℝ) ∧
          IsOpen U ∧ D⊆U ∧ U⊆interior J.space ∧
          (∀j,j≠i → Disjoint (Q.symm '' U) (S j)) ∧
          (∀x∈U,x∈L.boundary ℝ ↔ Q.symm x∈S i ∧ (H x).2=t) ∧
          ∀w∈L.boundary ℝ,∀O : Set V3,IsOpen O → w∈O →
            ∃B : OpenPartialHomeomorph V3 P3,
              w∈B.source ∧ B.source⊆O∩interior J.space ∧ B w=0 ∧
              LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
              (∀x∈B.source,Q.symm x∈S i ↔ (B x).2=0) ∧
              ∀x∈B.source,(H x).2-t=(B x).1.1) := by
  let A : V3 →ᵃ[ℝ] ℝ :=
    ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp H.toContinuousAffineMap).toAffineMap
  obtain ⟨t,ht,_,hpres,hcross⟩ :=
    exists_sphere_family_regular_cocore_section S s hdis Q hQ J hJ hJQ A hab hband
  refine ⟨t,ht,hpres,?_⟩
  by_cases hempty : ((Q '' ((⋃i,S i)∩Q.source)∩J.space)∩{x | (H x).2=t})=∅
  · exact Or.inl hempty
  · exact Or.inr (exists_sphere_family_cocore_innermost_disk_at_height S s hdis Q J hJQ
      hJcv H t hpres (fun x hx => hband x hx.1 (hx.2 ▸ ht)) hcross
      (Set.nonempty_iff_ne_empty.mpr hempty))

end PoincareConjecture.M76

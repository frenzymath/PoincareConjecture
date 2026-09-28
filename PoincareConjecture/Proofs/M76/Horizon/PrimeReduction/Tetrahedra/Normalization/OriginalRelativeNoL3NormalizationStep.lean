import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalNondiskCapAnnulus
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalInteriorCapModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalCircleRepairedDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.SeparatedCapBoundaryDecrease
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.TotalBoundaryExcess
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.SelectedCircleGraphPosition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleSurgeryCofaceTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeFamilyMarkedExchange










set_option autoImplicit false
open Set Metric Geometry TriangularRoofModel
namespace PoincareConjecture.M76
universe u
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1/2 : ℝ)) (1/2)

private theorem selected_relative_normalization_geometry
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [T2Space X] [Finite κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) {R : Set X}
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (S : κ → Set X) (i : κ) (new : Bool → Set X)
    (sfull : ∀ j, ChartwisePLSphere e (circleSurgeryFamily S i new j))
    (hfull : Pairwise fun j k => Disjoint (circleSurgeryFamily S i new j)
      (circleSurgeryFamily S i new k))
    (hspace : ∀ j, circleSurgeryFamily S i new j ⊆ g '' K.space)
    (hinside : ∀ j, circleSurgeryFamily S i new j ⊆ interior R)
    (havoid : Disjoint (⋃ j, circleSurgeryFamily S i new j) (g '' K.vertices))
    (hfinite : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ j, circleSurgeryFamily S i new j) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ j a, a ∈ K.faces → a.card = 2 →
      HasOriginalEdgeCofaceCharts e (circleSurgeryFamily S i new j) K g a)
    (hposition : ∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s)
      (⋃ j, circleSurgeryFamily S i new j) g s.1 (A s))
    (hdecrease : ∀ selected : Set ({j : κ // j ≠ i} ⊕ Bool),
      totalTetrahedralBoundaryExcess K hK g (⋃ j ∈ selected, circleSurgeryFamily S i new j) <
        totalTetrahedralBoundaryExcess K hK g (⋃ j, S j)) (b : Bool) :
    let S' := selectedCircleSurgeryFamily S i new b
    Nonempty (∀ j, ChartwisePLSphere e (S' j)) ∧
      (∀ j, S' j ⊆ g '' K.space) ∧ (∀ j, S' j ⊆ interior R) ∧
      Pairwise (fun j k => Disjoint (S' j) (S' k)) ∧
      Disjoint (⋃ j, S' j) (g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card = 2 →
        ((⋃ j, S' j) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
      (∀ j a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S' j) K g a) ∧
      (∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ j, S' j) g s.1 (A s)) ∧
      Nat.card (Set.range S') = Nat.card κ ∧
      totalTetrahedralBoundaryExcess K hK g (⋃ j, S' j) <
        totalTetrahedralBoundaryExcess K hK g (⋃ j, S j) := by
  classical
  obtain ⟨hs,hd,havoid',hsub,hcard⟩ :=
    selectedCircleSurgeryFamily_geometry S i new b sfull hfull havoid
  refine ⟨hs,?_,?_,hd,havoid',?_,?_,?_,hcard,?_⟩
  · intro j
    rw [selectedCircleSurgeryFamily_eq_index]
    exact hspace _
  · intro j
    rw [selectedCircleSurgeryFamily_eq_index]
    exact hinside _
  · intro a ha ha2
    exact (hfinite a ha ha2).subset (inter_subset_inter_left _ hsub)
  · intro j a ha ha2
    rw [selectedCircleSurgeryFamily_eq_index]
    exact hcofaces _ a ha ha2
  · intro s
    exact (hposition s).selected_circle_surgery S i new b sfull hfull
  · have heq :
        (⋃ j ∈ Set.range (selectedCircleSurgeryIndex i b), circleSurgeryFamily S i new j) =
          ⋃ j, selectedCircleSurgeryFamily S i new b j := by
      ext x
      constructor
      · intro hx
        obtain ⟨j,hj⟩ := mem_iUnion.mp hx
        obtain ⟨⟨k,rfl⟩,hxk⟩ := mem_iUnion.mp hj
        exact mem_iUnion.mpr ⟨k,(selectedCircleSurgeryFamily_eq_index S i new b k).symm.subset hxk⟩
      · intro hx
        obtain ⟨j,hj⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨selectedCircleSurgeryIndex i b j,
          mem_iUnion.mpr ⟨⟨j,rfl⟩,(selectedCircleSurgeryFamily_eq_index S i new b j).subset hj⟩⟩
    rw [←heq]
    exact hdecrease _

theorem HasNoPuncturedSphereComponents.exists_original_relative_selected_normalization_step
    {E : Type u} {X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [MetricSpace X]
    [Finite κ] [DecidableEq κ]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s j, (e j).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hS : ∀ i, S i ⊆ g '' K.space)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (havoid : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedge : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {R Q₀ : Set X} (hR : IsCompact R) (hRPL : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hTR : g '' convexHull ℝ (t : Set E) ⊆ R)
    (hf : ∀ j, LocallyPiecewiseAffineOn (f ∘ (e j).symm) (e j).target)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (O₀ : κ → Set X) (W₀ : ∀ i, (S i × unitInterval) ≃ₜ closure (O₀ i))
    (hQ₀eq : Q₀ = R \ ⋃ i, O₀ i) (hQ₀ : IsCompact Q₀) (hQ₀PL : PLDomain e Q₀)
    (hO₀ : ∀ i, IsOpen (O₀ i)) (hCR₀ : ∀ i, closure (O₀ i) ⊆ interior R)
    (hdis₀ : Pairwise fun i j => Disjoint (closure (O₀ i)) (closure (O₀ j)))
    (hopen₀ : ∀ i z, (W₀ i z : X) ∈ O₀ i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter₀ : ∀ i z, (W₀ i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC₀ : ∀ i, S i ⊆ closure (O₀ i))
    (B₀ : κ × Bool → Set X) (sB₀ : ∀ j, ChartwisePLSphere e (B₀ j))
    (hB₀dis : Pairwise fun j k => Disjoint (B₀ j) (B₀ k))
    (hB₀sub : ∀ j, B₀ j ⊆ closure (O₀ j.1))
    (hfront₀ : frontier Q₀ = frontier R ∪ ⋃ j, B₀ j)
    (hno : HasNoPuncturedSphereComponents e f Q₀)
    (hpositive : boundaryComponentExcess (⋃ i, S i) (g '' convexHull ℝ (t : Set E))
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) ≠ 0) :
    ∃ (i : κ) (replacement : Bool → Set X) (b : Bool),
      let S' := selectedCircleSurgeryFamily S i replacement b
      Nonempty (∀ j, ChartwisePLSphere e (S' j)) ∧
      (∀ j, S' j ⊆ g '' K.space) ∧ (∀ j, S' j ⊆ interior R) ∧
      Pairwise (fun j k => Disjoint (S' j) (S' k)) ∧
      Disjoint (⋃ j, S' j) (g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card = 2 →
        ((⋃ j, S' j) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
      (∀ j a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S' j) K g a) ∧
      (∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ j, S' j) g s.1 (A s)) ∧
      Nat.card (Set.range S') = Nat.card κ ∧
      totalTetrahedralBoundaryExcess K hK g (⋃ j, S' j) <
        totalTetrahedralBoundaryExcess K hK g (⋃ j, S j) ∧
    ∃ (O : κ → Set X) (W : ∀ j, (S j × unitInterval) ≃ₜ closure (O j))
      (B : κ × Bool → Set X) (sB : ∀ j, ChartwisePLSphere e (B j)) (a : X),
      let restored := R \ ⋃ k : {k : κ // k ≠ i}, O k.val
      let C := connectedComponentIn restored a
      IsCompact (R \ ⋃ j, O j) ∧ PLDomain e (R \ ⋃ j, O j) ∧
      HasNoPuncturedSphereComponents e f (R \ ⋃ j, O j) ∧
      (∀ j, IsOpen (O j) ∧ IsCompact (closure (O j)) ∧
        IsConnected (closure (O j)) ∧ closure (O j) ⊆ interior R) ∧
      Pairwise (fun j k => Disjoint (closure (O j)) (closure (O k))) ∧
      (∀ j z, (W j z : X) ∈ O j ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
      (∀ j z, (W j z : X) ∈ S j ↔ (z.2 : ℝ) = 1/2) ∧
      (∀ j, S j ⊆ closure (O j)) ∧
      frontier (R \ ⋃ j, O j) = frontier R ∪ ⋃ j, B j ∧
      Pairwise (fun j k => Disjoint (B j) (B k)) ∧
      (∀ j, B j ⊆ closure (O j.1)) ∧
      IsCompact C ∧ IsConnected C ∧ PLDomain e C ∧ S i ⊆ interior C ∧
      closure (O i) ⊆ interior C ∧
    ∃ (U : Set X) (WU : U ≃ₜ (frontier (halfBall 1) ×ˢ Icc (0 : ℝ) 1 : Set (P3 × ℝ)))
      (σ : P3 × ℝ → X),
      PolyhedralPLInCharts e σ (frontier (halfBall 1) ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ z : (frontier (halfBall 1) ×ˢ Icc (0 : ℝ) 1 : Set (P3 × ℝ)),
        σ z = (WU.symm z : X)) ∧
      IsCompact U ∧ PLDomain e U ∧ U ⊆ interior C ∧
      replacement b ⊆ frontier U ∧
      (∀ x : U, (x : X) ∈ replacement b ↔
        (WU x : P3 × ℝ).2 = if b then (1 : ℝ) else 0) ∧
      HasNoPuncturedSphereComponents e f (C \ interior U) ∧
      HasNoPuncturedSphereComponents e f (restored \ interior U) := by
  classical
  let he := hRPL.compatible
  let T := convexHull ℝ (t : Set E)
  let F := intrinsicFrontier ℝ T
  have hTK : T ⊆ K.space := K.convexHull_subset_space ht
  obtain ⟨ball⟩ := exists_chartwisePLBall_image
    (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
    (ContinuousLinearEquiv.refl ℝ V3) hg hTK hgi
  have hFT : g '' F ⊆ g '' T := image_mono
    (intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed)
  have hFout : Disjoint (g '' F) (interior (g '' T)) := by
    rw [←ball.frontier_eq]
    exact disjoint_left.mpr (fun _ hx hy => hx.2 hy)
  obtain ⟨γ,hγ,C₀,hC₀,hC₀dis,hC₀whole,hselect,hcap⟩ :=
    exists_original_nondisk_cap_with_annulus he hRPL.cover K hK g hg hgi Q hQ A hmap hA
      S sS hS hdis havoid hedge hedges hposition ht ht4
  obtain ⟨c,hc,hcne⟩ := hselect hpositive
  obtain ⟨n,polygon,d,i,hPi,hPe,hd,hdT,hdF,hdS,hri,howner,hmove⟩ := hcap c hc hcne
  obtain ⟨H,ann,hH,hHi,hfix,hpres,hp,hpi,hcapT,hcapS,hdisrim,ha,hai,haS,haT,
      hain,houter,hinner,hrA,hqA,hcontact,holdside,hneighborhood,
      v,q,braw,raw,hv,hwhole,hinter,hrim,hraweq,hrawcap,hsideann,hotherann,hrside,hrdis,
      hD,hDF,hDimage,hDsub,hDother,hrawposition,hcomponent,hotherboundary,hnomerge,
      hcounts,houtsideOld⟩ := hmove univ isOpen_univ (subset_univ _)
  obtain ⟨ρ,hρ,rim,old,rimSide,point,hrims,hrimdis,hrimcover,hselectedrim,hrimside,hcount⟩ := hcounts
  let : Finite ρ := hρ
  obtain ⟨d',r',hd',hd'T,hdi,hri',hproperAll,hd'actual,hr'actual⟩ :=
    exists_original_finite_cap_model he K hK hg hgi hTK hd hp hpi
      (hcapT.trans interior_subset) hcapS
  have hrSi : g '' r' ⊆ S i := by
    rw [hri']
    rintro _ ⟨z,hz,rfl⟩
    exact (hpres i (g z)).mpr (hri ⟨z,hz,rfl⟩)
  let V := interior (g '' T) ∩ (⋃ k : {k : κ // k ≠ i}, S k.val)ᶜ
  have hV : IsOpen V := isOpen_interior.inter
    (isClosed_iUnion_of_finite (fun k : {k : κ // k ≠ i} => (sS k.val).isCompact.isClosed)).isOpen_compl
  have hd'V : g '' d' ⊆ V := by
    intro x hx
    refine ⟨hcapT (hdi.subset hx),?_⟩
    intro ho
    obtain ⟨k,hkx⟩ := mem_iUnion.mp ho
    have hr : x ∈ g '' r' := by
      rw [hri']
      exact hcapS.subset ⟨hdi.subset hx,mem_iUnion.mpr ⟨k.val,hkx⟩⟩
    exact disjoint_left.mp (hdis k.property) hkx (hrSi hr)
  obtain ⟨J₀,_,hJ₀,hJ₀s,_,_⟩ := hd'.exists_finite_carrier_and_rim_complexes
  have hgd' : PolyhedralPLInCharts e g d' := hJ₀s ▸
    hg.restrict_finite J₀ hJ₀ (hJ₀s.subset.trans (hd'T.trans hTK))
  have hg'd : InjOn g d' := hgi.mono (hd'T.trans hTK)
  obtain ⟨Qcut,B,sB,O,W,a,hQeq,hQc,hQPL,hnoQ,hO,hOdis,hW,hWcenter,hSC,hfront,hmarksdis,
      hBsub,hCc,hCconn,hCPL,hSiC,hOiC,
      L,Bopp,j,P,k,r,b,caps,U,WU,σ,hLc,hLPL,hLO,hjd,hjq,hP,hmark,hopen,hk,hkdis,hkcover,
      hcaps,hσ,hσval,hU,hUPL,hUsub,hUi,hcapU,hcapmark,hnoU,hnoGlobal⟩ :=
    hno.exists_relative_family_marked_noL3_exchange O₀ S W₀ hQ₀eq hQ₀ hQ₀PL hO₀ hCR₀ hdis₀
      hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ sS hdis hR hRPL hSR
      K g hf hg hgi hreal i hd' g hgd' hg'd
      (fun x hx => interior_mono hTR (hd'V hx).1)
      (by rw [hdi,hri']; exact hcapS) hrSi hV hd'V
  have hPint : MapsTo P.map (Disk ×ˢ I) (interior (g '' T)) :=
    fun _ hz => (hP hz).1.1.1
  have hPavoid : MapsTo P.map (Disk ×ˢ I) (⋃ k : {k : κ // k ≠ i}, S k.val)ᶜ :=
    fun _ hz => (hP hz).1.1.2
  have hsmall : Disk ×ˢ J ⊆ Disk ×ˢ I := by
    rintro z ⟨hz,ht⟩
    exact ⟨hz,by constructor <;> linarith [ht.1,ht.2]⟩
  have hband : P.map '' (Rim ×ˢ J) ⊆ S i := by
    rintro _ ⟨z,hz,rfl⟩
    exact (hmark z (hsmall ⟨sphere_subset_closedBall hz.1,hz.2⟩)).mpr hz.1
  have hcenter : P.map '' (Rim ×ˢ {(0 : ℝ)}) = (sS i).map '' q := by
    rw [hrim,←hri',←hjq]
    apply Subset.antisymm
    · rintro _ ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
      rw [show u = 0 from hu,P.central z (sphere_subset_closedBall hz)]
      exact mem_image_of_mem j hz
    · rintro _ ⟨z,hz,rfl⟩
      exact ⟨(z,0),⟨hz,rfl⟩,P.central z (sphere_subset_closedBall hz)⟩
  have hmarks a : IsFinitePLBallPair P2 (k a) (r a) ∧ k a ⊆ sphere (0 : V3) 1 ∧
      (sS i).map '' r a = P.capRimSet a ∧
      ((sS i).map '' k a) ∩ P.closedStrip = (sS i).map '' r a :=
    ⟨(hk a).1,(hk a).2.1,(hk a).2.2.2.1,(hk a).2.2.2.2⟩
  obtain ⟨side,hside,htransport⟩ := P.exists_original_circle_repaired_disk_transport
    (sS i) he K hK hg hgi hTK hPint (hS i) v hv hwhole hinter hband hcenter
    hopen k r hmarks hkcover
  have hret a : (sS i).map '' k a ⊆ S i := by
    rintro _ ⟨z,hz,rfl⟩
    rw [(sS i).map_eq ⟨z,(hk a).2.1 hz⟩]
    exact ((sS i).parametrization ⟨z,(hk a).2.1 hz⟩).property
  have hretcontact a : ((sS i).map '' k a) ∩ P.closedStrip = P.capRimSet a :=
    (hmarks a).2.2.2.trans (hmarks a).2.2.1
  let replacement := fun a => ((sS i).map '' k a) ∪ P.capDisk a
  have hstripint : P.closedStrip ⊆ interior (g '' T) := by
    rintro _ ⟨z,hz,rfl⟩
    exact hPint (hsmall hz)
  have hstripclosed : IsClosed P.closedStrip :=
    (P.isCompact_closed_strip (by norm_num : (1/2 : ℝ) ≤ 1)).isClosed
  have hstripface (s) (hs : s ∈ K.faces) (hscard : s.card ≤ 3) :
      Disjoint P.closedStrip (g '' convexHull ℝ (s : Set E)) :=
    (original_tetrahedron_interior_disjoint_face K hg hgi ht ht4 hs hscard).mono_left hstripint
  have hcapstrip (b) : P.capDisk b ⊆ P.closedStrip := by
    rintro _ ⟨z,hz,rfl⟩
    refine ⟨z,⟨hz.1,?_⟩,rfl⟩
    have hzt : z.2 = if b then (1/2 : ℝ) else -(1/2) := hz.2
    rw [hzt]
    cases b <;> norm_num
  have houtside : (replacement true ∪ replacement false) \ P.closedStrip = S i \ P.closedStrip := by
    ext x
    constructor
    · rintro ⟨hx,hxoff⟩
      refine ⟨?_,hxoff⟩
      rcases hx with (hx | hx) | (hx | hx)
      · exact hret true hx
      · exact (hxoff (hcapstrip true hx)).elim
      · exact hret false hx
      · exact (hxoff (hcapstrip false hx)).elim
    · rintro ⟨hx,hxoff⟩
      refine ⟨?_,hxoff⟩
      rcases hkcover.symm.subset hx with (ht | hf) | hbandx
      · exact Or.inl (Or.inl ht)
      · exact Or.inr (Or.inl hf)
      · obtain ⟨z,hz,rfl⟩ := hbandx
        exact (hxoff ⟨z,⟨sphere_subset_closedBall hz.1,hz.2⟩,rfl⟩).elim
  have hfulloutside :
      (⋃ a, Sum.elim (fun k : {k : κ // k ≠ i} => S k.val) replacement a) \ P.closedStrip =
        (⋃ j, S j) \ P.closedStrip := by
    ext x
    constructor
    · rintro ⟨hx,hxoff⟩
      obtain ⟨a,ha⟩ := mem_iUnion.mp hx
      refine ⟨?_,hxoff⟩
      cases a with
      | inl k => exact mem_iUnion.mpr ⟨k.val,ha⟩
      | inr b =>
        have hxnew : x ∈ replacement true ∪ replacement false := by
          cases b
          · exact Or.inr ha
          · exact Or.inl ha
        exact mem_iUnion.mpr ⟨i,(houtside.subset ⟨hxnew,hxoff⟩).1⟩
    · rintro ⟨hx,hxoff⟩
      obtain ⟨j,hjx⟩ := mem_iUnion.mp hx
      refine ⟨?_,hxoff⟩
      by_cases hji : j = i
      · subst j
        rcases (houtside.symm.subset ⟨hjx,hxoff⟩).1 with ht | hf
        · exact mem_iUnion.mpr ⟨Sum.inr true,ht⟩
        · exact mem_iUnion.mpr ⟨Sum.inr false,hf⟩
      · exact mem_iUnion.mpr ⟨Sum.inl ⟨j,hji⟩,hjx⟩
  have hnewdis := P.separated_cap_family_pairwise_disjoint S i hdis
    (fun a => (sS i).map '' k a) hret hkdis hretcontact hPavoid
  have hcapsdis : Disjoint (replacement true) (replacement false) :=
    hnewdis (show (Sum.inr true : {k : κ // k ≠ i} ⊕ Bool) ≠ Sum.inr false by simp)
  have hdecrease := P.selected_separated_cap_boundary_excess_lt K hK hg hgi hTK hFT hFout
    S i (fun k => (sS k).isCompact.isClosed) hdis hS
    (fun a => (sS i).map '' v a) (fun a => (sS i).map '' k a) hret hkdis
    hretcontact caps hPint hPavoid side hside
    (fun a => by
      obtain ⟨hAi,hBi,f,hf,hfi,hfim,hffix,hfsupport,hfT,hG,hrest⟩ := htransport a
      exact ⟨hAi,hBi,f,hfsupport,hG⟩) rim rimSide point
    (fun a => (hrims a).1) (fun a => (hrims a).2.1) hrimdis hrimcover hrimside
    (fun a => (hrims a).2.2.2) (by rw [hjd,hdi]; exact hcount)
  have sfull : ∀ j, ChartwisePLSphere e (circleSurgeryFamily S i replacement j) :=
    fun j => by cases j with | inl j => exact sS j.val | inr b => exact caps b
  have hspace : ∀ j, circleSurgeryFamily S i replacement j ⊆ g '' K.space := by
    intro j
    cases j with
    | inl j => exact hS j.val
    | inr a => exact (htransport a).2.1.symm.subset.trans (image_mono inter_subset_left)
  have hinside : ∀ j, circleSurgeryFamily S i replacement j ⊆ interior R := by
    intro j x hx
    cases j with
    | inl j => exact hSR j.val hx
    | inr a =>
      rcases hx with hx | hx
      · exact hSR i (hret a hx)
      · obtain ⟨z,hz,rfl⟩ := hx
        exact interior_mono hTR (hPint (OriginalDiskProduct.cap_source_subset a hz))
  have hposition' : ∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s)
      (⋃ j, circleSurgeryFamily S i replacement j) g s.1 (A s) := by
    intro s
    exact (hposition s).of_equal_off_closed hstripclosed
      (hstripface s.1 s.2.1 (by omega)) hfulloutside
  have havoid' : Disjoint (⋃ j, circleSurgeryFamily S i replacement j) (g '' K.vertices) := by
    apply disjoint_left.mpr
    rintro x hx ⟨z,hz,rfl⟩
    have hzface : ({z} : Finset E) ∈ K.faces := hz
    have hzcarrier : g z ∈ g '' convexHull ℝ (({z} : Finset E) : Set E) := by
      apply mem_image_of_mem
      simp
    have hzoff : g z ∉ P.closedStrip := fun h => disjoint_left.mp
      (hstripface {z} hzface (by simp)) h hzcarrier
    exact disjoint_left.mp havoid (hfulloutside.subset ⟨hx,hzoff⟩).1 ⟨z,hz,rfl⟩
  have hfinite' : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ j, circleSurgeryFamily S i replacement j) ∩ (g '' convexHull ℝ (a : Set E))).Finite := by
    intro a ha ha2
    apply (hedges a ha ha2).subset
    intro x hx
    have hxoff : x ∉ P.closedStrip := fun h => disjoint_left.mp
      (hstripface a ha (by omega)) h hx.2
    exact ⟨(hfulloutside.subset ⟨hx.1,hxoff⟩).1,hx.2⟩
  have hcofaces' : ∀ j a, a ∈ K.faces → a.card = 2 →
      HasOriginalEdgeCofaceCharts e (circleSurgeryFamily S i replacement j) K g a := by
    intro j a ha ha2
    cases j with
    | inl j => exact hedge j.val a ha ha2
    | inr b =>
      have hpair := (hedge i a ha ha2).surgery_pair_of_disjoint_support hstripclosed
        (caps true).isCompact (caps false).isCompact hcapsdis
        (hstripface a ha (by omega)) houtside
      cases b
      · exact hpair.2
      · exact hpair.1
  have htotal : ∀ selected : Set ({k : κ // k ≠ i} ⊕ Bool),
      totalTetrahedralBoundaryExcess K hK g
        (⋃ j ∈ selected, circleSurgeryFamily S i replacement j) <
      totalTetrahedralBoundaryExcess K hK g (⋃ j, S j) := by
    intro selected
    apply totalTetrahedralBoundaryExcess_lt_of_supported_replacement he K hK g hg hgi
      Q A hmap hA S sS hS hdis havoid hposition ht ht4
      (circleSurgeryFamily S i replacement) sfull hnewdis ?_ selected (hdecrease selected)
    ext x
    constructor
    · intro hx
      exact ⟨(hfulloutside.subset ⟨hx.1,fun h => hx.2 (hstripint h)⟩).1,hx.2⟩
    · intro hx
      exact ⟨(hfulloutside.symm.subset ⟨hx.1,fun h => hx.2 (hstripint h)⟩).1,hx.2⟩
  obtain ⟨hs',hspace',hinside',hdis',hav',hfin',hcof',hpos',hcard',htotal'⟩ :=
    selected_relative_normalization_geometry K hK g Q A S i replacement sfull hnewdis
      hspace hinside havoid' hfinite' hcofaces' hposition' htotal b
  refine ⟨i,replacement,b,hs',hspace',hinside',hdis',hav',hfin',hcof',hpos',hcard',htotal',
    O,W,B,sB,a,?_,?_,?_,hO,hOdis,hW,hWcenter,hSC,?_,hmarksdis,hBsub,
    hCc,hCconn,hCPL,hSiC,hOiC,U,WU,σ,hσ,hσval,hU,hUPL,hUi,hcapU,hcapmark,hnoU,hnoGlobal⟩
  all_goals rw [←hQeq]
  · exact hQc
  · exact hQPL
  · exact hnoQ
  · exact hfront

end PoincareConjecture.M76

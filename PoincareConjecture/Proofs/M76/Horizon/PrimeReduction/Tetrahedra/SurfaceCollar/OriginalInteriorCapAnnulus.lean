import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalInwardDiskSides
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.InwardDiskNesting
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.MovedDiskAnnulus
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalInwardCrossing
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalAnnulusNeighborhood










set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_strictly_interior_cap_with_annulus
    {E X ι κ ρ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    [Finite κ] [Finite ρ]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s j, (e j).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedge : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (n : ρ → ℕ) (P : ∀ j, Polygon E (n j + 3))
    (hP : ∀ j, (P j).HasSimplicialEdges) (hPi : ∀ j, Function.Injective (P j))
    (hPT : ∀ j, (P j).boundary ℝ ⊆ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)))
    (hPdis : Pairwise fun j k => Disjoint (g '' (P j).boundary ℝ) (g '' (P k).boundary ℝ))
    (hfront : (⋃ j, g '' (P j).boundary ℝ) =
      (⋃ i, S i) ∩ frontier (g '' convexHull ℝ (t : Set E)))
    (j : ρ) (i : κ) (hPS : g '' (P j).boundary ℝ ⊆ S i)
    {d r : Set E} (hd : IsFinitePLBallPair P2 d r)
    (hdT : d ⊆ convexHull ℝ (t : Set E))
    (hdfront : d ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = r)
    (hdS : d ∩ g ⁻¹' (⋃ i, S i) = r) (hrP : r = (P j).boundary ℝ)
    {V : Set X} (hV : IsOpen V) (hrV : g '' r ⊆ V) :
    ∃ (H : X ≃ₜ X) (a : P2 → X),
      (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      EqOn H id Vᶜ ∧ (∀ i x, H x ∈ S i ↔ x ∈ S i) ∧
      PolyhedralPLInCharts e (H ∘ g) d ∧ InjOn (H ∘ g) d ∧
      (H ∘ g) '' d ⊆ interior (g '' convexHull ℝ (t : Set E)) ∧
      ((H ∘ g) '' d) ∩ (⋃ i, S i) = (H ∘ g) '' r ∧
      Disjoint ((H ∘ g) '' r) (g '' r) ∧
      PolyhedralPLInCharts e a Ann ∧ InjOn a Ann ∧
      a '' Ann ⊆ S i ∩ V ∧
      a '' Ann ⊆ g '' convexHull ℝ (t : Set E) ∧
      (a '' Ann) \ (g '' r) ⊆ interior (g '' convexHull ℝ (t : Set E)) ∧
      (∀ x ∈ Ann, a x ∈ g '' r ↔ depth 8 x = -1) ∧
      (∀ x ∈ Ann, a x ∈ (H ∘ g) '' r ↔ depth 8 x = 1) ∧
      g '' r ⊆ a '' Ann ∧ (H ∘ g) '' r ⊆ a '' Ann ∧
      ((H ∘ g) '' d) ∩ (a '' Ann) = (H ∘ g) '' r ∧
      (∃ (f : P2 → X) (F : Set X),
        PolyhedralPLInCharts e f (closedBall (0 : P2) 1) ∧
        InjOn f (closedBall (0 : P2) 1) ∧
        MapsTo f (closedBall (0 : P2) 1) (S i) ∧
        f '' sphere (0 : P2) 1 = g '' r ∧ IsClosed F ∧
        (f '' closedBall (0 : P2) 1) ∪ F = S i ∧
        (f '' closedBall (0 : P2) 1) ∩ F = g '' r ∧
        H '' (f '' closedBall (0 : P2) 1) ⊆
          (f '' closedBall (0 : P2) 1) \ (g '' r) ∧
        a '' Ann = (f '' closedBall (0 : P2) 1) \
          (H '' (f '' (closedBall (0 : P2) 1 \ sphere (0 : P2) 1))) ∧
        ∀ C : Set X, IsPreconnected C → C ⊆ S i →
          C ⊆ g '' convexHull ℝ (t : Set E) → (C ∩ g '' r).Nonempty →
          C ⊆ f '' closedBall (0 : P2) 1) ∧
      ∃ U : Set X, IsOpen U ∧ S i ∩ U = a '' interior Ann ∧
        Disjoint U ((H ∘ g) '' d) ∧
        U ⊆ V ∩ interior (g '' convexHull ℝ (t : Set E)) := by
  classical
  let T := g '' convexHull ℝ (t : Set E)
  have hTK := K.convexHull_subset_space ht
  have hTc : IsClosed T :=
    ((t.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (hg.continuousOn.mono hTK)).isClosed
  have hPK (k) : (P k).boundary ℝ ⊆ K.space :=
    (hPT k).trans ((intrinsicFrontier_subset
      (t.finite_toSet.isCompact_convexHull ℝ).isClosed).trans hTK)
  obtain ⟨x,hx,hxout⟩ := original_polygon_two_sided_accumulation K hK g hg hgi Q A hmap hA
    S sS hdis hedges hposition ht ht4 (P j) (hPi j) (hPT j) i hPS
  have hinward : ((g '' (P j).boundary ℝ) ∩ closure (S i ∩ interior T)).Nonempty := ⟨x,hx⟩
  have houtward : ((g '' (P j).boundary ℝ) ∩ closure (S i ∩ Tᶜ)).Nonempty := ⟨x,hx.1,hxout⟩
  obtain ⟨b,f,F,hb,hb1,hf,hfi,hfS,hfr,hF,hwhole,hinter,hfV,hfT,hfin,hconfine⟩ :=
    (sS i).exists_original_inward_disk_with_closed_complement he K hg hgi
      n P hP hPi hPK hPdis hTc hfront (subset_iUnion S i) j hPS hV
      (by simpa only [hrP] using hrV) hinward
  have hfr' : f '' sphere (0 : P2) 1 = g '' r := by rwa [hrP]
  have hrfront : f '' sphere (0 : P2) 1 ⊆ frontier T := by
    rw [hfr]
    exact fun _ hx => (hfront.subset (mem_iUnion.mpr ⟨j,hx⟩)).2
  obtain ⟨O,hO,hrO,hOV,hcore,hnest⟩ := exists_inward_disk_nesting_support
    hf.continuousOn hfi hF hwhole hinter hrfront hb hb1 hfT hV (hfr'.subset.trans hrV)
  obtain ⟨H,hH,hHi,hfix,hHS,hHg,hHgi,hcap,hcontact,_,hdisrim,hin⟩ :=
    exists_original_strictly_interior_cap he hcover K hK g hg hgi Q hQ A hmap hA
      S sS hdis hSV hedge hposition ht ht4 hd hdT hdfront hdS hO
      (hfr'.symm.subset.trans hrO)
  have hrH : H '' (f '' sphere (0 : P2) 1) = (H ∘ g) '' r := by
    rw [hfr',image_image]
    rfl
  have hrin : H '' (f '' sphere (0 : P2) 1) ⊆ interior T := by
    rw [hrH]
    exact (image_mono hd.1).trans hcap
  have hnested := hnest H hfix (hHS i) hin hrin
  have hunit : IsFinitePLBallPair P2 (closedBall (0 : P2) 1) (sphere (0 : P2) 1) := by
    have h := CoordinateHalfBoxes.base_ballPair (by norm_num : (0 : ℝ) < 1)
    have hbase : CoordinateHalfBoxes.base 1 = closedBall (0 : P2) 1 := by
      ext x
      simp only [CoordinateHalfBoxes.base,mem_prod,mem_Icc,mem_closedBall,
        dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
    have hfront := h.frontier_eq_of_finrank_eq rfl
    rw [hbase,frontier_closedBall _ one_ne_zero] at hfront
    rwa [hbase,←hfront] at h
  obtain ⟨a,ha,hai,haimage,haold,hanew⟩ :=
    exists_original_moved_disk_annulus he hcover hunit hf hfi H hH hnested
  have hashell : a '' Ann ⊆ f '' {x : P2 | ‖x‖ ∈ Icc b 1} := by
    rw [haimage]
    exact moved_disk_annulus_subset_shell hb1 hcore H hfix
  have haS : a '' Ann ⊆ S i := by
    rw [haimage]
    exact sdiff_subset.trans (image_subset_iff.mpr hfS)
  have hold : f '' sphere (0 : P2) 1 ⊆ a '' Ann := by
    rw [haimage]
    intro x hx
    refine ⟨image_mono sphere_subset_closedBall hx,?_⟩
    intro hm
    exact (hnested ((image_mono (image_mono sdiff_subset)) hm)).2 hx
  have hnew : H '' (f '' sphere (0 : P2) 1) ⊆ a '' Ann := by
    rw [haimage]
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨(hnested (mem_image_of_mem H (image_mono sphere_subset_closedBall hx))).1,?_⟩
    rintro ⟨y,⟨z,hz,rfl⟩,hy⟩
    obtain ⟨w,hw,hwx⟩ := hx
    have hzw := hfi hz.1 (sphere_subset_closedBall hw)
      ((H.injective hy).trans hwx.symm)
    exact hz.2 (hzw.symm ▸ hw)
  obtain ⟨U0,hU0,hU0S,_,hU0new⟩ := exists_original_moved_annulus_open_neighborhood
    (isCompact_closedBall (0 : P2) 1) sphere_subset_closedBall hf.continuousOn
    hF hwhole hinter H haimage haold hanew
  let U := ((U0 ∩ V) ∩ interior T) ∩ ((H ∘ g) '' d)ᶜ
  have hU : IsOpen U := ((hU0.inter hV).inter isOpen_interior).inter
    (hd.isCompact.image_of_continuousOn hHg.continuousOn).isClosed.isOpen_compl
  have hAnnU : a '' interior Ann ⊆ U := by
    intro x hx
    have hx0 := hU0S.symm.subset hx
    have hxA := image_mono interior_subset hx
    have hxnotold : x ∉ g '' r := by
      obtain ⟨z,hz,rfl⟩ := hx
      have hzA := interior_subset hz
      have hdepth : -1 < depth 8 z := by
        rw [interior_squareAnnulus (by norm_num : (2 : ℝ) * 1 < 8)] at hz
        exact hz.1
      intro hr
      have h := (haold z hzA).mp (hfr'.symm.subset hr)
      linarith
    refine ⟨⟨⟨hx0.2,hfV (hashell hxA)⟩,
      hfin ⟨hashell hxA,fun h => hxnotold (hfr'.subset h)⟩⟩,?_⟩
    intro hcapx
    exact disjoint_left.mp hU0new hx0.2
      (hrH.symm.subset (hcontact.subset ⟨hcapx,(subset_iUnion S i) (haS hxA)⟩))
  have hUS : S i ∩ U = a '' interior Ann := by
    apply Subset.antisymm
    · exact fun x hx => hU0S.subset ⟨hx.1,hx.2.1.1.1⟩
    · exact fun x hx => ⟨(hU0S.symm.subset hx).1,hAnnU hx⟩
  refine ⟨H,a,hH,hHi,(fun x hx => hfix (fun h => hx (hOV h))),hHS,
    hHg,hHgi,hcap,hcontact,hdisrim,ha,hai,
    (fun x hx => ⟨haS hx,hfV (hashell hx)⟩),hashell.trans hfT,?_,?_,?_,?_,?_,?_,?_,
    U,hU,hUS,disjoint_left.mpr (fun _ hx hc => hx.2 hc),
    (fun _ hx => ⟨hx.1.1.2,hx.1.2⟩)⟩
  · intro x hx
    exact hfin ⟨hashell hx.1,fun hr => hx.2 (hfr'.subset hr)⟩
  · simpa only [hfr'] using haold
  · simpa only [hrH] using hanew
  · exact hfr'.symm.subset.trans hold
  · exact hrH.symm.subset.trans hnew
  · apply Subset.antisymm
    · intro x hx
      exact hcontact.subset ⟨hx.1,(subset_iUnion S i) (haS hx.2)⟩
    · intro x hx
      exact ⟨image_mono hd.1 hx,hnew (hrH.symm.subset hx)⟩
  · refine ⟨f,F,hf,hfi,hfS,hfr',hF,hwhole,?_,?_,haimage,?_⟩
    · exact hinter.trans hfr'
    · simpa only [hfr'] using hnested
    · simpa only [←hrP] using hconfine houtward

end PoincareConjecture.M76

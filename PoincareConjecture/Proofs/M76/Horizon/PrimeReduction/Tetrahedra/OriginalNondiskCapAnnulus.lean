import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalNondiskContactDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalInteriorCapAnnulus
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalAnnularCapSide
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalFaceAvoidance
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.CircleSurgeryGraph
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.MovedDiskSphereSide
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.RepairedDiskComponent
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.AnnulusConnected
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalOneBoundaryRecognition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.RawCircleBoundaryCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.BoundaryComponentExcess
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.PositiveExcessPiece

set_option autoImplicit false
universe u
open Set Geometry Metric PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_nondisk_cap_with_annulus
    {E : Type u} {X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
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
    (hS : ∀ i, S i ⊆ g '' K.space)
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (havoid : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedge : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hposition : ∀ s,
      InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4) :
    ∃ γ : Type u, Finite γ ∧ ∃ C : γ → SimplicialComplex ℝ E,
      (∀ c, (C c).faces.Finite ∧ IsConnected (C c).space ∧
        (C c).space ⊆ convexHull ℝ (t : Set E)) ∧
      Pairwise (fun c d => Disjoint (C c).space (C d).space) ∧
      (⋃ c, (C c).space) = convexHull ℝ (t : Set E) ∩ g ⁻¹' (⋃ i, S i) ∧
      let F := intrinsicFrontier ℝ (convexHull ℝ (t : Set E))
      let disk := fun c => IsFinitePLBallPair P2 (C c).space ((C c).space ∩ F)
      (boundaryComponentExcess (⋃ j, S j) (g '' convexHull ℝ (t : Set E)) (g '' F) ≠ 0 →
        ∃ c, ¬ disk c ∧ ((C c).space ∩ F).Nonempty) ∧
      ∀ c, ¬ disk c → ((C c).space ∩ F).Nonempty →
        ∃ (n : ℕ) (P : Polygon E (n + 3)) (d : Set E) (i : κ),
          Function.Injective P ∧ P.HasSimplicialEdges ∧
          IsFinitePLBallPair P2 d (P.boundary ℝ) ∧
          d ⊆ convexHull ℝ (t : Set E) ∧ d ∩ F = P.boundary ℝ ∧
          d ∩ g ⁻¹' (⋃ i, S i) = P.boundary ℝ ∧ g '' P.boundary ℝ ⊆ S i ∧
          (∃ c', ¬ disk c' ∧ P.boundary ℝ ⊆ (C c').space) ∧
          ∀ V : Set X, IsOpen V → g '' P.boundary ℝ ⊆ V →
            ∃ (H : X ≃ₜ X) (a : P2 → X),
              (∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
                piecewiseAffineGroupoid V3) ∧
              (∀ i j, (e i).symm.trans (H.symm.toOpenPartialHomeomorph.trans (e j)) ∈
                piecewiseAffineGroupoid V3) ∧
              EqOn H id Vᶜ ∧ (∀ j x, H x ∈ S j ↔ x ∈ S j) ∧
              PolyhedralPLInCharts e (H ∘ g) d ∧ InjOn (H ∘ g) d ∧
              (H ∘ g) '' d ⊆ interior (g '' convexHull ℝ (t : Set E)) ∧
              ((H ∘ g) '' d) ∩ (⋃ j, S j) = (H ∘ g) '' P.boundary ℝ ∧
              Disjoint ((H ∘ g) '' P.boundary ℝ) (g '' P.boundary ℝ) ∧
              PolyhedralPLInCharts e a Ann ∧ InjOn a Ann ∧
              a '' Ann ⊆ S i ∩ V ∧ a '' Ann ⊆ g '' convexHull ℝ (t : Set E) ∧
              (a '' Ann) \ (g '' P.boundary ℝ) ⊆ interior (g '' convexHull ℝ (t : Set E)) ∧
              (∀ x ∈ Ann, a x ∈ g '' P.boundary ℝ ↔ depth 8 x = -1) ∧
              (∀ x ∈ Ann, a x ∈ (H ∘ g) '' P.boundary ℝ ↔ depth 8 x = 1) ∧
              g '' P.boundary ℝ ⊆ a '' Ann ∧ (H ∘ g) '' P.boundary ℝ ⊆ a '' Ann ∧
              ((H ∘ g) '' d) ∩ (a '' Ann) = (H ∘ g) '' P.boundary ℝ ∧
              (∃ (f : P2 → X) (F : Set X),
                PolyhedralPLInCharts e f (closedBall (0 : P2) 1) ∧
                InjOn f (closedBall (0 : P2) 1) ∧
                MapsTo f (closedBall (0 : P2) 1) (S i) ∧
                f '' sphere (0 : P2) 1 = g '' P.boundary ℝ ∧ IsClosed F ∧
                (f '' closedBall (0 : P2) 1) ∪ F = S i ∧
                (f '' closedBall (0 : P2) 1) ∩ F = g '' P.boundary ℝ ∧
                H '' (f '' closedBall (0 : P2) 1) ⊆
                  (f '' closedBall (0 : P2) 1) \ (g '' P.boundary ℝ) ∧
                a '' Ann = (f '' closedBall (0 : P2) 1) \
                  (H '' (f '' (closedBall (0 : P2) 1 \ sphere (0 : P2) 1))) ∧
                ∀ C : Set X, IsPreconnected C → C ⊆ S i →
                  C ⊆ g '' convexHull ℝ (t : Set E) →
                  (C ∩ g '' P.boundary ℝ).Nonempty → C ⊆ f '' closedBall (0 : P2) 1) ∧
              (∃ U : Set X, IsOpen U ∧ S i ∩ U = a '' interior Ann ∧
                Disjoint U ((H ∘ g) '' d) ∧
                U ⊆ V ∩ interior (g '' convexHull ℝ (t : Set E))) ∧
              let D := convexHull ℝ (t : Set E) ∩
                g ⁻¹' (((H ∘ g) '' d) ∪ (a '' Ann))
              ∃ (v : Fin 2 → Set V3) (q : Set V3) (b : Fin 2)
                (raw : ∀ k, ChartwisePLSphere e (((sS i).map '' v k) ∪ ((H ∘ g) '' d))),
                (∀ k, IsFinitePLBallPair P2 (v k) q) ∧
                v 0 ∪ v 1 = sphere (0 : V3) 1 ∧ v 0 ∩ v 1 = q ∧
                (sS i).map '' q = (H ∘ g) '' P.boundary ℝ ∧
                (∀ k, EqOn (raw k).map (sS i).map (v k)) ∧
                (∀ k, (raw k).map '' v k.rev = (H ∘ g) '' d) ∧
                a '' Ann ⊆ (sS i).map '' v b ∧
                (a '' Ann) ∩ ((sS i).map '' v b.rev) = (H ∘ g) '' P.boundary ℝ ∧
                g '' P.boundary ℝ ⊆ (sS i).map '' v b ∧
                Disjoint (g '' P.boundary ℝ) ((sS i).map '' v b.rev) ∧
                IsFinitePLBallPair P2 D (P.boundary ℝ) ∧ D ∩ F = P.boundary ℝ ∧
                g '' D = ((H ∘ g) '' d) ∪ (a '' Ann) ∧
                g '' D ⊆ ((sS i).map '' v b) ∪ ((H ∘ g) '' d) ∧
                (g '' D) ∩ (((sS i).map '' v b.rev) ∪ ((H ∘ g) '' d)) =
                  (H ∘ g) '' d ∧
                (∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s)
                  (⋃ j, circleSurgeryFamily S i
                    (fun b : Bool => ((sS i).map '' v (if b then 1 else 0)) ∪ ((H ∘ g) '' d)) j)
                  g s.1 (A s)) ∧
                (∀ x ∈ g '' D, connectedComponentIn
                  ((((sS i).map '' v b) ∪ ((H ∘ g) '' d)) ∩
                    (g '' convexHull ℝ (t : Set E))) x = g '' D) ∧
                (∃ c', ¬ disk c' ∧ g '' P.boundary ℝ ⊆ g '' (C c').space ∧
                  ∃ y ∈ (g '' (C c').space) ∩ (g '' F),
                    y ∈ (sS i).map '' v b.rev ∧ y ∉ g '' P.boundary ℝ) ∧
                (∀ k x, x ∈ ((((sS i).map '' v k) ∪ ((H ∘ g) '' d)) ∩
                    (g '' convexHull ℝ (t : Set E))) →
                  let Q := connectedComponentIn
                    ((((sS i).map '' v k) ∪ ((H ∘ g) '' d)) ∩
                      (g '' convexHull ℝ (t : Set E))) x
                  ∃ c', Q ⊆ (g '' (C c').space) ∪ ((H ∘ g) '' d) ∧
                    Q ∩ (⋃ j, S j) ⊆ g '' (C c').space) ∧
                (∃ ρ : Type u, Finite ρ ∧ ∃ (rim : ρ → Set X) (old : ρ → γ)
                    (side : ρ → ({j : κ // j ≠ i} ⊕ Fin 2)) (point : ρ → X),
                  (∀ j, IsClosed (rim j) ∧ IsConnected (rim j) ∧
                    rim j ⊆ g '' (C (old j)).space ∧ point j ∈ rim j) ∧
                  Pairwise (fun j k => Disjoint (rim j) (rim k)) ∧
                  (⋃ j, rim j) = (⋃ j, S j) ∩ g '' F ∧
                  (∃ j, rim j = g '' P.boundary ℝ ∧ side j = Sum.inr b) ∧
                  (∀ j, rim j ⊆ Sum.elim (fun k : {j : κ // j ≠ i} => S k.val)
                    (fun k => (sS i).map '' v k) (side j)) ∧
                  ∀ selected : Set ({j : κ // j ≠ i} ⊕ Fin 2),
                    let retained := {j | side j ∈ selected}
                    let family := Sum.elim (fun k : {j : κ // j ≠ i} => S k.val)
                      (fun k => (sS i).map '' v k ∪ (H ∘ g) '' d)
                    let label := fun j => (side j, connectedComponentIn
                      (family (side j) ∩ g '' convexHull ℝ (t : Set E)) (point j))
                    retained.ncard - (label '' retained).ncard <
                      boundaryComponentExcess (⋃ j, S j) (g '' convexHull ℝ (t : Set E))
                        (g '' F)) ∧
                ∃ W : Set X, IsOpen W ∧
                  (∀ s ∈ K.faces, s.card ≤ 3 → g '' convexHull ℝ (s : Set E) ⊆ W) ∧
                  ((((sS i).map '' v 0) ∪ ((H ∘ g) '' d)) ∪
                    (((sS i).map '' v 1) ∪ ((H ∘ g) '' d))) ∩ W = S i ∩ W := by
  classical
  obtain ⟨γ,hγ,C,hC,hCdis,hCwhole,hcap⟩ := exists_original_nondisk_piece_contact_disk
    he K hK g hg hgi Q A hmap hA S sS hS hdis havoid hposition ht ht4
  refine ⟨γ,hγ,C,hC,hCdis,hCwhole,?_,?_⟩
  · intro hne
    obtain ⟨ball⟩ := exists_chartwisePLBall_image
      (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
      (ContinuousLinearEquiv.refl ℝ V3) hg (K.convexHull_subset_space ht) hgi
    exact exists_nondisk_piece_of_nonzero_boundary_excess C g hC hCdis hCwhole
      (hg.continuousOn.mono (K.convexHull_subset_space ht))
      (hgi.mono (K.convexHull_subset_space ht))
      (intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed)
      (by rw [←ball.frontier_eq]; exact isClosed_frontier) hne
  dsimp only at hcap ⊢
  intro c hc hne
  obtain ⟨n,P,d,hPi,hPe,hd,hdT,hdF,hdS,howner,ρ,hρ,m,L,rimIndex,hL,hLdis,hLwhole,hrL⟩ :=
    hcap c hc hne
  let : Finite ρ := hρ
  have hrK : P.boundary ℝ ⊆ K.space := hd.1.trans (hdT.trans (K.convexHull_subset_space ht))
  have hrS : g '' P.boundary ℝ ⊆ ⋃ i, S i := by
    rintro _ ⟨x,hx,rfl⟩
    exact (hdS.symm.subset hx).2
  obtain ⟨circle⟩ := P.nonempty_boundary_homeomorph_circle hPe hPi
  have hrconn : IsConnected (g '' P.boundary ℝ) :=
    (isConnected_iff_connectedSpace.mpr (circle.connectedSpace_iff.mpr inferInstance)).image
      g (hg.continuousOn.mono hrK)
  obtain ⟨i,hri,_⟩ := hrconn.exists_unique_subset_finite_disjoint_closed S
    (fun i => (sS i).isCompact.isClosed) hdis hrS
  refine ⟨n,P,d,i,hPi,hPe,hd,hdT,hdF,hdS,hri,howner,?_⟩
  intro V hV hrV
  obtain ⟨ball⟩ := exists_chartwisePLBall_image
    (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
    (ContinuousLinearEquiv.refl ℝ V3) hg (K.convexHull_subset_space ht) hgi
  obtain ⟨H,a,hH,hHi,hfix,hpres,hp,hpi,hcap,hcapS,hdisrim,ha,hai,haS,haT,
      hain,houter,hinner,hrA,hqA,hcontact,holdside,hneighborhood⟩ :=
    exists_original_strictly_interior_cap_with_annulus he hcover K hK g hg hgi
    Q hQ A hmap hA S sS hdis havoid hedge hedges hposition ht ht4 m L
    (fun k => (hL k).2.1) (fun k => (hL k).1) (fun k => (hL k).2.2) hLdis
    (by rw [ball.frontier_eq]; exact hLwhole) rimIndex i (by rwa [←hrL])
    hd hdT hdF hdS hrL hV hrV
  refine ⟨H,a,hH,hHi,hfix,hpres,hp,hpi,hcap,hcapS,hdisrim,ha,hai,haS,haT,
    hain,houter,hinner,hrA,hqA,hcontact,holdside,hneighborhood,?_⟩
  have hcapSi : ((H ∘ g) '' d) ∩ S i = (H ∘ g) '' P.boundary ℝ := by
    apply Subset.antisymm
    · exact fun x hx => hcapS.subset ⟨hx.1,mem_iUnion.mpr ⟨i,hx.2⟩⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨⟨x,hd.1 hx,rfl⟩,(hpres i (g x)).mpr (hri ⟨x,hx,rfl⟩)⟩
  obtain ⟨z,hz⟩ := hrconn.nonempty
  have hzn : z ∉ (H ∘ g) '' P.boundary ℝ :=
    fun h => disjoint_left.mp hdisrim h hz
  obtain ⟨m,R,v,hRi,hR,hv,hwhole,hinter,hrim,_,_,_,hphysical,_,hrawwhole,_,_,_⟩ :=
    (sS i).exists_original_disk_rim_raw_caps he hd hp hpi hcapSi ⟨z,hri hz⟩ hzn
  obtain ⟨b,raw,hraw,hrawcap,hside,hother,hrside,hrdis,hD,hDF,himage,hsub,hintercap⟩ :=
    (sS i).exists_original_raw_cap_with_annular_disk he K hK hg hgi ht ht4
      (fun x hx => (hdF.symm.subset hx).2) v hv hwhole hinter hd hp hpi hcapSi hrim
      ha hai (haS.trans inter_subset_left) hcap haT hain hcontact hinner hrA hqA houter
  have hunit : IsFinitePLBallPair P2 (closedBall (0 : P2) 1) (sphere (0 : P2) 1) := by
    have h := CoordinateHalfBoxes.base_ballPair (by norm_num : (0 : ℝ) < 1)
    have hbase : CoordinateHalfBoxes.base 1 = closedBall (0 : P2) 1 := by
      ext x
      simp only [CoordinateHalfBoxes.base,mem_prod,mem_Icc,mem_closedBall,
        dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
    have hfront := h.frontier_eq_of_finrank_eq rfl
    rw [hbase,frontier_closedBall _ one_ne_zero] at hfront
    rwa [hbase,←hfront] at h
  obtain ⟨f,F,hf,hfi,hfS,hfr,hF,hfwhole,hfinter,hnest,hann,hconfine⟩ := holdside
  have hrim' : (sS i).map '' R.boundary ℝ = H '' (f '' sphere (0 : P2) 1) := by
    rw [hfr,image_image]
    exact hrim
  obtain ⟨_,hretann⟩ := (sS i).moved_disk_eq_opposite_side he hcover hunit hf hfi hF
    hfwhole (by rwa [hfr]) (hfr.symm ▸ hrconn.nonempty) H hH (by rwa [hfr]) v hv hwhole hinter
    hrim' b (by rwa [hfr])
  have hretann' : ((sS i).map '' v b) ∩ (f '' closedBall (0 : P2) 1) = a '' Ann :=
    hretann.trans hann.symm
  let pieces : γ → Set X := fun c => g '' (C c).space
  have hCK (c : γ) : (C c).space ⊆ K.space :=
    (hC c).2.2.trans (K.convexHull_subset_space ht)
  have hpc (c : γ) : IsConnected (pieces c) :=
    (hC c).2.1.image g (hg.continuousOn.mono (hCK c))
  have hpclosed (c : γ) : IsClosed (pieces c) :=
    (((C c).isCompact_space_of_finite (hC c).1).image_of_continuousOn
      (hg.continuousOn.mono (hCK c))).isClosed
  have hpdis : Pairwise fun c d => Disjoint (pieces c) (pieces d) := by
    intro c d hcd
    apply disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
    exact disjoint_left.mp (hCdis hcd) hx (hgi (hCK d hy) (hCK c hx) heq ▸ hy)
  have hpwhole : (⋃ c, pieces c) =
      (g '' convexHull ℝ (t : Set E)) ∩ (⋃ j, S j) := by
    change (⋃ c, g '' (C c).space) = _
    rw [←image_iUnion,hCwhole,image_inter_preimage]
  have hpS (c : γ) : pieces c ⊆ ⋃ j, S j :=
    (subset_iUnion pieces c).trans (hpwhole.subset.trans inter_subset_right)
  have hpT (c : γ) : pieces c ⊆ g '' convexHull ℝ (t : Set E) :=
    (subset_iUnion pieces c).trans (hpwhole.subset.trans inter_subset_left)
  have haConn : IsConnected (a '' Ann) :=
    ⟨⟨z,hrA hz⟩,(isPreconnected_complete_squareAnnulus (by norm_num : (0:ℝ)<1)
      (by norm_num : (4:ℝ)*1<8)).image a ha.continuousOn⟩
  obtain ⟨c',hac',_⟩ := haConn.exists_unique_subset_finite_disjoint_closed pieces hpclosed hpdis
    (fun x hx => hpwhole.symm.subset ⟨haT hx,mem_iUnion.mpr ⟨i,(haS hx).1⟩⟩)
  obtain ⟨j,hc'j,_⟩ := (hpc c').exists_unique_subset_finite_disjoint_closed S
    (fun j => (sS j).isCompact.isClosed) hdis (hpS c')
  have hji : j = i := by
    by_contra hji
    exact disjoint_left.mp (hdis hji) (hc'j (hac' (hrA hz))) (hri hz)
  have hc'f : pieces c' ⊆ f '' closedBall (0 : P2) 1 :=
    hconfine (pieces c') (hpc c').isPreconnected (hji ▸ hc'j) (hpT c')
      ⟨z,hac' (hrA hz),hz⟩
  obtain ⟨c0,hc0,hrc0⟩ := howner
  have hc0eq : c0 = c' := by
    by_contra hn
    exact disjoint_left.mp (hpdis hn) (image_mono hrc0 hz) (hac' (hrA hz))
  subst c0
  have hotherboundary : ∃ y ∈ pieces c' ∩
      (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))), y ∉ g '' P.boundary ℝ := by
    by_contra hn
    have hfront : pieces c' ∩ (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) =
        g '' P.boundary ℝ := by
      apply Subset.antisymm
      · intro y hy
        by_contra hyr
        exact hn ⟨y,hy,hyr⟩
      · exact fun y hy => ⟨image_mono hrc0 hy,image_mono (fun x hx =>
          (hdF.symm.subset hx).2) hy⟩
    have hsourcefront : (C c').space ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) =
        P.boundary ℝ := by
      apply Subset.antisymm
      · intro x hx
        obtain ⟨y,hy,heq⟩ := hfront.subset ⟨⟨x,hx.1,rfl⟩,⟨x,hx.2,rfl⟩⟩
        exact hgi (hrK hy) (hCK c' hx.1) heq ▸ hy
      · exact fun x hx => ⟨hrc0 hx,(hdF.symm.subset hx).2⟩
    have hball := original_piece_is_disk_of_single_boundary he K hK g hg hgi Q A hmap hA
      S sS hdis hedges hposition ht ht4 pieces hpclosed hpdis
      (by simpa only [inter_comm] using hpwhole.symm.subset) c' i (hji ▸ hc'j)
      (hC c').2.2 rfl P hPi hPe (fun x hx => (hdF.symm.subset hx).2) hfront
    exact hc0 (hsourcefront.symm ▸ hball)
  obtain ⟨y,hy,hyoff⟩ := hotherboundary
  have hyother : y ∈ (sS i).map '' v b.rev := by
    have hySi : y ∈ S i := hji ▸ hc'j hy.1
    have hyret : y ∉ (sS i).map '' v b := by
      intro hyr
      have hya := hretann'.subset ⟨hyr,hc'f hy.1⟩
      have hyin := hain ⟨hya,hyoff⟩
      have hyfront := hy.2
      rw [←ball.frontier_eq] at hyfront
      exact hyfront.2 hyin
    fin_cases b
    · exact (hphysical.symm.subset hySi).resolve_left hyret
    · exact (hphysical.symm.subset hySi).resolve_right hyret
  have hnewcomponent : ∀ x ∈ ((H ∘ g) '' d) ∪ (a '' Ann), connectedComponentIn
      ((((sS i).map '' v b) ∪ ((H ∘ g) '' d)) ∩
        (g '' convexHull ℝ (t : Set E))) x = ((H ∘ g) '' d) ∪ (a '' Ann) := by
    refine repaired_disk_eq_connectedComponentIn pieces hpclosed hpdis
      (by simpa only [inter_comm] using hpwhole.symm.subset) hpS c'
      (fun x hx => mem_iUnion.mpr ⟨i,?_⟩) (hcap.trans interior_subset) haT hside hac'
      ?_ ?_ ?_ ?_
    · obtain ⟨y,hy,rfl⟩ := hx
      have hyS : y ∈ sphere (0 : V3) 1 := by
        fin_cases b
        · exact hwhole.subset (Or.inl hy)
        · exact hwhole.subset (Or.inr hy)
      rw [(sS i).map_eq ⟨y,hyS⟩]
      exact ((sS i).parametrization ⟨y,hyS⟩).property
    · exact fun x hx => hretann'.subset ⟨hx.1,hc'f hx.2⟩
    · exact hcapS.subset.trans hqA
    · rw [←himage]
      exact (hD.isCompact.image_of_continuousOn (hg.continuousOn.mono
        (inter_subset_left.trans (K.convexHull_subset_space ht)))).isClosed
    · rw [←himage]
      exact hD.isConnected.image g (hg.continuousOn.mono
        (inter_subset_left.trans (K.convexHull_subset_space ht)))
  refine ⟨v,R.boundary ℝ,b,raw,hv,hwhole,hinter,hrim,hraw,hrawcap,hside,hother,
    hrside,hrdis,hD,hDF,himage,hsub,hintercap,?_,?_,
    ⟨c',hc0,image_mono hrc0,y,hy,hyother,hyoff⟩,?_,?_,
    ((H ∘ g) '' d)ᶜ,(hd.isCompact.image_of_continuousOn hp.continuousOn).isClosed.isOpen_compl,
    ?_,?_⟩
  · intro s
    apply (hposition s).of_equal_off_closed
      (hd.isCompact.image_of_continuousOn hp.continuousOn).isClosed
      ((original_tetrahedron_interior_disjoint_face K hg hgi ht ht4 s.2.1
        (by omega)).mono_left hcap)
    apply circleSurgeryFamily_sdiff
    simp only [Bool.false_eq_true,if_false,if_true]
    rw [union_comm (((sS i).map '' v 1) ∪ ((H ∘ g) '' d)),hrawwhole]
    ext x
    simp only [mem_sdiff,mem_union]
    tauto
  · simpa only [himage] using hnewcomponent
  · intro k x hx
    apply exists_old_piece_for_capped_component (S := ⋃ j, S j)
      (B := g '' convexHull ℝ (t : Set E)) pieces hpclosed hpdis
      (by simpa only [inter_comm] using hpwhole.symm.subset) hpS c'
      (hd.isCompact.image_of_continuousOn hp.continuousOn).isClosed
      (hcapS.subset.trans (hqA.trans hac'))
      (isConnected_connectedComponentIn_iff.mpr hx)
    intro z hz
    obtain ⟨hz,hzT⟩ := connectedComponentIn_subset _ _ hz
    refine ⟨?_,hzT⟩
    rcases hz with hz | hz
    · apply Or.inl
      refine mem_iUnion.mpr ⟨i,?_⟩
      obtain ⟨w,hw,rfl⟩ := hz
      have hwS : w ∈ sphere (0 : V3) 1 := by
        fin_cases k
        · exact hwhole.subset (Or.inl hw)
        · exact hwhole.subset (Or.inr hw)
      rw [(sS i).map_eq ⟨w,hwS⟩]
      exact ((sS i).parametrization ⟨w,hwS⟩).property
    · exact Or.inr hz
  · let rims : ρ → Set X := fun j => g '' (L j).boundary ℝ
    have hFT : intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ⊆
        convexHull ℝ (t : Set E) :=
      intrinsicFrontier_subset (t.finite_toSet.isCompact_convexHull ℝ).isClosed
    have hFK := hFT.trans (K.convexHull_subset_space ht)
    have hRimConn (j : ρ) : IsConnected (rims j) := by
      obtain ⟨h⟩ := (L j).nonempty_boundary_homeomorph_circle (hL j).2.1 (hL j).1
      exact (isConnected_iff_connectedSpace.mpr (h.connectedSpace_iff.mpr inferInstance)).image
        g (hg.continuousOn.mono ((hL j).2.2.trans hFK))
    have hVsub (k : Fin 2) : v k ⊆ sphere (0 : V3) 1 := by
      fin_cases k
      · exact subset_union_left.trans hwhole.subset
      · exact subset_union_right.trans hwhole.subset
    have hVclosed (k : Fin 2) : IsClosed ((sS i).map '' v k) :=
      ((hv k).isCompact.image_of_continuousOn ((sS i).piecewiseAffine.continuousOn.mono
        (hVsub k))).isClosed
    have hsi : InjOn (sS i).map (sphere (0 : V3) 1) := by
      intro x hx y hy heq
      have heq' : (sS i).parametrization ⟨x,hx⟩ = (sS i).parametrization ⟨y,hy⟩ :=
        Subtype.ext (by simpa only [←(sS i).map_eq] using heq)
      exact congrArg Subtype.val ((sS i).parametrization.injective heq')
    have hVI : ((sS i).map '' v 0) ∩ ((sS i).map '' v 1) ⊆ (H ∘ g) '' d := by
      rw [←hsi.image_inter (hVsub 0) (hVsub 1),hinter,hrim]
      exact image_mono hd.1
    have hcapF : Disjoint ((H ∘ g) '' d)
        (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) := by
      apply disjoint_left.mpr
      intro x hx hxF
      rw [←ball.frontier_eq] at hxF
      exact hxF.2 (hcap hx)
    have hDFphysical : (((H ∘ g) '' d) ∪ (a '' Ann)) ∩
        (g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) = rims rimIndex := by
      rw [←himage,←hgi.image_inter (inter_subset_left.trans (K.convexHull_subset_space ht)) hFK,
        hDF,hrL]
    obtain ⟨old,side,point,hold,hside,hsideR,hcount⟩ := exists_raw_circle_boundary_count
      pieces rims S hpclosed hpdis (by simpa only [inter_comm] using hpwhole.symm.subset)
      hpS (fun j => (sS j).isCompact.isClosed) hdis
      (by rw [←ball.frontier_eq]; exact isClosed_frontier)
      (image_mono hFT) hRimConn hLdis hLwhole i (fun k => (sS i).map '' v k)
      hVclosed hphysical hVI (hd.isCompact.image_of_continuousOn hp.continuousOn).isClosed
      hcapF c' (hcapS.subset.trans (hqA.trans hac')) rimIndex
      (by simpa only [rims,←hrL] using image_mono hrc0)
      ⟨y,hy,by simpa only [rims,←hrL] using hyoff⟩ b
      (by simpa only [rims,←hrL] using hrside)
      (fun x hx => hnewcomponent x (Or.inr (hrA (by simpa only [rims,←hrL] using hx))))
      hDFphysical
    have hRimClosed (j : ρ) : IsClosed (rims j) :=
      ((L j).isCompact_boundary.image_of_continuousOn
        (hg.continuousOn.mono ((hL j).2.2.trans hFK))).isClosed
    have hcanonical := boundaryComponentExcess_eq_of_finite_pieces
      (S := ⋃ j, S j) (B := g '' convexHull ℝ (t : Set E))
      (F := g '' intrinsicFrontier ℝ (convexHull ℝ (t : Set E))) pieces rims old hpclosed hpc
      hpdis (by simpa only [inter_comm] using hpwhole) hRimClosed hRimConn hLdis hLwhole
      (fun j => (hold j).1)
    exact ⟨ρ,hρ,rims,old,side,point,fun j => ⟨hRimClosed j,hRimConn j,(hold j).1,(hold j).2⟩,
      hLdis,hLwhole,⟨rimIndex,congrArg (fun Z => g '' Z) hrL.symm,hside⟩,hsideR,
      fun selected => hcanonical.symm ▸ hcount selected⟩
  · intro s hs hs3 y hy hcapy
    exact disjoint_left.mp (original_tetrahedron_interior_disjoint_face K hg hgi ht ht4 hs hs3)
      (hcap hcapy) hy
  · rw [hrawwhole]
    ext x
    simp only [mem_inter_iff,mem_union,mem_compl_iff]
    tauto

end PoincareConjecture.M76

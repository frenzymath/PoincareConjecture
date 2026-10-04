import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.Systems.PositionedSeparatedCaps
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.Systems.SeparatedCircleSphereAssembly
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.Systems.CircleSurgeryContactLedger
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.Systems.ProtectedCircleNeighborhood

/-!
# Protected surgery on a positioned sphere circle

The existing whole-family graph constructs the selected empty cap,
identity-period collar, disjoint caps and matching retained disks. Exact
carrier identities remove just the selected circle from the chosen face
and preserve every other original face.
-/

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareMT.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)

theorem exists_protected_positioned_circle_surgery_with_support
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {Z : Set X} (hZ : IsClosed Z) (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target)
    (hphysicalGraph : Q.symm '' G.space = (⋃ i, S i) ∩
      (g '' convexHull ℝ (s : Set E)))
    (hSZ : Disjoint (⋃ i, S i) Z)
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hcrossings : ∀ w ∈ G.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S i ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0)
    (hcircle : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅) :
    ∃ (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (n : ℕ) (L : Polygon V3 (n + 3)) (i : κ) (O : Set X) (new : Bool → Set X),
      Function.Injective L ∧ L.HasSimplicialEdges ∧
      L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
      L.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) ∧
      IsOpen O ∧ O ⊆ Q.source ∧ Q.symm '' L.boundary ℝ ⊆ O ∧
      Disjoint O Z ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        Disjoint O (g '' convexHull ℝ (a : Set E))) ∧
      (∀ j, j ≠ i → Disjoint O (S j)) ∧
      Nonempty (∀ b, ChartwisePLSphere e (new b)) ∧
      Disjoint (new true) (new false) ∧
      (∀ b j, j ≠ i → Disjoint (new b) (S j)) ∧
      (∀ b, Disjoint (new b) Z) ∧
      (new true ∪ new false) \ O = S i \ O ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        (new true ∪ new false) ∩ (g '' convexHull ℝ (a : Set E)) =
          S i ∩ (g '' convexHull ℝ (a : Set E))) ∧
      (new true ∪ new false) ∩ (g '' convexHull ℝ (s : Set E)) =
        (S i ∩ (g '' convexHull ℝ (s : Set E))) \ (Q.symm '' L.boundary ℝ) ∧
      ∃ C₀ : Set X, IsCompact C₀ ∧ C₀ ⊆ O ∧
        (new true ∪ new false) \ C₀ = S i \ C₀ ∧
        C₀ ∩ ((⋃ j, S j) ∩ (g '' convexHull ℝ (s : Set E))) =
          Q.symm '' L.boundary ℝ := by
  classical
  obtain ⟨C, n, L, D, i, hLi, hL, hLC, hD, hcompact, hDT, hDG,
      hphyscompact, hphysub, hDZ, hDsk, hcap, hirim, hiunique,
      m, R, d₀, d₁, hRi, hR, hd₀, hd₁, hparamunion, hparaminter,
      hpieces, hpiecerim, s₀, s₁, hs₀, hs₁, hs₀cap, hs₁cap,
      hrawunion, hrawinter, hother⟩ :=
    exists_positioned_sphere_system_circle_caps S sS hdis K N hNK g hgi
      hmark hs hs3 Q A hmap hA G hG hGT hphysicalGraph hSZ hdim hfinite
      hinterior hexterior he hcover hQ hcrossings hcircle
  have hTQ : convexHull ℝ (A '' (s : Set E)) ⊆ Q.target := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (A.toAffineMap.image_convexHull (s : Set E)).symm.subset hx
    change A u ∈ Q.target
    rw [← hA hu]
    exact Q.map_source (hmap hu)
  have hDQ : D ⊆ Q.target := hDT.trans (intrinsicInterior_subset.trans hTQ)
  have hLinter := hD.1.trans hDT
  obtain ⟨O, hO, hDO, hOQ, hOZ, hOfaces, hOmembers⟩ :=
    exists_protected_circle_cap_neighborhood S sS hdis K hK g hgc hgi hs hs3
      hZ hDZ hphysub hcap i hirim Q
      (by rintro _ ⟨x, hx, rfl⟩; exact Q.map_target (hDQ hx))
  have hd₀S : d₀ ⊆ sphere (0 : V3) 1 := subset_union_left.trans hparamunion.subset
  have hd₁S : d₁ ⊆ sphere (0 : V3) 1 := subset_union_right.trans hparamunion.subset
  have hsi : InjOn (sS i).map (sphere (0 : V3) 1) := by
    intro x hx y hy hxy
    rw [(sS i).map_eq ⟨x, hx⟩, (sS i).map_eq ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val ((sS i).parametrization.injective (Subtype.ext hxy))
  have hrimage : (sS i).map '' R.boundary ℝ = Q.symm '' L.boundary ℝ := by
    rw [← hparaminter, image_inter_on (s := d₀) (t := d₁)
      (fun x hx y hy hxy => hsi (hd₁S hx) (hd₀S hy) hxy)]
    exact hpiecerim
  have hrO := (image_mono hD.1).trans hDO
  obtain ⟨H, l, sigma, hH, hplane, hSigma, hMap, hInt, hTriangle, hSphere,
      hMember, hAxis, hImage, hFib, hOther, hzero, hsides, caps, hcaps,
      hcapsDis, hphysicalDis⟩ :=
    exists_positioned_sphere_system_separated_caps S sS hdis K g hgi hs hs3 Q hQ A
      hmap hA G hG hGT hphysicalGraph hdim hinterior hexterior hcrossings C L hL hLi
      hLC hLinter i R hR hRi hd₀ hd₀S hrimage hO hrO hD hDT hcap hDO
  have hSigmaCompact := hSigma.isCompact.image_of_continuousOn hSigma.continuousOn
  obtain ⟨J, hJ, hSigmaJ, hJQ⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed hSigmaCompact Q.open_target
      (by rintro _ ⟨x, hx, rfl⟩; exact (hMap hx).1)
  have hSigmaMapJ : MapsTo sigma (Dehn.signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3)) J.space :=
    fun x hx => interior_subset (hSigmaJ ⟨x, hx, rfl⟩)
  obtain ⟨φ, k, hφ, hφS, hφval, hk, hkdis, hkaxis, hwhole, t, ht, htDis, htOther⟩ :=
    exists_separated_circle_spheres_of_collar S sS hdis i he Q hQ
      (fun x _ => hcover x) J hJ hJQ (by positivity : (0 : ℝ) < l + 3)
      sigma hSigma hSigmaMapJ
      (fun z hz hz0 => (hMember ⟨z, hz⟩).mpr
        ((Dehn.signedTubeSheet_coordinate_iff _ hz.1 1).mpr hz0))
      (by intro x hx y hy; simpa only [and_comm] using hFib ⟨x, hx⟩ ⟨y, hy⟩)
      caps (fun b => (hcaps b).1) (fun b => (hcaps b).2.1) hcapsDis
      (fun b => (hcaps b).2.2.2.1)
  have hfaceMem {x : V3} (hxQ : x ∈ Q.target) :
      Q.symm x ∈ g '' convexHull ℝ (s : Set E) ↔
        x ∈ convexHull ℝ (A '' (s : Set E)) := by
    constructor
    · rintro ⟨u, hu, hux⟩
      apply (A.toAffineMap.image_convexHull (s : Set E)).subset
      refine ⟨u, hu, ?_⟩
      exact (hA hu).symm.trans ((congrArg Q hux).trans (Q.right_inv hxQ))
    · intro hx
      obtain ⟨u, hu, hux⟩ := (A.toAffineMap.image_convexHull (s : Set E)).symm.subset hx
      exact ⟨u, hu, (Q.left_inv (hmap hu)).symm.trans
        (congrArg Q.symm ((hA hu).trans hux))⟩
  have hface : ∀ z ∈ Dehn.signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3),
      Q.symm (sigma z) ∈ g '' convexHull ℝ (s : Set E) ↔ z.1.1 = 0 := by
    intro z hz
    exact (hfaceMem (hMap hz).1).trans
      ((hTriangle ⟨z, hz⟩).trans (by
        simpa using Dehn.signedTubeSheet_coordinate_iff z.1 hz.1 (0 : Fin 2)))
  have haxisPhysical :
      (fun u : ℝ => Q.symm (sigma ((0, 0), u))) '' Icc (0 : ℝ) (l + 3) =
        Q.symm '' L.boundary ℝ := by
    simpa only [image_image, Function.comp_def] using congrArg (image Q.symm) hImage
  have hcapFace (b : Bool) :
      Disjoint (Q.symm '' caps b) (g '' convexHull ℝ (s : Set E)) := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hxFace
    exact disjoint_left.mp (hcaps b).2.2.2.2 hx
      ((hfaceMem ((hcaps b).2.1 hx)).mp hxFace)
  obtain ⟨hBandFace, hRetainedAxis, hnewFace, houtside⟩ :=
    (sS i).circle_surgery_contact_ledger φ k hφS (fun b => (hk b).2.1)
      hkaxis hwhole (Q.symm ∘ sigma) hφval
      (g '' convexHull ℝ (s : Set E)) (Q.symm '' L.boundary ℝ) hface haxisPhysical
      (fun b => Q.symm '' caps b) hcapFace
  let T₀ := (Q.symm ∘ sigma) ''
    (Dehn.signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3))
  have hT₀ : IsCompact T₀ := by
    change IsCompact ((Q.symm ∘ sigma) '' _)
    simpa only [image_image, Function.comp_def] using hSigmaCompact.image_of_continuousOn
      (Q.continuousOn_symm.mono (by rintro _ ⟨z, hz, rfl⟩; exact (hMap hz).1))
  have hT₀O : T₀ ⊆ O := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hMap hz).2
  have hcapCompact (b : Bool) : IsCompact (Q.symm '' caps b) :=
    (hcaps b).1.isCompact.image_of_continuousOn
      (Q.continuousOn_symm.mono (hcaps b).2.1)
  let C₀ := T₀ ∪ (Q.symm '' caps true ∪ Q.symm '' caps false)
  have hC₀ : IsCompact C₀ := hT₀.union ((hcapCompact true).union (hcapCompact false))
  have hC₀O : C₀ ⊆ O := union_subset hT₀O
    (union_subset (hcaps true).2.2.1 (hcaps false).2.2.1)
  have hC₀Graph : C₀ ∩ ((⋃ j, S j) ∩ (g '' convexHull ℝ (s : Set E))) =
      Q.symm '' L.boundary ℝ := by
    apply Subset.antisymm
    · rintro x ⟨hxC, hxS, hxT⟩
      rcases hxC with hxTube | hxCaps
      · obtain ⟨z, hz, rfl⟩ := hxTube
        have h0 := (hface z hz).mp hxT
        have h1 : z.1.2 = 0 :=
          (Dehn.signedTubeSheet_coordinate_iff z.1 hz.1 1).mp
            ((hSphere ⟨z, hz⟩).mp hxS)
        exact ⟨sigma z, (hAxis ⟨z, hz⟩).mpr (Prod.ext h0 h1), rfl⟩
      · rcases hxCaps with hx | hx
        · exact False.elim (disjoint_left.mp (hcapFace true) hx hxT)
        · exact False.elim (disjoint_left.mp (hcapFace false) hx hxT)
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨u, hu, rfl⟩ := hImage.symm.subset hy
      have hz : ((0, 0), u) ∈ Dehn.signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3) :=
        ⟨(Dehn.signedTubeDiamond_coordinate_iff _).mpr (by norm_num), hu⟩
      exact ⟨Or.inl ⟨((0, 0), u), hz, rfl⟩,
        (hSphere ⟨_, hz⟩).mpr
          ((Dehn.signedTubeSheet_coordinate_iff _ hz.1 1).mpr rfl),
        (hface _ hz).mpr rfl⟩
  have hBandT₀ :
      (fun z : P2 => Q.symm (sigma ((z.1, 0), z.2))) ''
        (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) (l + 3)) ⊆ T₀ := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) (l + 3) :=
      ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
    have hdom : ((z.1, 0), z.2) ∈ Dehn.signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3) := by
      simpa only [Dehn.signedSheetStripMap_apply, Fin.reduceEq, if_false] using
        Dehn.signedSheetStripMap_mem (1 : Fin 2) hz'
    exact ⟨((z.1, 0), z.2), hdom, rfl⟩
  have hBandO := hBandT₀.trans hT₀O
  obtain ⟨hExterior, hContact⟩ := houtside O hBandO (fun b => (hcaps b).2.2.1)
  have hSupport := (houtside C₀ (hBandT₀.trans subset_union_left) (by
    intro b
    cases b
    · exact subset_union_right.trans subset_union_right
    · exact subset_union_left.trans subset_union_right)).1
  let new : Bool → Set X := fun b => (sS i).map '' k b ∪ Q.symm '' caps b
  refine ⟨C, n, L, i, O, new, hLi, hL, hLC, hLinter, hO, hOQ, hrO, hOZ,
    hOfaces, hOmembers, ⟨t⟩, htDis, htOther, ?_, hExterior, ?_, hnewFace,
    C₀, hC₀, hC₀O, hSupport, hC₀Graph⟩
  · intro b
    apply disjoint_left.mpr
    intro x hx hxZ
    have hxunion : x ∈ new true ∪ new false := by
      cases b
      · exact Or.inr hx
      · exact Or.inl hx
    have hxi : x ∈ S i := ((hContact Z hOZ.symm).subset ⟨hxunion, hxZ⟩).1
    exact disjoint_left.mp hSZ ((subset_iUnion S i) hxi) hxZ
  · intro a ha hac hane
    exact hContact _ (hOfaces a ha hac hane).symm

/-- The public surgery conclusion, obtained from the construction that
also retains its compact support. -/
theorem exists_protected_positioned_circle_surgery
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {Z : Set X} (hZ : IsClosed Z) (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target)
    (hphysicalGraph : Q.symm '' G.space = (⋃ i, S i) ∩
      (g '' convexHull ℝ (s : Set E)))
    (hSZ : Disjoint (⋃ i, S i) Z)
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hfinite : (G.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite)
    (hinterior : ∀ v : G.vertices,
      (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices,
      (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hcrossings : ∀ w ∈ G.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
      ∀ O : Set V3, IsOpen O → w ∈ O →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ O ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧
          LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S i ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0)
    (hcircle : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅) :
    ∃ (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (n : ℕ) (L : Polygon V3 (n + 3)) (i : κ) (O : Set X) (new : Bool → Set X),
      Function.Injective L ∧ L.HasSimplicialEdges ∧
      L.boundary ℝ = C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∧
      L.boundary ℝ ⊆ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) ∧
      IsOpen O ∧ O ⊆ Q.source ∧ Q.symm '' L.boundary ℝ ⊆ O ∧
      Disjoint O Z ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        Disjoint O (g '' convexHull ℝ (a : Set E))) ∧
      (∀ j, j ≠ i → Disjoint O (S j)) ∧
      Nonempty (∀ b, ChartwisePLSphere e (new b)) ∧
      Disjoint (new true) (new false) ∧
      (∀ b j, j ≠ i → Disjoint (new b) (S j)) ∧
      (∀ b, Disjoint (new b) Z) ∧
      (new true ∪ new false) \ O = S i \ O ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        (new true ∪ new false) ∩ (g '' convexHull ℝ (a : Set E)) =
          S i ∩ (g '' convexHull ℝ (a : Set E))) ∧
      (new true ∪ new false) ∩ (g '' convexHull ℝ (s : Set E)) =
        (S i ∩ (g '' convexHull ℝ (s : Set E))) \ (Q.symm '' L.boundary ℝ) := by
  obtain ⟨C, n, L, i, O, new, hLi, hL, hLC, hLint, hO, hOQ, hrO, hOZ,
      hOfaces, hOmembers, ht, htDis, htOther, htZ, hExterior, hOtherFaces,
      hFace, hSupport⟩ :=
    exists_protected_positioned_circle_surgery_with_support S sS hdis K N hK hNK
      g hgc hgi hZ hmark hs hs3 Q A hmap hA G hG hGT hphysicalGraph hSZ
      hdim hfinite hinterior hexterior he hcover hQ hcrossings hcircle
  exact ⟨C, n, L, i, O, new, hLi, hL, hLC, hLint, hO, hOQ, hrO, hOZ,
    hOfaces, hOmembers, ht, htDis, htOther, htZ, hExterior, hOtherFaces, hFace⟩

end PoincareMT.M76

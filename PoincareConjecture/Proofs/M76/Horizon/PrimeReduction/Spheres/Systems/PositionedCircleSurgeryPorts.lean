import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.WitnessProtectedCircleRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.ChartwiseBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PositionedSeparatedCaps
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.SeparatedCircleSphereAssembly
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleSurgeryContactLedger
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.ProtectedCircleNeighborhood
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortRegionProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PositionedPortMiddleDisk
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PositionedPortFaceProduct










set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)

theorem exists_protected_positioned_circle_surgery_ports
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
      (∃ C₀ : Set X, IsCompact C₀ ∧ C₀ ⊆ O ∧
        (new true ∪ new false) \ C₀ = S i \ C₀ ∧
        C₀ ∩ ((⋃ j, S j) ∩ (g '' convexHull ℝ (s : Set E))) =
          Q.symm '' L.boundary ℝ) ∧
      ∃ (k q : Bool → Set V3) (caps : Bool → Set X) (band region : Set X),
        (∀ b, IsFinitePLBallPair P2 (k b) (q b) ∧
          k b ⊆ sphere (0 : V3) 1 ∧
          new b = (sS i).map '' k b ∪ caps b ∧
          ((sS i).map '' k b) ∩ band = (sS i).map '' q b ∧
          region ∩ ((sS i).map '' k b) = (sS i).map '' q b) ∧
        Disjoint (k true) (k false) ∧
        (((sS i).map '' k true) ∪ ((sS i).map '' k false)) ∪ band = S i ∧
        Nonempty (ChartwisePLBall e region (band ∪ (caps true ∪ caps false))) ∧
        region ⊆ O ∧ frontier region = band ∪ (caps true ∪ caps false) ∧
        region ∩ (⋃ j, S j) = band ∧
        Disjoint (interior region) (⋃ j, S j) ∧
        ∃ Dc rc : Bool → Set V3,
          (∀ b, IsFinitePLBallPair P2 (Dc b) (rc b) ∧ Dc b ⊆ Q.target ∧
            caps b = Q.symm '' Dc b ∧
            (sS i).map '' q b = Q.symm '' rc b ∧
            caps b ∩ (⋃ j, S j) = (sS i).map '' q b ∧
            caps b ∩ ((sS i).map '' k b) = (sS i).map '' q b) ∧
          Disjoint (caps true) (caps false) ∧
          ∃ C : ((_root_.Dehn.annulusSquare 8 0 : Set P2) × unitInterval) ≃ₜ region,
            (∀ b z, (C z : X) ∈ caps b ↔ z.2 = if b then 1 else 0) ∧
            ∃ p : P3 → X,
              PolyhedralPLInCharts e p
                (_root_.Dehn.annulusSquare 8 0 ×ˢ Icc (0 : ℝ) 1) ∧
              (∀ z : (_root_.Dehn.annulusSquare 8 0 ×ˢ Icc (0 : ℝ) 1 : Set P3),
                p z = (C ((Homeomorph.Set.prod _ _) z) : X)) ∧
              (∀ t : ℝ, 0 < t → t < 1 →
                let j : P2 → X := fun z => p (z,t)
                PolyhedralPLInCharts e j (_root_.Dehn.annulusSquare 8 0) ∧
                InjOn j (_root_.Dehn.annulusSquare 8 0) ∧
                MapsTo j (_root_.Dehn.annulusSquare 8 0) region ∧
                (∀ z ∈ _root_.Dehn.annulusSquare 8 0,
                  j z ∈ ⋃ a, S a ↔ z ∈ frontier (_root_.Dehn.annulusSquare 8 0)) ∧
                j '' frontier (_root_.Dehn.annulusSquare 8 0) ⊆ band ∧
                j '' (_root_.Dehn.annulusSquare 8 0 \
                  frontier (_root_.Dehn.annulusSquare 8 0)) ⊆ interior region ∧
                ∀ b, Disjoint (j '' (_root_.Dehn.annulusSquare 8 0)) (caps b)) ∧
              (∀ b, Disjoint (caps b) (g '' convexHull ℝ (s : Set E))) ∧
              band ∩ (g '' convexHull ℝ (s : Set E)) = Q.symm '' L.boundary ℝ ∧
              ∃ ρ : V2 × ℝ → X,
                PolyhedralPLInCharts e ρ
                  (closedBall (0 : V2) 1 ×ˢ Icc (-1 : ℝ) 1) ∧
                InjOn ρ (closedBall (0 : V2) 1 ×ˢ Icc (-1 : ℝ) 1) ∧
                MapsTo ρ (closedBall (0 : V2) 1 ×ˢ Icc (-1 : ℝ) 1) region ∧
                (∀ z ∈ closedBall (0 : V2) 1 ×ˢ Icc (-1 : ℝ) 1,
                  ρ z ∈ S i ↔ z.1 ∈ sphere (0 : V2) 1) ∧
                (∀ b : Bool, Disjoint (ρ '' (closedBall (0 : V2) 1 ×ˢ
                  {if b then (1/2 : ℝ) else -(1/2)})) (g '' convexHull ℝ (s : Set E))) ∧
                (ρ '' (sphere (0 : V2) 1 ×ˢ Icc (-(1/2 : ℝ)) (1/2))) ∩
                  (g '' convexHull ℝ (s : Set E)) = Q.symm '' L.boundary ℝ ∧
                region ∩ (g '' convexHull ℝ (s : Set E)) ⊆
                  ρ '' (closedBall (0 : V2) 1 ×ˢ Ioo (-(1/2 : ℝ)) (1/2)) := by
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
  let d : Bool → Set V3 := fun b => if b then d₀ else d₁
  have hd (b : Bool) : IsFinitePLBallPair P2 (d b) (R.boundary ℝ) := by
    cases b <;> assumption
  obtain ⟨p, U, hU, hDU, hUO, hpne, hp, hUother,
      H, l, sigma, hH, hplane, hSigma, hMapU, hInt, hTriangle, hSphere,
      hMember, hAxis, hImage, hFib, hOther, hzero, hsides, caps, hcapsU,
      hcapsDis, hphysicalDis, B, bd, hB, hDB, hBV, hTubeB, hCapsB,
      region, hRegion, hRegionB, hFrontier, hFrontierM, hRegionU,
      hRegionFamily, hInteriorFamily, φ, k, hφ, hφS, hφval, hφaxis,
      hk, hkdis, hwhole⟩ :=
    exists_witness_protected_sphere_system_circle_region S sS hdis K g hgi hs hs3 Q hQ A
      hmap hA G hG hGT hphysicalGraph hdim hinterior hexterior hcrossings C L hL hLi
      hLC hLinter i R hR hRi d hd hparamunion hparaminter hrimage hO hrO hD hDT hcap hDO
  have hMap : MapsTo sigma (Dehn.signedTubeDiamond ×ˢ Icc (0 : ℝ) (l + 3))
      (Q.target ∩ Q.symm ⁻¹' O) := fun x hx => ⟨(hMapU hx).1, hUO (hMapU hx).2⟩
  have hcaps (b : Bool) := (hcapsU b).1
  have hcapsO (b : Bool) : Q.symm '' caps b ⊆ O := (hcapsU b).2.2.1.trans hUO
  let q : Bool → Set V3 := fun b =>
    (fun t : ℝ => φ (if b then 1 / 4 else -1 / 4, t)) '' Icc (0 : ℝ) (l + 3)
  let c : Bool → Set V3 := fun b =>
    (fun t : ℝ => sigma ((if b then 1 / 4 else -1 / 4, 0), t)) '' Icc (0 : ℝ) (l + 3)
  have hrims (b : Bool) : (sS i).map '' q b = Q.symm '' c b := by
    simpa only [q, c, image_image] using (hk b).2.2.2.1
  obtain ⟨t, ht, htDis, htOther⟩ :=
    exists_separated_circle_spheres S sS hdis i he Q hQ (fun x _ => hcover x)
      k q caps c (fun b => (hk b).1) (fun b => (hk b).2.1)
      (fun b => (hk b).2.2.1) hkdis hcaps (fun b => (hcapsU b).2.1)
      hcapsDis (fun b => (hcapsU b).2.2.2.1) hrims
  have hkaxis (b : Bool) :
      Disjoint (k b) ((fun t : ℝ => φ (0, t)) '' Icc (0 : ℝ) (l + 3)) := by
    rw [hφaxis]
    exact (hk b).2.2.2.2.2.1
  have hSigmaCompact := hSigma.isCompact.image_of_continuousOn hSigma.continuousOn
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
    exact disjoint_left.mp (hcapsU b).2.2.2.2 hx
      ((hfaceMem ((hcapsU b).2.1 hx)).mp hxFace)
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
    (hcaps b).isCompact.image_of_continuousOn
      (Q.continuousOn_symm.mono (hcapsU b).2.1)
  let C₀ := T₀ ∪ (Q.symm '' caps true ∪ Q.symm '' caps false)
  have hC₀ : IsCompact C₀ := hT₀.union ((hcapCompact true).union (hcapCompact false))
  have hC₀O : C₀ ⊆ O := union_subset hT₀O
    (union_subset (hcapsO true) (hcapsO false))
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
  obtain ⟨hExterior, hContact⟩ := houtside O hBandO (fun b => hcapsO b)
  have hSupport := (houtside C₀ (hBandT₀.trans subset_union_left) (by
    intro b
    cases b
    · exact subset_union_right.trans subset_union_right
    · exact subset_union_left.trans subset_union_right)).1
  let new : Bool → Set X := fun b => (sS i).map '' k b ∪ Q.symm '' caps b
  let band := (fun z : P2 => sigma ((z.1, 0), z.2)) ''
    (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) (l + 3))
  have hRegionQ : region ⊆ Q.target := fun x hx =>
    (hBV (interior_subset (hRegionB hx))).1
  have hcapCoord (b : Bool) : caps b ∩ (Q.symm ⁻¹' (⋃ j, S j)) = c b := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := (hcapsU b).2.2.2.1.subset ⟨⟨x, hx.1, rfl⟩, hx.2⟩
      have hyQ := (hcapsU b).2.1 ((hcaps b).1 hy)
      have heq := Q.symm.injOn hyQ ((hcapsU b).2.1 hx.1) hxy
      exact heq ▸ hy
    · intro x hx
      exact ⟨(hcaps b).1 hx,
        ((hcapsU b).2.2.2.1.symm.subset ⟨x, hx, rfl⟩).2⟩
  obtain ⟨product, hproductPL, hproduct⟩ := exists_circle_two_port_product_handle
    (by positivity : (0 : ℝ) < l + 3) sigma hSigma
    (by intro x hx y hy; simpa only [and_comm] using hFib ⟨x, hx⟩ ⟨y, hy⟩)
    (M := Q.symm ⁻¹' (⋃ j, S j))
    (fun z hz => (hSphere ⟨z, hz⟩).trans
      (Dehn.signedTubeSheet_coordinate_iff z.1 hz.1 1))
    caps hcaps hcapCoord hcapsDis hRegion
  let physicalProduct := product.trans (Q.symm.homeomorphOfImageSubsetSource hRegionQ rfl)
  obtain ⟨productMap,hproductMap,hproductValue⟩ := hproductPL
  have hproductTarget : MapsTo productMap
      (_root_.Dehn.annulusSquare 8 0 ×ˢ Icc (0 : ℝ) 1) Q.target := by
    intro z hz
    rw [←hproductValue ⟨z,hz⟩]
    exact hRegionQ (product ((Homeomorph.Set.prod _ _) ⟨z,hz⟩)).property
  have hphysicalPL : PolyhedralPLInCharts e (Q.symm ∘ productMap)
      (_root_.Dehn.annulusSquare 8 0 ×ˢ Icc (0 : ℝ) 1) := by
    have hproductMapCopy := hproductMap
    obtain ⟨J,hJ,hJs,_⟩ := hproductMapCopy
    rw [←hJs]
    exact polyhedralPLInCharts_of_compatible_inverse e Q (fun x _ => hcover x) hQ J hJ
      (hJs.symm ▸ hproductMap) (hJs.symm ▸ hproductTarget)
  have hphysicalValue
      (z : (_root_.Dehn.annulusSquare 8 0 ×ˢ Icc (0 : ℝ) 1 : Set P3)) :
      (Q.symm ∘ productMap) z = (physicalProduct ((Homeomorph.Set.prod _ _) z) : X) := by
    exact congrArg Q.symm (hproductValue z).symm
  have hphysicalProduct (b : Bool) (z) :
      (physicalProduct z : X) ∈ Q.symm '' caps b ↔ z.2 = if b then 1 else 0 := by
    rw [← hproduct b z]
    change Q.symm (product z) ∈ Q.symm '' caps b ↔ (product z : V3) ∈ caps b
    constructor
    · rintro ⟨x, hx, hxeq⟩
      exact (Q.symm.injOn ((hcapsU b).2.1 hx) (hRegionQ (product z).property) hxeq) ▸ hx
    · intro hz
      exact ⟨product z, hz, rfl⟩
  have hPhysicalCompact : IsCompact (Q.symm '' region) :=
    hRegion.isCompact.image_of_continuousOn (Q.continuousOn_symm.mono hRegionQ)
  have hPhysicalQ : Q.symm '' region ⊆ Q.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact Q.map_target (hRegionQ hx)
  have hPhysicalFrontier : frontier (Q.symm '' region) =
      Q.symm '' band ∪ (Q.symm '' caps true ∪ Q.symm '' caps false) := by
    have hh := Q.symm.image_frontier_eq_target_inter_of_closure_subset
      (D := region) (by rwa [hRegion.isCompact.isClosed.closure_eq])
    change Q.symm '' frontier region = Q.source ∩ frontier (Q.symm '' region) at hh
    rw [inter_eq_right.mpr (hPhysicalCompact.isClosed.frontier_subset.trans hPhysicalQ)] at hh
    rw [← hh, hFrontier, image_union, image_union]
  let coord : P3 ≃L[ℝ] V3 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  have hPhysicalBall := chartwisePLBall_of_finitePLBallPair_in_chart
    e Q (fun x _ => hcover x) hQ coord hRegion hRegionQ
  have hbandImage : (sS i).map ''
      (φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) (l + 3))) =
      Q.symm '' band := by
    rw [image_image, show band = _ from rfl, image_image]
    apply image_congr
    intro z hz
    exact hφval z ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hmapSphere : (sS i).map '' sphere (0 : V3) 1 = S i := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [(sS i).map_eq ⟨x, hx⟩]
      exact ((sS i).parametrization ⟨x, hx⟩).property
    · intro x hx
      obtain ⟨z, hz⟩ := (sS i).parametrization.surjective ⟨x, hx⟩
      exact ⟨z, z.property, ((sS i).map_eq z).trans (congrArg Subtype.val hz)⟩
  have hphysicalWhole :
      ((sS i).map '' k true ∪ (sS i).map '' k false) ∪ Q.symm '' band = S i := by
    calc
      _ = (sS i).map '' ((k true ∪ k false) ∪
          φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) (l + 3))) := by
        rw [image_union, image_union, hbandImage]
      _ = (sS i).map '' sphere (0 : V3) 1 := congrArg (image (sS i).map) hwhole
      _ = S i := hmapSphere
  have hRegionSelected : (Q.symm '' region) ∩ S i = Q.symm '' band := by
    apply Subset.antisymm
    · intro x hx
      exact hRegionFamily.subset ⟨hx.1,(subset_iUnion S i) hx.2⟩
    · intro x hx
      exact ⟨(hRegionFamily.symm.subset hx).1,hphysicalWhole.subset (Or.inr hx)⟩
  have hphysicalBandFace : (Q.symm '' band) ∩ (g '' convexHull ℝ (s : Set E)) =
      Q.symm '' L.boundary ℝ := by
    simpa only [band, image_image, Function.comp_def] using hBandFace
  have hfaceClosed : IsClosed (g '' convexHull ℝ (s : Set E)) :=
    ((s.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (hgc.mono (K.convexHull_subset_space hs))).isClosed
  have hRetainedBand (b : Bool) :
      ((sS i).map '' k b) ∩ (Q.symm '' band) = (sS i).map '' q b := by
    rw [← hbandImage, ← image_inter_on (s := k b)
      (t := φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc (0 : ℝ) (l + 3)))
      (fun x hx y hy hxy => hsi
        (by
          obtain ⟨z, hz, rfl⟩ := hx
          exact hφS ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩)
        ((hk b).2.1 hy) hxy), (hk b).2.2.2.2.1]
  have hcapFamily (b : Bool) :
      (Q.symm '' caps b) ∩ (⋃ j, S j) = (sS i).map '' q b :=
    (hcapsU b).2.2.2.1.trans (hrims b).symm
  have hcapRetained (b : Bool) :
      (Q.symm '' caps b) ∩ ((sS i).map '' k b) = (sS i).map '' q b := by
    apply Subset.antisymm
    · rintro x ⟨hxc, y, hy, rfl⟩
      have hyS : (sS i).map y ∈ S i :=
        hmapSphere.subset ⟨y, (hk b).2.1 hy, rfl⟩
      exact (hcapFamily b).subset ⟨hxc, (subset_iUnion S i) hyS⟩
    · intro x hx
      exact ⟨((hcapFamily b).symm.subset hx).1, image_mono (hk b).1.1 hx⟩
  refine ⟨C, n, L, i, O, new, hLi, hL, hLC, hLinter, hO, hOQ, hrO, hOZ,
    hOfaces, hOmembers, ⟨t⟩, htDis, htOther, ?_, hExterior, ?_, hnewFace,
    ⟨C₀, hC₀, hC₀O, hSupport, hC₀Graph⟩, ?_⟩
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

  · refine ⟨k, q, (fun b => Q.symm '' caps b), Q.symm '' band,
      Q.symm '' region, ?_, hkdis, hphysicalWhole, ?_,
      hRegionU.trans hUO, hPhysicalFrontier, hRegionFamily, hInteriorFamily, ?_⟩
    · intro b
      exact ⟨(hk b).1, (hk b).2.1, rfl, hRetainedBand b, (hk b).2.2.2.2.2.2⟩
    · simpa only [image_union] using hPhysicalBall
    · refine ⟨caps, c, (fun b => ⟨hcaps b, (hcapsU b).2.1, rfl,
        hrims b, hcapFamily b, hcapRetained b⟩), hphysicalDis,
        physicalProduct, hphysicalProduct, Q.symm ∘ productMap, hphysicalPL,
        hphysicalValue, ?_, hcapFace, hphysicalBandFace, ?_⟩
      · intro t ht0 ht1
        exact original_two_port_level_disk (fun b => Q.symm '' caps b)
          (_root_.Dehn.isFinitePLBallPair_annulusSquare (by norm_num))
          physicalProduct (Q.symm ∘ productMap) hphysicalPL hphysicalValue
          hphysicalProduct hPhysicalFrontier hRegionFamily ht0 ht1
      · exact exists_original_two_port_face_product (fun b => Q.symm '' caps b)
          (_root_.Dehn.isFinitePLBallPair_annulusSquare (by norm_num))
          physicalProduct (Q.symm ∘ productMap) hphysicalPL hphysicalValue
          hphysicalProduct hPhysicalFrontier hRegionSelected hfaceClosed hcapFace hphysicalBandFace

end PoincareConjecture.M76

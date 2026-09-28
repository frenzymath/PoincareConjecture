import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PositionedCircleSurgeryPorts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PrescribedCircleGraphSelection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeFamilyPrescribedExchange
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3RelativeFamilyCenteredExchange









set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem exists_original_relative_noL3_circle_step
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [MetricSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R Q₀ Z : Set X} {f : X → E}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hKR : g '' K.space ⊆ R) (hR : IsCompact R) (hRPL : PLDomain e R)
    (hSR : ∀ i, S i ⊆ interior R) (hfrontZ : frontier R ⊆ Z)
    (hZ : IsClosed Z) (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ N.space)
    (hf : ∀ a, LocallyPiecewiseAffineOn (f ∘ (e a).symm) (e a).target)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (O₀ : κ → Set X) (W₀ : ∀ i, (S i × unitInterval) ≃ₜ closure (O₀ i))
    (hQ₀eq : Q₀ = R \ ⋃ i, O₀ i) (hQ₀ : IsCompact Q₀) (hQ₀PL : PLDomain e Q₀)
    (hO₀ : ∀ i, IsOpen (O₀ i)) (hCR₀ : ∀ i, closure (O₀ i) ⊆ interior R)
    (hdis₀ : Pairwise fun i j => Disjoint (closure (O₀ i)) (closure (O₀ j)))
    (hopen₀ : ∀ i z, (W₀ i z : X) ∈ O₀ i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter₀ : ∀ i z, (W₀ i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2)
    (hSC₀ : ∀ i, S i ⊆ closure (O₀ i))
    (B₀ : κ × Bool → Set X) (sB₀ : ∀ i, ChartwisePLSphere e (B₀ i))
    (hB₀dis : Pairwise fun i j => Disjoint (B₀ i) (B₀ j))
    (hB₀sub : ∀ i, B₀ i ⊆ closure (O₀ i.1))
    (hfront₀ : frontier Q₀ = frontier R ∪ ⋃ i, B₀ i)
    (hno : HasNoPuncturedSphereComponents e f Q₀)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite)
    (hGT : G.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target)
    (hphysical : Q.symm '' G.space = (⋃ i, S i) ∩ (g '' convexHull ℝ (s : Set E)))
    (hSZ : Disjoint (⋃ i, S i) Z) (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
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
      ∀ V : Set V3, IsOpen V → w ∈ V →
        ∃ B : OpenPartialHomeomorph V3 P3,
          w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
          LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
          (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S i ↔ (B x).2 = 0) ∧
          ∀ x ∈ B.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0)
    (hcofaces : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (hcircle : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
        intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅) :
    ∃ (S' : κ → Set X) (H : SimplicialComplex ℝ V3)
      (sS' : ∀ i, ChartwisePLSphere e (S' i)),
      (Pairwise fun i j => Disjoint (S' i) (S' j)) ∧
      Disjoint (⋃ i, S' i) Z ∧ (∀ i, S' i ⊆ interior R) ∧
      (∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S' i) K g a) ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        (⋃ i, S' i) ∩ (g '' convexHull ℝ (a : Set E)) ⊆
          (⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))) ∧
      H ≤ G ∧ H.faces.Finite ∧ H.faces.ncard < G.faces.ncard ∧
      H.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target ∧
      (∀ a ∈ H.faces, a.card ≤ 2) ∧
      Q.symm '' H.space = (⋃ i, S' i) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (∀ v : H.vertices, (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      (∀ v : H.vertices, (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) ∧
      (H.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      (∀ w ∈ H.space ∩ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))),
        ∀ V : Set V3, IsOpen V → w ∈ V →
          ∃ B : OpenPartialHomeomorph V3 P3,
            w ∈ B.source ∧ B.source ⊆ V ∧ B w = 0 ∧
            LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
            (∀ x ∈ B.source, Q.symm x ∈ ⋃ i, S' i ↔ (B x).2 = 0) ∧
            ∀ x ∈ B.source, x ∈ convexHull ℝ (A '' (s : Set E)) ↔ (B x).1.1 = 0) ∧
      (∀ a ∈ K.faces, a.card = 3 → a ≠ s →
        ∀ (Q' : OpenPartialHomeomorph X V3) (A' : E →ᴬ[ℝ] V3),
          (InNonreturningTriangleGraphPosition Q' (⋃ j, S j) g a A' →
            InNonreturningTriangleGraphPosition Q' (⋃ j, S' j) g a A') ∧
          (InCircleFreeNonreturningTriangleGraphPosition Q' (⋃ j, S j) g a A' →
            InCircleFreeNonreturningTriangleGraphPosition Q' (⋃ j, S' j) g a A')) ∧
      ∃ (O' : κ → Set X) (W' : ∀ i, (S' i × unitInterval) ≃ₜ closure (O' i))
        (B' : κ × Bool → Set X) (_sB' : ∀ i, ChartwisePLSphere e (B' i)),
        (∀ i, IsOpen (O' i) ∧ closure (O' i) ⊆ interior R) ∧
        (Pairwise fun i j => Disjoint (closure (O' i)) (closure (O' j))) ∧
        (∀ i z, (W' i z : X) ∈ O' i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) ∧
        (∀ i z, (W' i z : X) ∈ S' i ↔ (z.2 : ℝ) = 1/2) ∧
        (∀ i, S' i ⊆ closure (O' i)) ∧
        IsCompact (R \ ⋃ i, O' i) ∧ PLDomain e (R \ ⋃ i, O' i) ∧
        HasNoPuncturedSphereComponents e f (R \ ⋃ i, O' i) ∧
        (Pairwise fun i j => Disjoint (B' i) (B' j)) ∧
        (∀ i, B' i ⊆ closure (O' i.1)) ∧
        frontier (R \ ⋃ i, O' i) = frontier R ∪ ⋃ i, B' i := by
  classical
  let Zp := Z ∪ (interior R)ᶜ
  have hZp : IsClosed Zp := hZ.union isOpen_interior.isClosed_compl
  have hmarkp : ∀ x ∈ K.space, g x ∈ Zp ↔ x ∈ N.space := by
    intro x hx
    constructor
    · rintro (hZx | hRx)
      · exact (hmark x hx).mp hZx
      · exact (hmark x hx).mp (hfrontZ ⟨subset_closure (hKR ⟨x,hx,rfl⟩),hRx⟩)
    · exact fun hn => Or.inl ((hmark x hx).mpr hn)
  have hSZp : Disjoint (⋃ i, S i) Zp := by
    apply disjoint_union_right.mpr
    refine ⟨hSZ,disjoint_left.mpr ?_⟩
    intro x hx hout
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact hout (hSR i hi)
  obtain ⟨C,n,L,i,V,oldNew,hLi,hL,hLC,hLint,hV,hVQ,hrV,hVZ,hVfaces,hVothers,
      _,_,_,_,_,_,_,_,oldk,oldq,oldcaps,band,region,hOldk,hOlddis,hOldcover,
      ⟨ball⟩,hregionV,hregionFront,hregionFamily,_,Dc,rc,_,_,Wport,hportcaps,
      p,hp,hpval,hlevels,hcapsF,hbandF,ρ,hρ,hρi,hρregion,hρS,hρcaps,hρband,_⟩ :=
    exists_protected_positioned_circle_surgery_ports S sS hdis K N hK hNK g
      hg.continuousOn hgi hZp hmarkp hs hs3 Q A hmap hA G hG hGT hphysical hSZp
      hdim hfinite hinterior hexterior he hcover hQ hcrossings hcircle
  have hregionR : region ⊆ interior R := by
    intro x hx
    by_contra hout
    exact disjoint_left.mp hVZ (hregionV hx) (Or.inr hout)
  have hregionConn : IsConnected region := by
    rw [←ball.image_closedBall]
    exact (isConnected_closedBall (x := (0 : V3)) zero_le_one).image ball.map ball.piecewiseAffine.continuousOn
  have hmeet : (S i ∩ region).Nonempty := by
    let z : V2 := fun _ => 1
    have hz : z ∈ sphere (0 : V2) 1 := by simp [z]
    have hzD := sphere_subset_closedBall hz
    have ht : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    exact ⟨ρ (z,0),(hρS _ ⟨hzD,ht⟩).mpr hz,hρregion ⟨hzD,ht⟩⟩
  obtain ⟨Qcut,B,sB,O,W,a,hQeq,hQc,hQPL,hnoQ,hO,hOdis,hW,hWcenter,hSC,hfront,
      hBdis,hBsub,hCc,hCconn,hCPL,hSiC,hOiC,hregionC,Kopp,Bopp,P,k,q,b,caps,U,WU,σ,
      hKopp,hKoppPL,hKoppO,hPmap,hPinside,hPproper,hPopen,hk,hkd,hkcover,hcaps,
      hσ,hσval,hU,hUPL,hUsub,hUC,hcapU,hcapmark,hnoU,hnoGlobal⟩ :=
    hno.exists_relative_family_prescribed_product_noL3_exchange O₀ S W₀ hQ₀eq hQ₀ hQ₀PL
      hO₀ hCR₀ hdis₀ hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ sS hdis
      hR hRPL hSR K g hf hg hgi hreal i ball.isCompact hregionConn hregionR
      (fun j hj => (hVothers j hj).mono_left hregionV) hmeet ρ hρ hρi hρregion hρS
  let new := fun b => (sS i).map '' k b ∪ P.capDisk b
  have hcontact (a : Bool) : ((sS i).map '' k a) ∩ P.closedStrip = P.capRimSet a :=
    (hk a).2.2.2.2.trans (hk a).2.2.2.1
  have hpV : MapsTo P.map (closedBall (0 : V2) 1 ×ˢ Icc (-1 : ℝ) 1) V := by
    rw [hPmap]
    exact fun z hz => hregionV (hρregion hz)
  have hcapFace (a : Bool) : Disjoint (P.capDisk a) (g '' convexHull ℝ (s : Set E)) := by
    simpa only [OriginalDiskProduct.capDisk,hPmap] using hρcaps a
  have hbandFace : (P.map '' (sphere (0 : V2) 1 ×ˢ Icc (-(1/2 : ℝ)) (1/2))) ∩
      (g '' convexHull ℝ (s : Set E)) =
      Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) := by
    simpa only [hPmap,hLC] using hρband
  obtain ⟨H,hHG,_,hSdis',hSZ',hcofaces',houtside,hother,hface,hH,hHT,hdim',hphys',
      hint',hext',hfinite',hlt,hcross',hotherpos⟩ :=
    P.exists_selected_positioned_circle_graph S sS i hdis K g hs3 Q A G C hG hGT hphysical
      hdim hfinite hinterior hexterior hSZ (hVZ.mono_right subset_union_left) hVfaces hVothers
      hpV hPproper (fun a => (sS i).map '' k a) hkd hcontact hkcover caps hcapFace hbandFace
      hcofaces hcrossings b
  obtain ⟨Oc,Hc,sS',W',B',sB',_,_,_,_,hO',hOdis',hW',hWcenter',hSC',_,_,
      hCut',hCutPL',hno',hBdis',hBsub',hfront'⟩ :=
    hnoGlobal.exists_fixed_relative_family_centered_exchange O S W hR hRPL
      (hQeq ▸ hQPL) (fun k => (hO k).1) (fun k => (hO k).2.2.2) hOdis hW hWcenter hSC
      sS B sB hBdis hBsub (hQeq ▸ hfront) i a hCc hCPL (caps b) WU σ hσ hσval b
      (hcapU.trans hU.isClosed.frontier_subset) hUC hcapmark hnoU K g hf hg hgi hreal
  let S' := Function.update S i (new b)
  have hinside' (k : κ) : S' k ⊆ interior R := by
    intro x hx
    exact (hO' k).2 (hSC' k hx)
  exact ⟨S',H,sS',hSdis',hSZ',hinside',hcofaces',hother,
    hHG.trans (G.deleteEdgeComponent_le C),hH,hlt,hHT,hdim',hphys',hint',hext',hfinite',hcross',hotherpos,
    Function.update O i Oc,W',B',sB',hO',hOdis',hW',hWcenter',hSC',hCut',hCutPL',hno',
    hBdis',hBsub',hfront'⟩

end PoincareConjecture.M76

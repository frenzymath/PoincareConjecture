import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalRelativeNoL3CircleStep

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem exists_original_relative_noL3_circle_free_face
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
    (hcofaces : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a) :
    ∃ (S' : κ → Set X) (H : SimplicialComplex ℝ V3)
      (_sS' : ∀ i, ChartwisePLSphere e (S' i)),
      (Pairwise fun i j => Disjoint (S' i) (S' j)) ∧
      Disjoint (⋃ i, S' i) Z ∧ (∀ i, S' i ⊆ interior R) ∧
      (∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S' i) K g a) ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        (⋃ i, S' i) ∩ (g '' convexHull ℝ (a : Set E)) ⊆
          (⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))) ∧
      H ≤ G ∧ H.faces.Finite ∧
      H.space ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target ∧
      (∀ a ∈ H.faces, a.card ≤ 2) ∧
      Q.symm '' H.space = (⋃ i, S' i) ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (∀ v : H.vertices, (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      (∀ v : H.vertices, (v : V3) ∉ intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E))) →
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) ∧
      (H.space ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Finite ∧
      (∀ C : H.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        (C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
          intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))).Nonempty) ∧
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
  induction hn : G.faces.ncard using Nat.strong_induction_on generalizing S G Q₀ O₀ B₀ with
  | h m ih =>
    by_cases hcircle : ∃ C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ∩
          intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) = ∅
    · obtain ⟨S1,H,sS1,hdis1,hSZ1,hSR1,hcofaces1,hother1,hHG,hH,hlt,hHT,hdim1,hphys1,
        hint1,hext1,hfinite1,hcross1,hotherpos1,O1,W1,B1,sB1,hO1,hOdis1,hW1,hWcenter1,hSC1,
        hCut1,hCutPL1,hno1,hBdis1,hBsub1,hfront1⟩ :=
        exists_original_relative_noL3_circle_step S sS hdis K N hK hNK g hg hgi
          hKR hR hRPL hSR hfrontZ hZ hmark hf hreal O₀ W₀ hQ₀eq hQ₀ hQ₀PL hO₀ hCR₀
          hdis₀ hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ hno hs hs3 Q A hmap hA
          G hG hGT hphysical hSZ hdim hfinite hinterior hexterior he hcover hQ
          hcrossings hcofaces hcircle
      obtain ⟨S2,H2,sS2,hdis2,hSZ2,hSR2,hcofaces2,hother2,hH2H,hH2,hH2T,hdim2,hphys2,
        hint2,hext2,hfinite2,hfree2,hcross2,hotherpos2,hcut2⟩ :=
        ih H.faces.ncard (by omega)
          (S := S1) (sS := sS1) (hdis := hdis1) (hSR := hSR1)
          (Q₀ := R \ ⋃ i, O1 i) (O₀ := O1) (W₀ := W1)
          (hQ₀eq := rfl) (hQ₀ := hCut1) (hQ₀PL := hCutPL1)
          (hO₀ := fun i => (hO1 i).1) (hCR₀ := fun i => (hO1 i).2)
          (hdis₀ := hOdis1) (hopen₀ := hW1) (hcenter₀ := hWcenter1) (hSC₀ := hSC1)
          (B₀ := B1) (sB₀ := sB1) (hB₀dis := hBdis1) (hB₀sub := hBsub1)
          (hfront₀ := hfront1) (hno := hno1)
          (G := H) (hG := hH) (hGT := hHT) (hphysical := hphys1) (hSZ := hSZ1)
          (hdim := hdim1) (hfinite := hfinite1) (hinterior := hint1) (hexterior := hext1)
          (hcrossings := hcross1) (hcofaces := hcofaces1) rfl
      refine ⟨S2,H2,sS2,hdis2,hSZ2,hSR2,hcofaces2,
        fun a ha hac hane => (hother2 a ha hac hane).trans (hother1 a ha hac hane),
        hH2H.trans hHG,hH2,hH2T,hdim2,hphys2,hint2,hext2,hfinite2,hfree2,hcross2,?_,hcut2⟩
      intro a ha ha3 hane Q' A'
      exact ⟨(hotherpos2 a ha ha3 hane Q' A').1 ∘ (hotherpos1 a ha ha3 hane Q' A').1,
        (hotherpos2 a ha ha3 hane Q' A').2 ∘ (hotherpos1 a ha ha3 hane Q' A').2⟩
    · refine ⟨S,G,sS,hdis,hSZ,hSR,hcofaces,(fun _ _ _ _ => Subset.rfl),le_rfl,
        hG,hGT,hdim,hphysical,hinterior,hexterior,hfinite,?_,hcrossings,
        (fun _ _ _ _ _ _ => ⟨id,id⟩),
        O₀,W₀,B₀,sB₀,(fun i => ⟨hO₀ i,hCR₀ i⟩),hdis₀,hopen₀,hcenter₀,hSC₀,
        hQ₀eq ▸ hQ₀,hQ₀eq ▸ hQ₀PL,hQ₀eq ▸ hno,hB₀dis,hB₀sub,hQ₀eq ▸ hfront₀⟩
      intro C
      exact Set.nonempty_iff_ne_empty.mpr (fun hh => hcircle ⟨C,hh⟩)

end PoincareConjecture.M76

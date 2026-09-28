import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.OriginalRelativeNoL3CircleFree
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_relative_noL3_circle_free_on_triangles
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
    (hSZ : Disjoint (⋃ i, S i) Z) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s i, (e i).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (hpositions : ∀ s, InNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    (t : Finset (K.FaceOfCard 3)) :
    ∃ (S' : κ → Set X) (_sS' : ∀ i, ChartwisePLSphere e (S' i)),
      (Pairwise fun i j => Disjoint (S' i) (S' j)) ∧
      Disjoint (⋃ i, S' i) Z ∧ (∀ i, S' i ⊆ interior R) ∧
      Disjoint (⋃ i, S' i) (g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card = 2 →
        ((⋃ i, S' i) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
      (∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S' i) K g a) ∧
      (∀ a ∈ K.faces, a.card ≤ 2 →
        (⋃ i, S' i) ∩ (g '' convexHull ℝ (a : Set E)) ⊆
          (⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))) ∧
      (∀ s, InNonreturningTriangleGraphPosition (Q s) (⋃ i, S' i) g s.1 (A s)) ∧
      (∀ s ∈ t, InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S' i) g s.1 (A s)) ∧
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
  induction t using Finset.induction_on generalizing S Q₀ O₀ B₀ with
  | empty =>
    exact ⟨S,sS,hdis,hSZ,hSR,hSV,hedges,hcofaces,(fun _ _ _ => Subset.rfl),
      hpositions,(by simp),O₀,W₀,B₀,sB₀,(fun i => ⟨hO₀ i,hCR₀ i⟩),
      hdis₀,hopen₀,hcenter₀,hSC₀,hQ₀eq ▸ hQ₀,hQ₀eq ▸ hQ₀PL,hQ₀eq ▸ hno,
      hB₀dis,hB₀sub,hQ₀eq ▸ hfront₀⟩
  | @insert s t hst ih =>
    obtain ⟨S0,sS0,hdis0,hSZ0,hSR0,hSV0,hedges0,hcofaces0,hcontacts0,hpositions0,hprocessed0,
      O0,W0,B0,sB0,hO0,hOdis0,hW0,hWcenter0,hSC0,hCut0,hCutPL0,hno0,hBdis0,hBsub0,hfront0⟩ :=
      ih (S := S) (sS := sS) (hdis := hdis) (hSR := hSR)
        (O₀ := O₀) (W₀ := W₀) (hQ₀eq := hQ₀eq) (hQ₀ := hQ₀) (hQ₀PL := hQ₀PL)
        (hO₀ := hO₀) (hCR₀ := hCR₀) (hdis₀ := hdis₀) (hopen₀ := hopen₀)
        (hcenter₀ := hcenter₀) (hSC₀ := hSC₀) (B₀ := B₀) (sB₀ := sB₀)
        (hB₀dis := hB₀dis) (hB₀sub := hB₀sub) (hfront₀ := hfront₀) (hno := hno)
        (hSZ := hSZ) (hSV := hSV) (hedges := hedges) (hcofaces := hcofaces) (hpositions := hpositions)
    obtain ⟨G,hG,hGT,hdim,hphys,hint,hext,hfinite,hcross,hreturn⟩ := hpositions0 s
    obtain ⟨S1,H,sS1,hdis1,hSZ1,hSR1,hcofaces1,hother,hHG,hH,hHT,hdim1,hphys1,
      hint1,hext1,hfinite1,hfree1,hcross1,hotherpos,hcut1⟩ :=
      exists_original_relative_noL3_circle_free_face S0 sS0 hdis0 K N hK hNK g hg hgi
        hKR hR hRPL hSR0 hfrontZ hZ hmark hf hreal O0 W0 rfl hCut0 hCutPL0
        (fun i => (hO0 i).1) (fun i => (hO0 i).2) hOdis0 hW0 hWcenter0 hSC0 B0 sB0
        hBdis0 hBsub0 hfront0 hno0 s.2.1 s.2.2 (Q s) (A s) (hmap s) (hA s)
        G hG hGT hphys hSZ0 hdim hfinite hint hext he hcover (hQ s) hcross hcofaces0
    have hdegree (v : H.vertices) :
        (H.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
          (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨v.val,hHG v.property⟩).ncard := by
      by_cases hv : (v : V3) ∈ intrinsicInterior ℝ (convexHull ℝ (A s '' (s.1 : Set E)))
      · exact (hint1 v hv).trans (hint ⟨v.val,hHG v.property⟩ hv).symm
      · exact (hext1 v hv).trans (hext ⟨v.val,hHG v.property⟩ hv).symm
    have hnew : InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S1 i) g s.1 (A s) :=
      ⟨H,hH,hHT,hdim1,hphys1,hint1,hext1,hfinite1,hcross1,
        G.nonreturning_of_subcomplex H hG hHG hdegree s.1 (A s) hreturn,hfree1⟩
    have hcontacts (a : Finset E) (ha : a ∈ K.faces) (hac : a.card ≤ 2) :
        (⋃ i, S1 i) ∩ (g '' convexHull ℝ (a : Set E)) ⊆
          (⋃ i, S0 i) ∩ (g '' convexHull ℝ (a : Set E)) := by
      apply hother a ha (by omega)
      intro hh
      have := congrArg Finset.card hh
      have := s.2.2
      omega
    have hSV1 : Disjoint (⋃ i, S1 i) (g '' K.vertices) := by
      apply disjoint_left.mpr
      rintro x hx ⟨z,hz,rfl⟩
      have hface : ({z} : Finset E) ∈ K.faces := hz
      have hzcarrier : g z ∈ g '' convexHull ℝ (({z} : Finset E) : Set E) := by
        apply mem_image_of_mem
        simp
      exact disjoint_left.mp hSV0
        (hcontacts {z} hface (by simp) ⟨hx,hzcarrier⟩).1 ⟨z,hz,rfl⟩
    refine ⟨S1,sS1,hdis1,hSZ1,hSR1,hSV1,
      (fun a ha ha2 => (hedges0 a ha ha2).subset (hcontacts a ha ha2.le)),
      hcofaces1,(fun a ha hac => (hcontacts a ha hac).trans (hcontacts0 a ha hac)),
      ?_,?_,hcut1⟩
    · intro q
      by_cases hqs : q = s
      · subst q
        exact hnew.to_nonreturning
      · exact (hotherpos q.1 q.2.1 q.2.2 (fun h => hqs (Subtype.ext h)) (Q q) (A q)).1
          (hpositions0 q)
    · intro q hq
      by_cases hqs : q = s
      · subst q
        exact hnew
      · exact (hotherpos q.1 q.2.1 q.2.2 (fun h => hqs (Subtype.ext h)) (Q q) (A q)).2
          (hprocessed0 q ((Finset.mem_insert.mp hq).resolve_left hqs))

theorem exists_original_relative_noL3_circle_free_triangles
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
    (hSZ : Disjoint (⋃ i, S i) Z) (hSV : Disjoint (⋃ i, S i) (g '' K.vertices))
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))).Finite)
    (hcofaces : ∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S i) K g a)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (hQ : ∀ s i, (e i).symm.trans (Q s) ∈ piecewiseAffineGroupoid V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (hpositions : ∀ s, InNonreturningTriangleGraphPosition (Q s) (⋃ i, S i) g s.1 (A s))
    :
    ∃ (S' : κ → Set X) (_sS' : ∀ i, ChartwisePLSphere e (S' i)),
      (Pairwise fun i j => Disjoint (S' i) (S' j)) ∧
      Disjoint (⋃ i, S' i) Z ∧ (∀ i, S' i ⊆ interior R) ∧
      Disjoint (⋃ i, S' i) (g '' K.vertices) ∧
      (∀ a ∈ K.faces, a.card = 2 →
        ((⋃ i, S' i) ∩ (g '' convexHull ℝ (a : Set E))).Finite) ∧
      (∀ i a, a ∈ K.faces → a.card = 2 → HasOriginalEdgeCofaceCharts e (S' i) K g a) ∧
      (∀ a ∈ K.faces, a.card ≤ 2 →
        (⋃ i, S' i) ∩ (g '' convexHull ℝ (a : Set E)) ⊆
          (⋃ i, S i) ∩ (g '' convexHull ℝ (a : Set E))) ∧
      (∀ s, InNonreturningTriangleGraphPosition (Q s) (⋃ i, S' i) g s.1 (A s)) ∧
      (∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) (⋃ i, S' i) g s.1 (A s)) ∧
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
  let := K.finite_faceOfCard hK 3
  let := Fintype.ofFinite (K.FaceOfCard 3)
  obtain ⟨S',sS',hdis',hSZ',hSR',hSV',hedges',hcofaces',hcontacts',hpositions',hfree',hcut'⟩ :=
    exists_original_relative_noL3_circle_free_on_triangles S sS hdis K N hK hNK g hg hgi
      hKR hR hRPL hSR hfrontZ hZ hmark hf hreal O₀ W₀ hQ₀eq hQ₀ hQ₀PL hO₀ hCR₀
      hdis₀ hopen₀ hcenter₀ hSC₀ B₀ sB₀ hB₀dis hB₀sub hfront₀ hno hSZ hSV hedges
      hcofaces he hcover Q hQ A hmap hA hpositions Finset.univ
  exact ⟨S',sS',hdis',hSZ',hSR',hSV',hedges',hcofaces',hcontacts',hpositions',
    fun s => hfree' s (Finset.mem_univ s),hcut'⟩


end PoincareConjecture.M76

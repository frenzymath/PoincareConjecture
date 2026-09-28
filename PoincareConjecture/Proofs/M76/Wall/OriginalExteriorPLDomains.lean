import PoincareConjecture.Proofs.M76.Wall.OriginalExteriorHeightCorner
import PoincareConjecture.Proofs.M76.Wall.OriginalExteriorLevelChart
import PoincareConjecture.Proofs.M76.Wall.HighExteriorSuperlevelChart
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ExteriorSuperlevelFrontierBounds












set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

open Classical in





theorem PLDomain.original_exterior_superlevel
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L C W : Set X}
    (he : PLDomain e L) (hLC : L ⊆ C)
    (K N D : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hNK : N ≤ K) (hDK : D ≤ K)
    (H : C ≃ₜ K.space) (g : E → C) (hgc : ContinuousOn g K.space)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (F : X → E) (hFc : Continuous F) (hHF : ∀ y : C, (H y : E) = F y)
    (hN : N.space = F '' (C \ interior L)) (hD : D.space = F '' frontier L)
    (A : Set E) {f : E → ℝ} (hf : K.AffineOnFaces f)
    (hzero : ∀ v ∈ K.vertices, v ∉ A → f v = 0)
    (hstars : ∀ p ∈ K.vertices, p ∈ A →
      ∃ G : OpenPartialHomeomorph X V3,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space G.source ∧
        (K.closedStar p).AffineOnFaces (fun z => G (g z)) ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        G.source ⊆ interior C ∩ W ∧
        (G.source ⊆ Lᶜ ∨ ∃ (psi : V3 →ᴬ[ℝ] ℝ) (u : V3),
          psi.contLinear u = 1 ∧
          (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ psi (G y)) ∧
          ∀ y ∈ G.source, y ∈ frontier L ↔ psi (G y) = 0))
    {beta : ℝ} (hbeta : 0 < beta) (hreg : ∀ v ∈ K.vertices, f v ≠ beta) :
    let R := (fun z => (g z : X)) '' (N.space ∩ {z | beta ≤ f z})
    IsCompact R ∧ R ⊆ interior C ∩ W ∧
      PLDomain e R ∧ PLDomain e (L ∪ R) ∧
      frontier R = ((C \ interior L) ∩ {y | f (F y) = beta}) ∪
        (frontier L ∩ {y | beta ≤ f (F y)}) ∧
      frontier (L ∪ R) = (frontier L ∩ {y | f (F y) ≤ beta}) ∪
        ((C \ interior L) ∩ {y | f (F y) = beta}) := by
  classical
  let R := (fun z => (g z : X)) '' (N.space ∩ {z | beta ≤ f z})
  let Bnew := ((C \ interior L) ∩ {y | f (F y) = beta}) ∪
    (frontier L ∩ {y | beta ≤ f (F y)})
  let Bunion := (frontier L ∩ {y | f (F y) ≤ beta}) ∪
    ((C \ interior L) ∩ {y | f (F y) = beta})
  have hsupport : ∀ p ∈ K.vertices, p ∈ A →
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (interior C ∩ W) := by
    intro p hpK hpA
    obtain ⟨G, hsource, _, _, hinside, _⟩ := hstars p hpK hpA
    exact fun z hz => hinside (hsource hz)
  obtain ⟨hcompact, hinside, hR, _⟩ := original_exterior_height_region
    K N hK hNK he.closed hLC H g hgc hg F hHF hN A hf hzero hsupport hbeta
  have hclosed : IsClosed R := hcompact.isClosed
  have hFC : MapsTo F C K.space := by
    intro y hy
    rw [← hHF ⟨y, hy⟩]
    exact (H ⟨y, hy⟩).property
  have hc : ContinuousOn (f ∘ F) C := (hf.continuousOn hK).comp hFc.continuousOn hFC
  have hbounds : frontier R ⊆ Bnew ∧ frontier (L ∪ R) ⊆ Bunion :=
    exterior_superlevel_frontier_subsets he.closed hclosed hLC
      (fun y hy => (hinside hy).1) hc hR
  let Chart (S : Set X) (y : X) : Prop :=
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (B : OpenPartialHomeomorph X V3),
      ell.contLinear v = 1 ∧ y ∈ B.source ∧ ell (B y) = 0 ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      ∀ z ∈ B.source, z ∈ S ↔ 0 ≤ ell (B z)
  have hchart_front (S : Set X) (y : X) (hy : Chart S y) : y ∈ frontier S := by
    obtain ⟨ell, v, B, hv, hyB, hzeroB, _, hhalf⟩ := hy
    have hell : ell.toAffineMap.linear ≠ 0 := by
      intro heq
      have hval : ell.toAffineMap.linear v = 1 := hv
      rw [heq] at hval
      norm_num at hval
    exact ((B.isImage_frontier_of_affine_nonneg ell hell hhalf).apply_mem_iff hyB).mp hzeroB
  have hlevel (y : X) (hy : y ∈ C \ interior L) (hyf : f (F y) = beta) :
      Chart R y ∧ Chart (L ∪ R) y := by
    let z : K.space := H ⟨y, hy.1⟩
    have hzy : (z : E) = F y := hHF ⟨y, hy.1⟩
    have hgz : (g z : X) = y := by
      rw [hg z]
      exact congrArg Subtype.val (H.symm_apply_apply ⟨y, hy.1⟩)
    have hfz : f z = beta := by rw [hzy]; exact hyf
    have hzpos : 0 < f z := by rw [hfz]; exact hbeta
    have hzreg : ∀ v ∈ K.vertices, f v ≠ f z := by
      intro v hv
      rw [hfz]
      exact hreg v hv
    by_cases hyL : y ∈ L
    · have hyfront : y ∈ frontier L := ⟨subset_closure hyL, hy.2⟩
      have hzD : (z : E) ∈ D.space := by
        rw [hD]
        exact ⟨y, hyfront, hzy.symm⟩
      have hcorner := exists_original_exterior_height_corner e K N D hK hNK hDK
        he.closed hLC H g hgc hg F hHF hN hD A hf hzero hstars z hzD hzpos hzreg
      dsimp only at hcorner
      simp only [hfz, hgz] at hcorner
      obtain ⟨a, u, P, U, hau, hanu, hyP, hyU, hPzero, hUzero,
        _, _, hP, hU, hPhalf, hUhalf, _, _⟩ := hcorner
      exact ⟨⟨-a, -u, P, hanu, hyP, hPzero, hP, hPhalf⟩,
        ⟨a, u, U, hau, hyU, hUzero, hU, hUhalf⟩⟩
    · have hplain : ∀ p ∈ K.vertices, p ∈ A →
          ∃ G : OpenPartialHomeomorph X V3,
            MapsTo (fun z => (g z : X)) (K.closedStar p).space G.source ∧
            (K.closedStar p).AffineOnFaces (fun z => G (g z)) ∧
            (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
            G.source ⊆ interior C ∩ W := by
        intro p hpK hpA
        obtain ⟨G, hsource, hcoord, hG, hinsideG, _⟩ := hstars p hpK hpA
        exact ⟨G, hsource, hcoord, hG, hinsideG⟩
      have hzL : (g z : X) ∉ L := by rwa [hgz]
      have hplainchart := exists_original_exterior_level_chart e K N hK hNK he.closed
        hLC H g hgc hg F hHF hN A hf hzero hplain z hzL hzpos hzreg
      dsimp only at hplainchart
      simp only [hfz, hgz] at hplainchart
      obtain ⟨b, w, P, hbw, hyP, hbP, _, hP, hPhalf, hUhalf, _, _⟩ := hplainchart
      exact ⟨⟨b, w, P, hbw, hyP, hbP, hP, hPhalf⟩,
        ⟨b, w, P, hbw, hyP, hbP, hP, hUhalf⟩⟩
  have hhigh (y : X) (hy : y ∈ frontier L) (hyf : beta < f (F y)) : Chart R y := by
    have hyR : y ∈ R := by
      exact hR.symm.subset ⟨⟨hLC (he.closed.frontier_subset hy), hy.2⟩, hyf.le⟩
    obtain ⟨ell, v, P, hv, hyP, hzeroP, hP, hhalf, _, _⟩ :=
      he.exists_high_exterior_chart hc hR hy (hinside hyR).1 hyf
    exact ⟨ell, v, P, hv, hyP, hzeroP, hP, hhalf⟩
  have haway (y : X) (hy : y ∈ frontier L) (hyR : y ∉ R) : Chart (L ∪ R) y := by
    obtain ⟨ell, v, B, hv, hyB, hzeroB, hB, hhalf⟩ := he.halfspace y hy
    refine ⟨ell, v, B.restrOpen Rᶜ hclosed.isOpen_compl, hv, ⟨hyB, hyR⟩,
      hzeroB, ?_, ?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right B (hB i) hclosed.isOpen_compl
    · intro z hz
      change z ∈ L ∪ R ↔ 0 ≤ ell (B z)
      rw [mem_union]
      exact (or_iff_left hz.2).trans (hhalf z hz.1)
  have hnew_chart (y : X) (hy : y ∈ Bnew) : Chart R y := by
    rcases hy with hy | hy
    · exact (hlevel y hy.1 hy.2).1
    · by_cases heq : f (F y) = beta
      · exact (hlevel y ⟨hLC (he.closed.frontier_subset hy.1), hy.1.2⟩ heq).1
      · exact hhigh y hy.1 (lt_of_le_of_ne hy.2 (Ne.symm heq))
  have hunion_chart (y : X) (hy : y ∈ Bunion) : Chart (L ∪ R) y := by
    rcases hy with hy | hy
    · by_cases hyR : y ∈ R
      · have hlarge : beta ≤ f (F y) := (hR.subset hyR).2
        exact (hlevel y ⟨hLC (he.closed.frontier_subset hy.1), hy.1.2⟩
          (le_antisymm hy.2 hlarge)).2
      · exact haway y hy.1 hyR
    · exact (hlevel y hy.1 hy.2).2
  refine ⟨hcompact, hinside,
    ⟨he.cover, he.compatible, hclosed, fun y hy => hnew_chart y (hbounds.1 hy)⟩,
    ⟨he.cover, he.compatible, he.closed.union hclosed,
      fun y hy => hunion_chart y (hbounds.2 hy)⟩, ?_, ?_⟩
  · exact Subset.antisymm hbounds.1 (fun y hy => hchart_front R y (hnew_chart y hy))
  · exact Subset.antisymm hbounds.2 (fun y hy => hchart_front (L ∪ R) y (hunion_chart y hy))

end PoincareConjecture.M76
